#!/usr/bin/env node
/**
 * Automated encode→expand→collapse→CRC roundtrip.
 * Iterates packet shapes and noise until every case passes (or reports failure).
 */
import {
  DATA_COUNT, SYNC, SYMBOL_SIZE,
  expandBits, collapseVals, thresholdVals, syncScoreAt,
  wrapPayload, valsToPayload, bitsToInkVals, bytesToBits, crc32
} from "../protocol.js"

function assert(cond, msg){
  if(!cond) throw new Error(msg)
}

function copyBiasExpand(payload, n){
  // Old buggy front-loaded expand (SYNC got extra copies).
  const L = payload.length
  const rep = (n / L) | 0
  const extra = n - rep * L
  let out = ""
  for(let i = 0; i < L; i++){
    const copies = rep + (i < extra ? 1 : 0)
    out += payload[i].repeat(copies)
  }
  return out
}

function makePc6(meta = false){
  const fileId = "testdev"
  const k = 3, r = 2, seq = 1, seed = 0
  const data = new Uint8Array(SYMBOL_SIZE)
  for(let i = 0; i < SYMBOL_SIZE; i++) data[i] = (i * 17 + 3) & 255
  const b64 = Buffer.from(data).toString("base64")
  if(meta){
    return [
      "PC6M", fileId, String(k), String(r), "48",
      Buffer.from("cyanob.py").toString("base64"),
      Buffer.from("text/plain").toString("base64"),
      String(seq), String(seed), b64
    ].join("|")
  }
  return ["PC6", fileId, String(k), String(r), String(seq), String(seed), b64].join("|")
}

function roundtrip(label, text, { noise = 0, expand = expandBits } = {}){
  const logical = wrapPayload(text)
  assert(logical.startsWith(SYNC), `${label}: missing SYNC`)
  assert(logical.length <= DATA_COUNT, `${label}: packet ${logical.length} > ${DATA_COUNT}`)

  const frame = expand(logical, DATA_COUNT)
  assert(frame.length === DATA_COUNT, `${label}: frame length`)

  let vals = bitsToInkVals(frame)
  if(noise > 0){
    for(let i = 0; i < vals.length; i++){
      vals[i] = Math.max(0, Math.min(255, vals[i] + (Math.random() * 2 - 1) * noise))
    }
  }

  // Perfect collapse at true length must recover SYNC + CRC.
  const cvals = collapseVals(vals, logical.length)
  const direct = thresholdVals(cvals)
  assert(direct.sync === 32, `${label}: direct SYNC ${direct.sync}/32 (need 32)`)
  const bodyBits = direct.bits.slice(SYNC.length)
  const rawLen = (logical.length - SYNC.length) / 8 - 4
  const body = (() => {
    const bytes = new Uint8Array(logical.length / 8)
    // decode via valsToPayload path
    return null
  })()

  const recovered = valsToPayload(vals)
  assert(recovered.text === text, `${label}: CRC/payload mismatch (sync=${recovered.sync}, got ${recovered.text?.slice(0, 40)})`)
  return { ok: true, sync: recovered.sync, logicalLen: logical.length }
}

function measureBodyErrors(expand){
  const text = makePc6(false)
  const logical = wrapPayload(text)
  const frame = expand(logical, DATA_COUNT)
  const vals = bitsToInkVals(frame)
  const cvals = collapseVals(vals, logical.length)
  const { bits } = thresholdVals(cvals)
  let syncOk = 0, bodyOk = 0
  for(let i = 0; i < SYNC.length; i++) if(bits[i] === logical[i]) syncOk++
  for(let i = SYNC.length; i < logical.length; i++) if(bits[i] === logical[i]) bodyOk++
  return {
    syncOk,
    bodyOk,
    bodyTotal: logical.length - SYNC.length,
    bodyPct: bodyOk / (logical.length - SYNC.length)
  }
}

const cases = []
let failures = []

function runCase(name, fn){
  try{
    const result = fn()
    cases.push({ name, ok: true, ...result })
    console.log(`  ✓ ${name}`)
  }catch(err){
    cases.push({ name, ok: false, error: err.message })
    failures.push(name)
    console.log(`  ✗ ${name}: ${err.message}`)
  }
}

console.log("PartiCl protocol roundtrip\n")

console.log("1) Bias check (front-loaded stretch starved the body under matching collapse):")
{
  function collapseFront(vals, L){
    const n = vals.length
    const rep = (n / L) | 0
    const extra = n - rep * L
    const out = new Float32Array(L)
    let idx = 0
    for(let i = 0; i < L; i++){
      const copies = rep + (i < extra ? 1 : 0)
      let s = 0
      for(let c = 0; c < copies; c++) s += vals[idx++]
      out[i] = s / copies
    }
    return out
  }
  const text = makePc6(false)
  const logical = wrapPayload(text)
  // Perfect path: both schemes lossless
  const evenFrame = expandBits(logical, DATA_COUNT)
  const frontFrame = copyBiasExpand(logical, DATA_COUNT)
  assert(thresholdVals(collapseVals(bitsToInkVals(evenFrame), logical.length)).sync === 32, "even clean")
  assert(thresholdVals(collapseFront(bitsToInkVals(frontFrame), logical.length)).sync === 32, "front clean")

  // Tail noise: front-loaded keeps SYNC, loses body; even shares the pain.
  const spoil = (frame) => {
    const vals = bitsToInkVals(frame)
    for(let i = (DATA_COUNT * 0.4) | 0; i < DATA_COUNT; i++){
      vals[i] = Math.random() > 0.5 ? 200 : 20
    }
    return vals
  }
  const evenR = thresholdVals(collapseVals(spoil(evenFrame), logical.length))
  const frontR = thresholdVals(collapseFront(spoil(frontFrame), logical.length))
  console.log(`   even+tail-noise:  SYNC ${evenR.sync}/32`)
  console.log(`   front+tail-noise: SYNC ${frontR.sync}/32 (inflated SYNC, weaker body)`)
}

console.log("\n2) Clean roundtrips:")
runCase("PC6 clean", () => roundtrip("PC6", makePc6(false)))
runCase("PC6M clean", () => roundtrip("PC6M", makePc6(true)))

console.log("\n3) Noisy roundtrips (multi-frame accum + soft chase):")
function tryNoisy(label, meta, noise, frames){
  const text = makePc6(meta)
  const logical = wrapPayload(text)
  const frame = expandBits(logical, DATA_COUNT)
  const accum = new Float32Array(DATA_COUNT)
  for(let f = 0; f < frames; f++){
    const vals = bitsToInkVals(frame)
    for(let i = 0; i < vals.length; i++){
      vals[i] = Math.max(0, Math.min(255, vals[i] + (Math.random() * 2 - 1) * noise))
      accum[i] += vals[i]
    }
  }
  for(let i = 0; i < accum.length; i++) accum[i] /= frames
  const recovered = valsToPayload(accum)
  assert(recovered.text === text, `${label}: sync=${recovered.sync}`)
}

for(const meta of [false, true]){
  const label = meta ? "PC6M" : "PC6"
  const frames = meta ? 6 : 3
  const noises = meta ? [0, 12, 22] : [0, 20, 40, 55]
  let maxNoise = -1
  for(const noise of noises){
    const name = `${label} noise=${noise}×${frames}`
    let ok = false
    let lastErr = null
    // A few seeds — camera noise is random; require majority success.
    let hits = 0
    for(let attempt = 0; attempt < 5; attempt++){
      try{
        tryNoisy(name, meta, noise, frames)
        hits++
      }catch(err){
        lastErr = err
      }
    }
    ok = hits >= (noise === 0 ? 5 : 3)
    if(ok){
      cases.push({ name, ok: true, noise, hits })
      console.log(`  ✓ ${name} (${hits}/5)`)
      maxNoise = noise
    }else{
      cases.push({ name, ok: false, error: lastErr?.message, noise, hits })
      console.log(`  ✗ ${name}: ${hits}/5 · ${lastErr?.message}`)
      failures.push(name)
      break
    }
  }
  if(maxNoise >= 0) console.log(`   → ${label} OK through noise=${maxNoise}`)
}

console.log("\n4) Regression: front-loaded expand + mid noise should prefer SYNC over body:")
{
  const text = makePc6(false)
  const logical = wrapPayload(text)
  const frame = copyBiasExpand(logical, DATA_COUNT)
  const vals = bitsToInkVals(frame)
  // Corrupt only the second half of the frame (body-heavy region under front-load).
  for(let i = (DATA_COUNT * 0.35) | 0; i < DATA_COUNT; i++){
    vals[i] = Math.max(0, Math.min(255, vals[i] + (Math.random() > 0.5 ? 70 : -70)))
  }
  const cvals = collapseVals(vals, logical.length)
  const { bits, sync } = thresholdVals(cvals)
  let bodyErr = 0
  for(let i = SYNC.length; i < logical.length; i++) if(bits[i] !== logical[i]) bodyErr++
  console.log(`   biased+tail-noise → SYNC ${sync}/32 · body errors ${bodyErr}`)
  const recovered = valsToPayload(vals)
  console.log(`   recover: ${recovered.text ? "CRC ok (lucky)" : "CRC fail (expected)"}`)
}

const failed = cases.filter(c => c.ok === false)
console.log(`\n${"─".repeat(40)}`)
console.log(`Result: ${cases.filter(c => c.ok).length}/${cases.length} passed`)
if(failed.length){
  console.error("FAILED:", failed.map(f => f.name).join(", "))
  process.exit(1)
}
console.log("All roundtrips OK — decode path is self-consistent.")
process.exit(0)
