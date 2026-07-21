#!/usr/bin/env node
/**
 * Automated encode→expand→collapse→CRC roundtrip.
 * Run: node test/roundtrip.mjs
 *
 * Hard gate: clean PC6/PC6M must CRC-ok.
 * Noise cases use a seeded RNG so results are deterministic.
 */
import {
  DATA_COUNT, SYNC, SYMBOL_SIZE,
  expandBits, collapseVals, thresholdVals,
  wrapPayload, valsToPayload, bitsToInkVals,
  blurBitGrid, deblurBitGrid
} from "../protocol.js"

function assert(cond, msg){
  if(!cond) throw new Error(msg)
}

function mulberry32(seed){
  let a = seed >>> 0
  return () => {
    a |= 0
    a = (a + 0x6d2b79f5) | 0
    let t = Math.imul(a ^ (a >>> 15), 1 | a)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

function copyBiasExpand(payload, n){
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

function roundtrip(label, text){
  const logical = wrapPayload(text)
  assert(logical.startsWith(SYNC), `${label}: missing SYNC`)
  assert(logical.length <= DATA_COUNT, `${label}: packet ${logical.length} > ${DATA_COUNT}`)
  const frame = expandBits(logical, DATA_COUNT)
  const vals = bitsToInkVals(frame)
  const direct = thresholdVals(collapseVals(vals, logical.length))
  assert(direct.sync === 32, `${label}: direct SYNC ${direct.sync}/32`)
  const recovered = valsToPayload(vals)
  assert(recovered.text === text, `${label}: CRC fail (sync=${recovered.sync})`)
  return { sync: recovered.sync, logicalLen: logical.length }
}

function tryNoisy(meta, noise, frames, seed){
  const rnd = mulberry32(seed)
  const text = makePc6(meta)
  const logical = wrapPayload(text)
  const frame = expandBits(logical, DATA_COUNT)
  const accum = new Float32Array(DATA_COUNT)
  for(let f = 0; f < frames; f++){
    const vals = bitsToInkVals(frame)
    for(let i = 0; i < vals.length; i++){
      vals[i] = Math.max(0, Math.min(255, vals[i] + (rnd() * 2 - 1) * noise))
      accum[i] += vals[i]
    }
  }
  for(let i = 0; i < accum.length; i++) accum[i] /= frames
  const recovered = valsToPayload(accum)
  assert(recovered.text === text, `sync=${recovered.sync}`)
}

const cases = []
const failures = []

function runCase(name, fn){
  try{
    const result = fn() || {}
    cases.push({ name, ok: true, ...result })
    console.log(`  ✓ ${name}`)
  }catch(err){
    cases.push({ name, ok: false, error: err.message })
    failures.push(name)
    console.log(`  ✗ ${name}: ${err.message}`)
  }
}

console.log("PartiCl protocol roundtrip\n")

console.log("1) Clean roundtrips (hard gate):")
runCase("PC6 clean", () => roundtrip("PC6", makePc6(false)))
runCase("PC6M clean", () => roundtrip("PC6M", makePc6(true)))

console.log("\n3) Blur robustness (neighbor bleed):")
for(const mix of [0.25, 0.4]){
  runCase(`PC6 blur=${mix}`, () => {
    const text = makePc6(false)
    const vals = blurBitGrid(bitsToInkVals(expandBits(wrapPayload(text), DATA_COUNT)), mix)
    const recovered = valsToPayload(vals)
    assert(recovered.text === text, `sync=${recovered.sync}`)
    return { mix }
  })
  runCase(`PC6M blur=${mix}`, () => {
    const text = makePc6(true)
    const vals = blurBitGrid(bitsToInkVals(expandBits(wrapPayload(text), DATA_COUNT)), mix)
    const recovered = valsToPayload(vals)
    assert(recovered.text === text, `sync=${recovered.sync}`)
    return { mix }
  })
}
runCase("PC6 blur=0.55", () => {
  const text = makePc6(false)
  const vals = blurBitGrid(bitsToInkVals(expandBits(wrapPayload(text), DATA_COUNT)), 0.55)
  const recovered = valsToPayload(vals)
  assert(recovered.text === text, `sync=${recovered.sync}`)
})

console.log("\n4) Seeded noisy roundtrips:")
const noisy = [
  ["PC6", false, 0, 3, 1],
  ["PC6", false, 25, 3, 2],
  ["PC6M", true, 0, 6, 4],
  ["PC6M", true, 12, 6, 5]
]
for(const [label, meta, noise, frames, seed] of noisy){
  runCase(`${label} noise=${noise}×${frames}`, () => {
    tryNoisy(meta, noise, frames, seed)
    return { noise }
  })
}

console.log("\n5) Old front-loaded stretch still fails under tail noise (expected):")
{
  const logical = wrapPayload(makePc6(false))
  const frame = copyBiasExpand(logical, DATA_COUNT)
  const rnd = mulberry32(99)
  const vals = bitsToInkVals(frame)
  for(let i = (DATA_COUNT * 0.35) | 0; i < DATA_COUNT; i++){
    vals[i] = Math.max(0, Math.min(255, vals[i] + (rnd() > 0.5 ? 70 : -70)))
  }
  const recovered = valsToPayload(vals)
  console.log(`   sync ${recovered.sync}/32 · ${recovered.text ? "CRC ok" : "CRC fail"}`)
}

console.log(`\n${"─".repeat(40)}`)
console.log(`Result: ${cases.filter(c => c.ok).length}/${cases.length} passed`)
if(failures.length){
  console.error("FAILED:", failures.join(", "))
  process.exit(1)
}
console.log("All roundtrips OK — decode path is self-consistent.")
process.exit(0)
