#!/usr/bin/env node
/**
 * Automated encode→expand→collapse→CRC roundtrip.
 * Run: node test/roundtrip.mjs
 */
import {
  DATA_COUNT, SYNC, SYMBOL_SIZE,
  expandBits, collapseVals, thresholdVals,
  wrapPayload, valsToPayload, bitsToInkVals
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
  assert(logical.length <= DATA_COUNT, `${label}: packet too long (${logical.length})`)
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
console.log("1) Clean roundtrips:")
runCase("PC6 clean", () => roundtrip("PC6", makePc6(false)))
runCase("PC6M clean", () => roundtrip("PC6M", makePc6(true)))

console.log("\n2) Seeded noisy roundtrips:")
for(const [label, meta, noise, frames, seed] of [
  ["PC6", false, 0, 3, 1],
  ["PC6M", true, 0, 6, 4]
]){
  runCase(`${label} noise=${noise}×${frames}`, () => {
    tryNoisy(meta, noise, frames, seed)
    return { noise }
  })
}

console.log("\n3) RS corrects flipped cells:")
runCase("PC6 + 8 flipped bits", () => {
  const text = makePc6(false)
  const logical = wrapPayload(text)
  const frame = expandBits(logical, DATA_COUNT)
  const vals = bitsToInkVals(frame)
  for(const i of [40, 100, 200, 350, 500, 650, 800, 950]){
    vals[i] = vals[i] > 100 ? 20 : 200
  }
  const recovered = valsToPayload(vals)
  assert(recovered.text === text, `RS miss sync=${recovered.sync}`)
})

console.log(`\n${"─".repeat(40)}`)
console.log(`Result: ${cases.filter(c => c.ok).length}/${cases.length} passed`)
if(failures.length){
  console.error("FAILED:", failures.join(", "))
  process.exit(1)
}
console.log("All roundtrips OK.")
process.exit(0)
