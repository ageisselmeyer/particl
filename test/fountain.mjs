#!/usr/bin/env node
/** Fountain recovery with intentional drops. Run: node test/fountain.mjs */

function fountainRng(seed){
  let s = seed >>> 0
  return () => {
    s = (Math.imul(s, 1664525) + 1013904223) >>> 0
    return s / 4294967296
  }
}
function pickLtDegree(k, rnd){
  if(k <= 1) return 1
  const u = rnd()
  if(u < 0.4) return 1
  if(u < 0.7) return 2
  if(u < 0.9) return Math.min(k, 3)
  return Math.min(k, 2 + ((rnd() * Math.min(k - 1, 6)) | 0))
}
function ltIndices(k, seed){
  const rnd = fountainRng(seed)
  const d = Math.min(k, Math.max(1, pickLtDegree(k, rnd)))
  const set = new Set()
  let guard = 0
  while(set.size < d && guard++ < k * 8) set.add((rnd() * k) | 0)
  if(!set.size) set.add(0)
  return [...set]
}
function xorBytes(into, from){
  const n = Math.min(into.length, from.length)
  for(let i = 0; i < n; i++) into[i] ^= from[i]
}
function ltDecodeGE(k, symbolMap){
  const rows = []
  for(const sym of symbolMap.values()){
    const coef = new Uint8Array(k)
    for(const i of sym.indices) if(i >= 0 && i < k) coef[i] = 1
    let any = false
    for(let i = 0; i < k; i++) if(coef[i]){ any = true; break }
    if(!any) continue
    rows.push({ coef, data: sym.data.slice() })
  }
  if(rows.length < k) return null
  const pivotForCol = new Int32Array(k).fill(-1)
  let row = 0
  for(let col = 0; col < k; col++){
    let piv = -1
    for(let i = row; i < rows.length; i++){
      if(rows[i].coef[col]){ piv = i; break }
    }
    if(piv < 0) continue
    if(piv !== row){
      const tmp = rows[row]; rows[row] = rows[piv]; rows[piv] = tmp
    }
    for(let i = 0; i < rows.length; i++){
      if(i === row || !rows[i].coef[col]) continue
      for(let c = 0; c < k; c++) rows[i].coef[c] ^= rows[row].coef[c]
      xorBytes(rows[i].data, rows[row].data)
    }
    pivotForCol[col] = row
    row++
    if(row >= rows.length) break
  }
  const known = new Array(k).fill(null)
  for(let col = 0; col < k; col++){
    const pr = pivotForCol[col]
    if(pr < 0) return null
    const data = rows[pr].data.slice()
    for(let c = 0; c < k; c++){
      if(c === col) continue
      if(rows[pr].coef[c]){
        if(!known[c]) return null
        xorBytes(data, known[c])
      }
    }
    known[col] = data
  }
  return known
}
function fileIdSeed(fileId, j){
  let h = 2166136261 >>> 0
  for(let i = 0; i < fileId.length; i++){
    h ^= fileId.charCodeAt(i)
    h = Math.imul(h, 16777619) >>> 0
  }
  return (h ^ Math.imul(j + 1, 0x9e3779b1)) >>> 0
}
function hash01(i, salt){
  let x = Math.imul(i ^ (salt * 0x9e3779b9), 0x85ebca6b) >>> 0
  x ^= x >>> 16
  x = Math.imul(x, 0xc2b2ae35) >>> 0
  x ^= x >>> 13
  return (x >>> 0) / 4294967296
}

const SYMBOL_SIZE = 96
const FOUNTAIN_SOURCE_COPIES = 1
const FOUNTAIN_REPAIR_BASE = 1.0

function buildPackets(fileBytes){
  const fileId = "testdev"
  const k = Math.max(1, Math.ceil(fileBytes.length / SYMBOL_SIZE))
  const padded = new Uint8Array(k * SYMBOL_SIZE)
  padded.set(fileBytes)
  const sources = []
  for(let i = 0; i < k; i++) sources.push(padded.subarray(i * SYMBOL_SIZE, (i + 1) * SYMBOL_SIZE))
  const r = Math.max(3, Math.ceil(k * FOUNTAIN_REPAIR_BASE))
  const packets = []
  for(let copy = 0; copy < FOUNTAIN_SOURCE_COPIES; copy++){
    for(let i = 0; i < k; i++) packets.push({ seq: i, seed: 0, data: sources[i].slice(), indices: [i] })
  }
  for(let j = 0; j < r; j++){
    const seed = fileIdSeed(fileId, j)
    const indices = ltIndices(k, seed)
    const data = new Uint8Array(SYMBOL_SIZE)
    for(const idx of indices) xorBytes(data, sources[idx])
    packets.push({ seq: k + j, seed, data, indices })
  }
  for(let i = packets.length - 1; i > 0; i--){
    const j = Math.floor(hash01(i, 91) * (i + 1))
    const t = packets[i]; packets[i] = packets[j]; packets[j] = t
  }
  return { k, r, packets }
}

function recover(packets, k, dropRatio, seed){
  const rnd = fountainRng(seed)
  const map = new Map()
  for(const p of packets){
    if(rnd() < dropRatio) continue
    if(map.has(p.seq)) continue
    map.set(p.seq, { data: p.data.slice(), indices: p.indices })
  }
  const ge = ltDecodeGE(k, map)
  return { ok: !!ge, kept: map.size, data: ge }
}

const fileBytes = new Uint8Array(96 * 8 + 40)
for(let i = 0; i < fileBytes.length; i++) fileBytes[i] = (i * 17 + 3) & 255
const { k, r, packets } = buildPackets(fileBytes)
console.log(`Fountain test: k=${k} r=${r} total=${packets.length} file=${fileBytes.length}B`)

let fails = 0
for(const [label, drop, seed, required] of [
  ["0% drop", 0, 1, true],
  ["20% drop", 0.2, 2, true],
  ["35% drop", 0.35, 3, true],
  ["35% drop b", 0.35, 7, true]
]){
  const res = recover(packets, k, drop, seed)
  let bytesOk = false
  if(res.ok && res.data){
    const merged = new Uint8Array(k * SYMBOL_SIZE)
    for(let i = 0; i < k; i++) merged.set(res.data[i], i * SYMBOL_SIZE)
    bytesOk = [...fileBytes].every((b, i) => merged[i] === b)
  }
  const ok = res.ok && bytesOk
  console.log(`  ${ok ? "✓" : "✗"} ${label}: kept ${res.kept}/${packets.length}`)
  if(required && !ok) fails++
}

if(fails){
  console.error(`FAILED: ${fails} cases`)
  process.exit(1)
}
console.log("All fountain recovery cases OK (misses tolerated).")
