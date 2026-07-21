#!/usr/bin/env node
/** MDS packet RS: any k of n recover. Run: node test/fountain.mjs */
import { rsEncode, rsDecodeErasures } from "../rs.js"

const TARGET_K = 10
const TARGET_N = 20

function planCoding(fileLen){
  let k = TARGET_K
  let n = TARGET_N
  let sym = Math.max(1, Math.ceil(fileLen / k))
  while(sym > 220){
    k++
    n = k * 2
    sym = Math.max(1, Math.ceil(fileLen / k))
  }
  return { k, n, sym }
}

function encodeRsPackets(sources, n){
  const k = sources.length
  const nsym = n - k
  const symLen = sources[0].length
  const packets = Array.from({ length: n }, () => new Uint8Array(symLen))
  for(let b = 0; b < symLen; b++){
    const col = new Uint8Array(k)
    for(let j = 0; j < k; j++) col[j] = sources[j][b]
    const cw = rsEncode(col, nsym)
    for(let i = 0; i < n; i++) packets[i][b] = cw[i]
  }
  return packets
}

function decodeRsPackets(symbolMap, k, n, symLen){
  if(symbolMap.size < k) return null
  const nsym = n - k
  const erase = []
  for(let i = 0; i < n; i++) if(!symbolMap.has(i)) erase.push(i)
  if(erase.length > nsym) return null
  const sources = Array.from({ length: k }, () => new Uint8Array(symLen))
  for(let b = 0; b < symLen; b++){
    const cw = new Uint8Array(n)
    for(let i = 0; i < n; i++){
      const s = symbolMap.get(i)
      cw[i] = s ? s[b] : 0
    }
    const col = rsDecodeErasures(cw, nsym, erase)
    if(!col) return null
    for(let j = 0; j < k; j++) sources[j][b] = col[j]
  }
  return sources
}

function mulberry(seed){
  let a = seed >>> 0
  return () => {
    a |= 0
    a = (a + 0x6d2b79f5) | 0
    let t = Math.imul(a ^ (a >>> 15), 1 | a)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

const fileBytes = new Uint8Array(2048)
for(let i = 0; i < fileBytes.length; i++) fileBytes[i] = (i * 17 + 3) & 255
const { k, n, sym } = planCoding(fileBytes.length)
const padded = new Uint8Array(k * sym)
padded.set(fileBytes)
const sources = []
for(let i = 0; i < k; i++) sources.push(padded.subarray(i * sym, (i + 1) * sym))
const packets = encodeRsPackets(sources, n)

console.log(`2KB plan: k=${k} n=${n} sym=${sym} frames=${n} need=${k}`)

let fails = 0
for(const [label, keepCount, seed] of [
  ["exactly k", k, 1],
  ["exactly k (b)", k, 7],
  ["k+2", k + 2, 3],
  ["all n", n, 1]
]){
  const rnd = mulberry(seed)
  const idx = Array.from({ length: n }, (_, i) => i)
  for(let i = idx.length - 1; i > 0; i--){
    const j = (rnd() * (i + 1)) | 0
    const t = idx[i]; idx[i] = idx[j]; idx[j] = t
  }
  const map = new Map()
  for(let i = 0; i < keepCount; i++) map.set(idx[i], packets[idx[i]])
  const recovered = decodeRsPackets(map, k, n, sym)
  let ok = false
  if(recovered){
    const merged = new Uint8Array(k * sym)
    for(let i = 0; i < k; i++) merged.set(recovered[i], i * sym)
    ok = [...fileBytes].every((b, i) => merged[i] === b)
  }
  console.log(`  ${ok ? "✓" : "✗"} ${label}: kept ${map.size}/${n}`)
  if(!ok) fails++
}

// k-1 must fail
{
  const map = new Map()
  for(let i = 0; i < k - 1; i++) map.set(i, packets[i])
  const recovered = decodeRsPackets(map, k, n, sym)
  const ok = recovered == null
  console.log(`  ${ok ? "✓" : "✗"} k-1 must fail`)
  if(!ok) fails++
}

if(fails){
  console.error("FAILED", fails)
  process.exit(1)
}
console.log("All MDS any-k-of-n cases OK.")
