/**
 * Raptor-style fountain: LDPC-ish precode + Luby Transform (robust soliton).
 * Any ~K..1.25K distinct output symbols recover K source blocks (high probability).
 * Global — no per-chunk coupon collector.
 */

export const LT_BLOCK = 200
/** TX cycle length ≈ K * this (systematic + repair). Extra is rateless slack. */
/** TX unique symbols ≈ K * this (degree-1 intermediates + LT repair). */
export const LT_TX_MULT = 2.2

function xorshift32(seed){
  let s = (seed >>> 0) || 1
  return () => {
    s ^= s << 13; s >>>= 0
    s ^= s >>> 17; s >>>= 0
    s ^= s << 5; s >>>= 0
    return s >>> 0
  }
}

export function fountainRng01(seed){
  const g = xorshift32(seed)
  return () => g() / 4294967296
}

export function fileIdSeed(fileId, j){
  let h = 2166136261 >>> 0
  const s = String(fileId || "")
  for(let i = 0; i < s.length; i++){
    h ^= s.charCodeAt(i)
    h = Math.imul(h, 16777619) >>> 0
  }
  return (h ^ Math.imul((j + 1) >>> 0, 0x9e3779b1)) >>> 0
}

function xorInto(dst, src){
  for(let i = 0; i < dst.length; i++) dst[i] ^= src[i]
}

/** Precode overhead: ~8% repair intermediates (Raptor-like). */
export function precodeS(K){
  return Math.max(8, Math.ceil(K * 0.08))
}

/**
 * Build L = K+S intermediates: systematic sources + XOR parity checks.
 * Parity j XORs ~4 random sources (deterministic from fileId).
 */
export function buildIntermediates(sourceBlocks, fileId){
  const K = sourceBlocks.length
  const blockLen = sourceBlocks[0].length
  const S = precodeS(K)
  const L = K + S
  const inter = new Array(L)
  for(let i = 0; i < K; i++) inter[i] = sourceBlocks[i]
  for(let j = 0; j < S; j++){
    const rnd = fountainRng01(fileIdSeed(fileId, 0xA0000 + j) ^ 0xC0DEC0DE)
    const mix = new Uint8Array(blockLen)
    const deg = Math.min(K, 3 + ((rnd() * 3) | 0)) // 3..5
    const used = new Set()
    let guard = 0
    while(used.size < deg && guard++ < K * 8){
      used.add((rnd() * K) | 0)
    }
    for(const idx of used) xorInto(mix, sourceBlocks[idx])
    inter[K + j] = mix
  }
  return { inter, K, S, L, blockLen }
}

/** Robust soliton degree for LT over L intermediates. */
export function robustSolitonDegree(L, rnd, c = 0.1, delta = 0.05){
  if(L <= 1) return 1
  const R = Math.max(1, c * Math.log(L / delta) * Math.sqrt(L))
  const rho = new Float64Array(L + 1)
  rho[1] = 1 / L
  for(let d = 2; d <= L; d++) rho[d] = 1 / (d * (d - 1))
  const tau = new Float64Array(L + 1)
  const kBound = Math.min(L, Math.max(1, Math.floor(L / R)))
  for(let d = 1; d < kBound; d++) tau[d] = R / (d * L)
  tau[kBound] = (R * Math.log(R / delta)) / L
  let z = 0
  const mu = new Float64Array(L + 1)
  for(let d = 1; d <= L; d++){
    mu[d] = rho[d] + tau[d]
    z += mu[d]
  }
  let u = rnd()
  let acc = 0
  for(let d = 1; d <= L; d++){
    acc += mu[d] / z
    if(u <= acc) return d
  }
  return Math.min(L, kBound)
}

/** Neighbors of one LT symbol over L intermediates. */
export function ltNeighbors(L, seed){
  const rnd = fountainRng01(seed)
  const d = Math.min(L, Math.max(1, robustSolitonDegree(L, rnd)))
  const set = new Set()
  let guard = 0
  while(set.size < d && guard++ < L * 16){
    set.add((rnd() * L) | 0)
  }
  if(!set.size) set.add(0)
  return [...set]
}

export function ltMix(inter, indices){
  const out = new Uint8Array(inter[0].length)
  for(const i of indices) xorInto(out, inter[i])
  return out
}

/** Peel decoder over L unknowns. Returns array of Uint8Array|null. */
export function ltPeelPartial(L, symbolMap){
  const eqs = []
  for(const sym of symbolMap.values()){
    eqs.push({
      indices: new Set(sym.indices),
      data: sym.data.slice()
    })
  }
  const known = new Array(L).fill(null)
  let changed = true
  while(changed){
    changed = false
    for(let e = eqs.length - 1; e >= 0; e--){
      const eq = eqs[e]
      for(const idx of [...eq.indices]){
        if(known[idx]){
          xorInto(eq.data, known[idx])
          eq.indices.delete(idx)
        }
      }
      if(eq.indices.size === 0){
        eqs.splice(e, 1)
        continue
      }
      if(eq.indices.size === 1){
        const i = [...eq.indices][0]
        if(!known[i]){
          known[i] = eq.data
          changed = true
        }
        eqs.splice(e, 1)
      }
    }
  }
  return known
}

/**
 * After peel stalls, solve remaining unknowns with dense GF(2) GE if few enough.
 * This is what makes “almost done” actually finish.
 */
export function ltSparseGE(L, symbolMap, known, maxUnknown = 320){
  const unknown = []
  const uIndex = new Int32Array(L).fill(-1)
  for(let i = 0; i < L; i++){
    if(!known[i]){
      uIndex[i] = unknown.length
      unknown.push(i)
    }
  }
  const U = unknown.length
  if(U === 0) return known
  if(U > maxUnknown) return known

  const rows = []
  for(const sym of symbolMap.values()){
    const coef = new Uint8Array(U)
    const data = sym.data.slice()
    let deg = 0
    let inconsistent = false
    for(const idx of sym.indices){
      if(idx < 0 || idx >= L) continue
      if(known[idx]){
        xorInto(data, known[idx])
      }else{
        const u = uIndex[idx]
        if(u >= 0){
          coef[u] ^= 1
          if(coef[u]) deg++
          else deg--
        }else{
          inconsistent = true
        }
      }
    }
    if(inconsistent) continue
    // recount deg
    deg = 0
    for(let i = 0; i < U; i++) if(coef[i]) deg++
    if(deg === 0) continue
    rows.push({ coef, data })
  }
  if(rows.length < U) return known

  const pivotForCol = new Int32Array(U).fill(-1)
  let row = 0
  for(let col = 0; col < U; col++){
    let piv = -1
    for(let i = row; i < rows.length; i++){
      if(rows[i].coef[col]){ piv = i; break }
    }
    if(piv < 0) continue
    if(piv !== row){
      const tmp = rows[row]
      rows[row] = rows[piv]
      rows[piv] = tmp
    }
    for(let i = 0; i < rows.length; i++){
      if(i === row || !rows[i].coef[col]) continue
      for(let c = 0; c < U; c++) rows[i].coef[c] ^= rows[row].coef[c]
      xorInto(rows[i].data, rows[row].data)
    }
    pivotForCol[col] = row
    row++
    if(row >= rows.length) break
  }

  const solved = new Array(U).fill(null)
  for(let pass = 0; pass < U; pass++){
    for(let col = 0; col < U; col++){
      if(solved[col]) continue
      const pr = pivotForCol[col]
      if(pr < 0) continue
      const r = rows[pr]
      let ready = true
      const data = r.data.slice()
      for(let c = 0; c < U; c++){
        if(!r.coef[c] || c === col) continue
        if(!solved[c]){ ready = false; break }
        xorInto(data, solved[c])
      }
      // pivot row must include this col
      if(ready && r.coef[col]) solved[col] = data
    }
  }

  const out = known.slice()
  for(let c = 0; c < U; c++){
    if(solved[c]) out[unknown[c]] = solved[c]
  }
  return out
}

/**
 * After LT recovers intermediates, use precode parities to fill missing sources.
 * Parity j was XOR of a deterministic set of sources — same as encoder.
 */
export function precodeFillSources(known, K, S, fileId){
  const L = K + S
  if(known.length < L) return known
  let changed = true
  while(changed){
    changed = false
    for(let j = 0; j < S; j++){
      const pIdx = K + j
      if(!known[pIdx]) continue
      const rnd = fountainRng01(fileIdSeed(fileId, 0xA0000 + j) ^ 0xC0DEC0DE)
      const deg = Math.min(K, 3 + ((rnd() * 3) | 0))
      const used = []
      const set = new Set()
      let guard = 0
      while(set.size < deg && guard++ < K * 8){
        const idx = (rnd() * K) | 0
        if(!set.has(idx)){
          set.add(idx)
          used.push(idx)
        }
      }
      let missing = -1
      let missCount = 0
      const acc = known[pIdx].slice()
      for(const idx of used){
        if(!known[idx]){
          missCount++
          missing = idx
        }else{
          xorInto(acc, known[idx])
        }
      }
      if(missCount === 1 && missing >= 0 && !known[missing]){
        known[missing] = acc
        changed = true
      }
    }
  }
  return known
}

export function countKnown(known, n){
  let c = 0
  for(let i = 0; i < n; i++) if(known[i]) c++
  return c
}

/**
 * Try recover K source blocks from LT symbol map.
 * symbolMap values: { indices: number[], data: Uint8Array }
 */
export function tryFountainRecover(K, S, fileId, symbolMap){
  const L = K + S
  let known = ltPeelPartial(L, symbolMap)
  known = precodeFillSources(known, K, S, fileId)
  // Inject knowns and peel again
  {
    const aug = new Map(symbolMap)
    for(let i = 0; i < L; i++){
      if(known[i]) aug.set(`__k${i}`, { indices: [i], data: known[i] })
    }
    known = ltPeelPartial(L, aug)
    known = precodeFillSources(known, K, S, fileId)
  }
  // Finish remaining with sparse GE (critical for endgame)
  if(!known.slice(0, K).every(Boolean)){
    known = ltSparseGE(L, symbolMap, known, 400)
    known = precodeFillSources(known, K, S, fileId)
    const aug = new Map(symbolMap)
    for(let i = 0; i < L; i++){
      if(known[i]) aug.set(`__k${i}`, { indices: [i], data: known[i] })
    }
    known = ltPeelPartial(L, aug)
  }

  const sources = known.slice(0, K)
  if(!sources.every(Boolean)){
    return { ok: false, sources: null, knownCount: countKnown(known, K), interCount: countKnown(known, L) }
  }
  return { ok: true, sources, knownCount: K, interCount: countKnown(known, L) }
}

/** Split file into fixed-size source blocks (last padded). */
export function splitSourceBlocks(fileBytes, blockLen = LT_BLOCK){
  const K = Math.max(1, Math.ceil(fileBytes.length / blockLen))
  const padded = new Uint8Array(K * blockLen)
  padded.set(fileBytes)
  const blocks = []
  for(let i = 0; i < K; i++) blocks.push(padded.subarray(i * blockLen, (i + 1) * blockLen))
  return { blocks, K, blockLen }
}

/**
 * Build TX payload strings (PC9F).
 * Format: PC9F|fileId|K|S|fileSize|nameB64|typeB64|kind|seed|dataB64
 * kind I = degree-1 intermediate (seed = index 0..L-1); sources are 0..K-1
 * kind L = LT over intermediates (seed → robust-soliton neighbors)
 */
export function buildFountainPayloads(fileBytes, fileMeta, encodeUtf8B64, encodeBytesB64, fixedFileId){
  const fileId = fixedFileId || (
    typeof crypto !== "undefined" && crypto.getRandomValues
      ? (crypto.getRandomValues(new Uint32Array(1))[0] >>> 0).toString(36)
      : Math.floor(Math.random() * 1e9).toString(36)
  )
  const { blocks, K, blockLen } = splitSourceBlocks(fileBytes, LT_BLOCK)
  const { inter, S, L } = buildIntermediates(blocks, fileId)
  const nameB64 = encodeUtf8B64(fileMeta.name || "file")
  const typeB64 = encodeUtf8B64(fileMeta.type || "application/octet-stream")
  const size = fileMeta.size >>> 0

  const out = []
  // Degree-1 for every intermediate (sources + precode) — strong peel base
  for(let i = 0; i < L; i++){
    out.push([
      "PC9F", fileId, String(K), String(S), String(size),
      nameB64, typeB64, "I", String(i), encodeBytesB64(inter[i])
    ].join("|"))
  }
  // Extra LT repair (new information beyond the identity set)
  const nRepair = Math.max(L, Math.ceil(K * (LT_TX_MULT - 1)))
  for(let j = 0; j < nRepair; j++){
    const seed = fileIdSeed(fileId, j)
    const indices = ltNeighbors(L, seed)
    const mix = ltMix(inter, indices)
    out.push([
      "PC9F", fileId, String(K), String(S), String(size),
      nameB64, typeB64, "L", String(seed >>> 0), encodeBytesB64(mix)
    ].join("|"))
  }
  // Shuffle so identity + repair interleave
  for(let i = out.length - 1; i > 0; i--){
    let x = Math.imul(i ^ 0x9e3779b9, 0x85ebca6b) >>> 0
    x = (x ^ (x >>> 16)) >>> 0
    const j = x % (i + 1)
    const t = out[i]; out[i] = out[j]; out[j] = t
  }

  const meta = {
    mode: "lt",
    fileId,
    K,
    S,
    L,
    blockLen,
    total: out.length,
    need: K,
    overhead: LT_TX_MULT
  }
  return { frames: out, meta }
}
