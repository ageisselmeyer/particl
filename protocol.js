/** Pure encode/decode protocol — shared by the app and automated roundtrip tests. */

export const SYNC = "11001100111100001010101011001100"
export const GRID_W = 32
export const GRID_H = 32
export const DATA_COUNT = GRID_W * GRID_H
export const SYMBOL_SIZE = 16

export function bytesToBits(bytes){
  let s = ""
  for(let i = 0; i < bytes.length; i++) s += bytes[i].toString(2).padStart(8, "0")
  return s
}

export function bitsToBytes(bits){
  const n = (bits.length / 8) | 0
  const out = new Uint8Array(n)
  for(let i = 0; i < n; i++) out[i] = parseInt(bits.slice(i * 8, i * 8 + 8), 2) || 0
  return out
}

export function crc32(bytes){
  let c = 0xffffffff
  for(let i = 0; i < bytes.length; i++){
    c ^= bytes[i]
    for(let k = 0; k < 8; k++) c = (c >>> 1) ^ (0xedb88320 & -(c & 1))
  }
  return (c ^ 0xffffffff) >>> 0
}

/** Front-loaded block-repeat (matched expand/collapse) — best SYNC lock on device. */
export function expandBits(payload, n){
  const L = payload.length
  if(L <= 0) return "0".repeat(n)
  if(L >= n) return payload.slice(0, n)
  const rep = (n / L) | 0
  const extra = n - rep * L
  let out = ""
  for(let i = 0; i < L; i++){
    const copies = rep + (i < extra ? 1 : 0)
    out += payload[i].repeat(copies)
  }
  return out
}

export function collapseVals(vals, targetLen){
  const n = vals.length
  const L = targetLen
  if(L >= n){
    const out = new Float32Array(L)
    out.set(vals.length >= L ? vals.subarray(0, L) : vals)
    return out
  }
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

export function syncScoreAt(bits, start = 0){
  if(!bits || start < 0 || start + SYNC.length > bits.length) return 0
  let ok = 0
  for(let j = 0; j < SYNC.length; j++) if(bits[start + j] === SYNC[j]) ok++
  return ok
}

export function thresholdVals(vals){
  const n = vals.length
  let sum = 0
  for(let i = 0; i < n; i++) sum += vals[i]
  const mean = sum / n
  let varSum = 0
  for(let i = 0; i < n; i++){
    const d = vals[i] - mean
    varSum += d * d
  }
  const std = Math.sqrt(varSum / n)
  const bins = new Int32Array(32)
  let vmin = Infinity, vmax = -Infinity
  for(let i = 0; i < n; i++){
    if(vals[i] < vmin) vmin = vals[i]
    if(vals[i] > vmax) vmax = vals[i]
  }
  const span = Math.max(1e-3, vmax - vmin)
  for(let i = 0; i < n; i++) bins[Math.min(31, ((vals[i] - vmin) / span * 31) | 0)]++
  let w0 = 0, sum0 = 0, bestT = 15, bestVar = -1, sumBins = 0
  for(let b = 0; b < 32; b++) sumBins += b * bins[b]
  for(let t = 0; t < 31; t++){
    w0 += bins[t]
    if(!w0) continue
    sum0 += t * bins[t]
    const w1 = n - w0
    if(!w1) break
    const m0 = sum0 / w0, m1 = (sumBins - sum0) / w1
    const between = w0 * w1 * (m0 - m1) * (m0 - m1)
    if(between > bestVar){ bestVar = between; bestT = t }
  }
  const thr = vmin + ((bestT + 0.5) / 31) * span
  let bits = ""
  for(let i = 0; i < n; i++) bits += vals[i] > thr ? "1" : "0"
  return { bits, thr, mean, std, sync: syncScoreAt(bits, 0) }
}

export function wrapPayload(text){
  const raw = new TextEncoder().encode(text)
  const crc = crc32(raw)
  const body = new Uint8Array(4 + raw.length)
  body[0] = (crc >>> 24) & 255
  body[1] = (crc >>> 16) & 255
  body[2] = (crc >>> 8) & 255
  body[3] = crc & 255
  body.set(raw, 4)
  return SYNC + bytesToBits(body)
}

export function decodeBodyText(bodyBits){
  const maxBytes = Math.min(520, (bodyBits.length / 8) | 0)
  if(maxBytes < 5) return null
  for(let rawLen = 4; rawLen <= maxBytes - 4; rawLen++){
    const body = bitsToBytes(bodyBits.slice(0, (rawLen + 4) * 8))
    const crc =
      ((body[0] << 24) | (body[1] << 16) | (body[2] << 8) | body[3]) >>> 0
    const raw = body.subarray(4, 4 + rawLen)
    if(crc32(raw) !== crc) continue
    try{
      const text = new TextDecoder().decode(raw)
      if(text.startsWith("PC6M|") || text.startsWith("PC6|") ||
         text.startsWith("PC5M|") || text.startsWith("PC5D|")) return text
    }catch(_){}
  }
  return null
}

/** Simulate camera blur by mixing each cell with its 4-neighbors. */
export function blurBitGrid(vals, mix = 0.35){
  const out = new Float32Array(DATA_COUNT)
  for(let gy = 0; gy < GRID_H; gy++){
    for(let gx = 0; gx < GRID_W; gx++){
      const i = gy * GRID_W + gx
      let neigh = 0, n = 0
      if(gx > 0){ neigh += vals[i - 1]; n++ }
      if(gx < GRID_W - 1){ neigh += vals[i + 1]; n++ }
      if(gy > 0){ neigh += vals[i - GRID_W]; n++ }
      if(gy < GRID_H - 1){ neigh += vals[i + GRID_W]; n++ }
      const meanN = n ? neigh / n : vals[i]
      out[i] = vals[i] * (1 - mix) + meanN * mix
    }
  }
  return out
}

export function deblurBitGrid(vals, k = 0.22){
  const out = new Float32Array(DATA_COUNT)
  for(let gy = 0; gy < GRID_H; gy++){
    for(let gx = 0; gx < GRID_W; gx++){
      const i = gy * GRID_W + gx
      let neigh = 0, n = 0
      if(gx > 0){ neigh += vals[i - 1]; n++ }
      if(gx < GRID_W - 1){ neigh += vals[i + 1]; n++ }
      if(gy > 0){ neigh += vals[i - GRID_W]; n++ }
      if(gy < GRID_H - 1){ neigh += vals[i + GRID_W]; n++ }
      const meanN = n ? neigh / n : vals[i]
      out[i] = Math.max(0, vals[i] + (vals[i] - meanN) * k)
    }
  }
  return out
}

/** Recover payload from full-grid ink samples (higher = darker = bit 1). */
export function valsToPayload(vals){
  const maxBody = Math.min(520, ((vals.length - SYNC.length) / 8) | 0)
  const bodies = []
  for(let bb = 5; bb <= maxBody; bb++) bodies.push(bb)
  bodies.sort((a, b) => {
    const da = Math.min(Math.abs(a - 47), Math.abs(a - 82))
    const db = Math.min(Math.abs(b - 47), Math.abs(b - 82))
    return da - db || a - b
  })

  const confOf = (cvals, thr) => {
    const conf = new Float32Array(cvals.length)
    for(let i = 0; i < cvals.length; i++) conf[i] = Math.abs(cvals[i] - thr)
    return conf
  }

  let bestSync = 0
  let bestBits = null
  let bestConf = null

  for(const bb of bodies){
    const L = SYNC.length + bb * 8
    const cvals = collapseVals(vals, L)
    const r = thresholdVals(cvals)
    if(r.sync > bestSync){
      bestSync = r.sync
      bestBits = r.bits
      bestConf = confOf(cvals, r.thr)
    }
    if(r.sync < 26) continue
    const text = decodeBodyText(r.bits.slice(SYNC.length))
    if(text) return { text, sync: r.sync, length: L }
  }

  // Soft chase: flip ambiguous body bits near the threshold.
  if(bestBits && bestConf && bestSync >= 28){
    const amb = []
    for(let i = SYNC.length; i < bestBits.length; i++) amb.push({ i, c: bestConf[i] })
    amb.sort((a, b) => a.c - b.c)
    const top = amb.slice(0, 12).map(x => x.i)
    const flipAt = (src, idx) => {
      const arr = src.split("")
      arr[idx] = arr[idx] === "1" ? "0" : "1"
      return arr.join("")
    }
    for(const idx of top){
      const text = decodeBodyText(flipAt(bestBits, idx).slice(SYNC.length))
      if(text) return { text, sync: bestSync, length: bestBits.length }
    }
    for(let a = 0; a < Math.min(6, top.length); a++){
      for(let b = a + 1; b < Math.min(6, top.length); b++){
        let s = flipAt(bestBits, top[a])
        s = flipAt(s, top[b])
        const text = decodeBodyText(s.slice(SYNC.length))
        if(text) return { text, sync: bestSync, length: bestBits.length }
      }
    }
  }

  return { text: null, sync: bestSync, length: 0 }
}

export function bitsToInkVals(bits, on = 200, off = 20){
  return Float32Array.from(bits, c => (c === "1" ? on : off))
}
