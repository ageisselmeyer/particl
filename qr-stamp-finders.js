/**
 * Stamp standard QR corner finders onto an ImageData before decode.
 * TX may omit finders for a cleaner particle look; RX restores them at a known grid.
 */

export function moduleCountForVersion(version){
  const v = version | 0
  if(v < 1 || v > 40) return 0
  return 21 + 4 * (v - 1)
}

export function versionForModuleCount(n){
  if(((n - 21) % 4) !== 0) return 0
  const v = ((n - 21) / 4 | 0) + 1
  return v >= 1 && v <= 40 ? v : 0
}

/** All legal module counts (v1…v40). */
export function allModuleCounts(){
  const out = []
  for(let v = 1; v <= 40; v++) out.push(moduleCountForVersion(v))
  return out
}

/**
 * Paint nested 7×7 finders at TL / TR / BL.
 * Assumes the image is a full QR including quiet modules on each side.
 * @param {ImageData} img
 * @param {number} n — module count (no quiet)
 * @param {number} [quiet=4]
 * @returns {ImageData}
 */
export function stampFindersOnImageData(img, n, quiet = 4){
  const w = img.width | 0
  const h = img.height | 0
  const out = new Uint8ClampedArray(img.data)
  const total = n + quiet * 2
  if(total < 9 || w < 16 || h < 16) return new ImageData(out, w, h)
  const cellW = w / total
  const cellH = h / total
  const originX = quiet * cellW
  const originY = quiet * cellH

  const paint = (r0, c0) => {
    for(let dr = 0; dr < 7; dr++){
      for(let dc = 0; dc < 7; dc++){
        const edge = dr === 0 || dr === 6 || dc === 0 || dc === 6
        const core = dr >= 2 && dr <= 4 && dc >= 2 && dc <= 4
        const shade = edge || core ? 0 : 255
        const x0 = Math.floor(originX + (c0 + dc) * cellW)
        const y0 = Math.floor(originY + (r0 + dr) * cellH)
        const x1 = Math.max(x0 + 1, Math.floor(originX + (c0 + dc + 1) * cellW))
        const y1 = Math.max(y0 + 1, Math.floor(originY + (r0 + dr + 1) * cellH))
        for(let y = y0; y < y1; y++){
          if(y < 0 || y >= h) continue
          for(let x = x0; x < x1; x++){
            if(x < 0 || x >= w) continue
            const i = (y * w + x) * 4
            out[i] = out[i + 1] = out[i + 2] = shade
            out[i + 3] = 255
          }
        }
      }
    }
  }

  paint(0, 0)
  paint(0, n - 7)
  paint(n - 7, 0)
  return new ImageData(out, w, h)
}

/** Rotate through module-count candidates until a decode locks the version. */
export function pickStampModuleCounts(lockedN, frameNo, perFrame = 3, preferN = 0){
  if(lockedN > 0) return [lockedN]
  const all = allModuleCounts()
  const ranked = all.filter((n) => n >= 41).concat(all.filter((n) => n < 41))
  const out = []
  if(preferN > 0 && versionForModuleCount(preferN)){
    out.push(preferN)
    // neighbors ±4 modules (±1 version)
    if(versionForModuleCount(preferN - 4)) out.push(preferN - 4)
    if(versionForModuleCount(preferN + 4)) out.push(preferN + 4)
  }
  const start = ((frameNo >>> 0) * perFrame) % ranked.length
  for(let i = 0; out.length < perFrame; i++){
    const n = ranked[(start + i) % ranked.length]
    if(!out.includes(n)) out.push(n)
  }
  return out.slice(0, perFrame)
}

/**
 * Estimate module count from timing alternation after the image is rectified.
 * Returns 0 if unreliable.
 */
export function estimateModuleCountFromTiming(img, quiet = 4){
  const w = img.width | 0
  const h = img.height | 0
  if(w < 64 || h < 64) return 0
  const data = img.data
  // Timing row is module row 6 → y ≈ (quiet+6.5)/(n+2*quiet)*h — unknown n.
  // Scan several candidate rows in the upper band and pick the strongest alternation.
  const runs = []
  for(const yFrac of [0.12, 0.14, 0.16, 0.18, 0.22]){
    const y = Math.min(h - 2, Math.max(1, (yFrac * h) | 0))
    let prev = data[(y * w + (w >> 2)) * 4] < 140 ? 0 : 1
    let run = 1
    const lengths = []
    const x0 = (w * 0.2) | 0
    const x1 = (w * 0.8) | 0
    for(let x = x0 + 1; x < x1; x++){
      const bit = data[(y * w + x) * 4] < 140 ? 0 : 1
      if(bit === prev) run++
      else{
        if(run >= 2) lengths.push(run)
        prev = bit
        run = 1
      }
    }
    if(run >= 2) lengths.push(run)
    if(lengths.length >= 8){
      lengths.sort((a, b) => a - b)
      const med = lengths[lengths.length >> 1]
      runs.push(med)
    }
  }
  if(!runs.length) return 0
  runs.sort((a, b) => a - b)
  const cell = runs[runs.length >> 1]
  if(cell < 3 || cell > w / 20) return 0
  const total = Math.round(w / cell)
  const n = total - quiet * 2
  // Snap to legal QR size
  const v = versionForModuleCount(n)
  if(v) return n
  // nearest legal
  let best = 0, bestD = 1e9
  for(const m of allModuleCounts()){
    const d = Math.abs(m - n)
    if(d < bestD){ bestD = d; best = m }
  }
  return bestD <= 4 ? best : 0
}
