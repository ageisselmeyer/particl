/**
 * Ball / point-cloud visual filter for XOR-scrambled QR.
 * TX: binary noise field → dark splats on white paper (cell-aligned for RX).
 * RX: cell-average binarize with darkOnLight polarity → XOR unfilter.
 */

export function hash01(i, salt){
  let x = Math.imul((i >>> 0) ^ (salt * 0x9e3779b9), 0x85ebca6b) >>> 0
  x ^= x >>> 16
  x = Math.imul(x, 0xc2b2ae35) >>> 0
  x ^= x >>> 13
  return (x >>> 0) / 4294967296
}

function splatBall(acc, w, h, cx, cy, rad, amp){
  if(amp <= 0 || rad < 0.5) return
  const r2 = rad * rad
  const x0 = Math.max(0, Math.floor(cx - rad - 1))
  const x1 = Math.min(w, Math.ceil(cx + rad + 1))
  const y0 = Math.max(0, Math.floor(cy - rad - 1))
  const y1 = Math.min(h, Math.ceil(cy + rad + 1))
  for(let y = y0; y < y1; y++){
    for(let x = x0; x < x1; x++){
      const dx = x - cx
      const dy = y - cy
      const d2 = dx * dx + dy * dy
      if(d2 >= r2) continue
      const t = 1 - d2 / r2
      acc[y * w + x] += amp * t * t
    }
  }
}

/** Majority bit in one XOR noise cell — matches RX cellAvg sampling. */
function cellMajorityOn(src, w, h, cx, cy, noiseScale){
  const x0 = Math.floor(cx * w / noiseScale)
  const y0 = Math.floor(cy * h / noiseScale)
  const x1 = Math.min(w, Math.floor((cx + 1) * w / noiseScale))
  const y1 = Math.min(h, Math.floor((cy + 1) * h / noiseScale))
  let sum = 0, n = 0
  for(let y = y0; y < y1; y++){
    for(let x = x0; x < x1; x++){
      sum += src[(y * w + x) * 4] >= 128 ? 1 : 0
      n++
    }
  }
  return n > 0 && sum / n >= 0.5
}

/**
 * Render XOR binary as dark splats on white, one cluster per noise cell.
 * Dots are coarse and grid-aligned so camera cellAvg + XOR unfilter can recover.
 */
export function renderBallCloud(binaryImg, w, h, {
  seed = 0x50415254,
  noiseScale = 96,
  dotFill = 0.44,
  inkThreshold = 0.28
} = {}){
  const src = binaryImg.data
  const acc = new Float32Array(w * h)
  const cellW = w / noiseScale
  const cellH = h / noiseScale
  const dotRad = Math.max(2.5, Math.min(cellW, cellH) * dotFill)

  for(let cy = 0; cy < noiseScale; cy++){
    for(let cx = 0; cx < noiseScale; cx++){
      if(!cellMajorityOn(src, w, h, cx, cy, noiseScale)) continue
      const px = (cx + 0.5) * cellW
      const py = (cy + 0.5) * cellH
      const cellId = cy * noiseScale + cx
      const count = 1 + (hash01(cellId, seed) > 0.62 ? 1 : 0)
      for(let b = 0; b < count; b++){
        const jx = (hash01(cellId, seed + b * 3) - 0.5) * cellW * 0.28
        const jy = (hash01(cellId, seed + b * 7) - 0.5) * cellH * 0.28
        const rad = dotRad * (0.88 + hash01(cellId, seed + b * 5) * 0.18)
        splatBall(acc, w, h, px + jx, py + jy, rad, 1)
      }
    }
  }

  const out = new Uint8ClampedArray(w * h * 4)
  for(let p = 0; p < w * h; p++){
    const ink = acc[p] >= inkThreshold ? Math.min(1, acc[p]) : 0
    const v = 255 - (ink * 255 | 0)
    const j = p * 4
    out[j] = out[j + 1] = out[j + 2] = v
    out[j + 3] = 255
  }
  return new ImageData(out, w, h)
}

/** @deprecated — crop broke XOR lattice alignment; kept for experiments. */
export function cropCanvasToActiveDisk(canvas, fill = 0.94){
  const w = canvas.width | 0
  const h = canvas.height | 0
  if(w < 16 || h < 16) return w
  const side = Math.max(16, Math.round(Math.min(w, h) * fill))
  const sx = ((w - side) / 2) | 0
  const sy = ((h - side) / 2) | 0
  const ctx = canvas.getContext("2d", { willReadFrequently: true })
  if(!ctx) return w
  const cropped = ctx.getImageData(sx, sy, side, side)
  canvas.width = side
  canvas.height = side
  ctx.putImageData(cropped, 0, 0)
  return side
}
