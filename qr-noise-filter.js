/**
 * Camera frame helpers for QR decode — crop, warp, blur.
 */

/** 3×3 box blur — tames LCD moire before binarize. */
export function boxBlurRgba(data, w, h, passes = 1){
  const tmp = new Uint8ClampedArray(data.length)
  for(let pass = 0; pass < passes; pass++){
    for(let y = 0; y < h; y++){
      for(let x = 0; x < w; x++){
        let r = 0, g = 0, b = 0, n = 0
        for(let dy = -1; dy <= 1; dy++){
          for(let dx = -1; dx <= 1; dx++){
            const xx = Math.max(0, Math.min(w - 1, x + dx))
            const yy = Math.max(0, Math.min(h - 1, y + dy))
            const i = (yy * w + xx) * 4
            r += data[i]; g += data[i + 1]; b += data[i + 2]; n++
          }
        }
        const o = (y * w + x) * 4
        tmp[o] = (r / n) | 0
        tmp[o + 1] = (g / n) | 0
        tmp[o + 2] = (b / n) | 0
        tmp[o + 3] = 255
      }
    }
    data.set(tmp)
  }
}

/** Push quad corners outward — centroids sit inset from the true QR edge. */
export function expandQuad(quad, scale = 1.06){
  const cx = (quad.tl.x + quad.tr.x + quad.br.x + quad.bl.x) * 0.25
  const cy = (quad.tl.y + quad.tr.y + quad.br.y + quad.bl.y) * 0.25
  const ex = (p) => ({ x: cx + (p.x - cx) * scale, y: cy + (p.y - cy) * scale })
  return { tl: ex(quad.tl), tr: ex(quad.tr), br: ex(quad.br), bl: ex(quad.bl) }
}

/**
 * Find the white paper / QR square in a camera frame (bright on dark).
 * Returns four corners for perspective warp before finder stamping.
 */
export function detectBrightQuad(data, W, H, thr = 168){
  let n = 0
  let minX = W, minY = H, maxX = 0, maxY = 0
  for(let y = 0; y < H; y += 2){
    for(let x = 0; x < W; x += 2){
      const i = (y * W + x) * 4
      const lum = data[i] * 0.299 + data[i + 1] * 0.587 + data[i + 2] * 0.114
      if(lum < thr) continue
      n++
      if(x < minX) minX = x
      if(y < minY) minY = y
      if(x > maxX) maxX = x
      if(y > maxY) maxY = y
    }
  }
  if(n < (W * H) * 0.04) return null
  const bw = maxX - minX
  const bh = maxY - minY
  if(bw < W * 0.25 || bh < H * 0.25) return null

  let tl = null, tr = null, br = null, bl = null
  let tlS = Infinity, trS = -Infinity, brS = -Infinity, blS = Infinity
  const step = Math.max(1, Math.round(Math.min(bw, bh) / 220))
  for(let y = minY; y <= maxY; y += step){
    for(let x = minX; x <= maxX; x += step){
      const i = (y * W + x) * 4
      const lum = data[i] * 0.299 + data[i + 1] * 0.587 + data[i + 2] * 0.114
      if(lum < thr) continue
      const s1 = x + y
      const s2 = x - y
      if(s1 < tlS){ tlS = s1; tl = { x, y } }
      if(s2 > trS){ trS = s2; tr = { x, y } }
      if(s1 > brS){ brS = s1; br = { x, y } }
      if(s2 < blS){ blS = s2; bl = { x, y } }
    }
  }
  if(!(tl && tr && br && bl)) return null
  return { tl, tr, br, bl }
}

function bilinearSample(data, W, H, x, y){
  const x0 = Math.floor(x), y0 = Math.floor(y)
  const x1 = x0 + 1, y1 = y0 + 1
  const tx = x - x0, ty = y - y0
  const clampX = (v) => Math.max(0, Math.min(W - 1, v))
  const clampY = (v) => Math.max(0, Math.min(H - 1, v))
  const at = (ix, iy) => {
    const p = (clampY(iy) * W + clampX(ix)) * 4
    return [data[p], data[p + 1], data[p + 2]]
  }
  const a = at(x0, y0), b = at(x1, y0), c = at(x0, y1), d = at(x1, y1)
  return [
    a[0] * (1 - tx) * (1 - ty) + b[0] * tx * (1 - ty) + c[0] * (1 - tx) * ty + d[0] * tx * ty,
    a[1] * (1 - tx) * (1 - ty) + b[1] * tx * (1 - ty) + c[1] * (1 - tx) * ty + d[1] * tx * ty,
    a[2] * (1 - tx) * (1 - ty) + b[2] * tx * (1 - ty) + c[2] * (1 - tx) * ty + d[2] * tx * ty
  ]
}

function mapQuad(u, v, tl, tr, br, bl){
  const topX = tl.x + (tr.x - tl.x) * u
  const topY = tl.y + (tr.y - tl.y) * u
  const botX = bl.x + (br.x - bl.x) * u
  const botY = bl.y + (br.y - bl.y) * u
  return {
    x: topX + (botX - topX) * v,
    y: topY + (botY - topY) * v
  }
}

export function warpQuadToSquare(data, W, H, quad, size = 512){
  const out = new Uint8ClampedArray(size * size * 4)
  const { tl, tr, br, bl } = quad
  for(let y = 0; y < size; y++){
    const v = (y + 0.5) / size
    for(let x = 0; x < size; x++){
      const u = (x + 0.5) / size
      const p = mapQuad(u, v, tl, tr, br, bl)
      const rgb = bilinearSample(data, W, H, p.x, p.y)
      const i = (y * size + x) * 4
      out[i] = rgb[0]
      out[i + 1] = rgb[1]
      out[i + 2] = rgb[2]
      out[i + 3] = 255
    }
  }
  return new ImageData(out, size, size)
}

export function coverCropSquare(videoOrCanvas, size = 512){
  const c = document.createElement("canvas")
  c.width = size
  c.height = size
  const ctx = c.getContext("2d", { willReadFrequently: true })
  const vw = videoOrCanvas.videoWidth || videoOrCanvas.width
  const vh = videoOrCanvas.videoHeight || videoOrCanvas.height
  const side = Math.min(vw, vh)
  const sx = ((vw - side) / 2) | 0
  const sy = ((vh - side) / 2) | 0
  ctx.drawImage(videoOrCanvas, sx, sy, side, side, 0, 0, size, size)
  return c
}
