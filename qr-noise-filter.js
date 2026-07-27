/**
 * Invertible QR noise filter (WebGL + CPU fallback).
 *
 * XOR with a deterministic cell hash — apply twice to restore.
 * Pipeline: QR → filter → camera → filter → decode.
 */

export const NOISE_SEED = 0x50415254
/** Coarser grid = more camera/warp tolerant (96 drifted ~3 cells from cyan under-expand). */
export const NOISE_SCALE = 48
/** Push cyan centroids out to true canvas corners (markers sit inset in the margin). */
export const CYAN_EXPAND = 1.12

const VERT = `
attribute vec2 aPos;
varying vec2 vUv;
void main(){
  vUv = aPos * 0.5 + 0.5;
  gl_Position = vec4(aPos, 0.0, 1.0);
}
`

const FRAG = `
precision highp float;
varying vec2 vUv;
uniform sampler2D uTex;
uniform vec2 uTexSize;
uniform float uSeed;
uniform float uScale;
uniform float uStrength;

const float MAX_CELL = 64.0;

float hash21(vec2 p){
  vec2 q = fract(p * 0.1031);
  q += dot(q, q.yx + 33.33);
  return fract((q.x + q.y) * q.y);
}

void main(){
  vec4 c = texture2D(uTex, vUv);
  float lum = dot(c.rgb, vec3(0.299, 0.587, 0.114));
  float bit = step(0.45, lum);
  vec2 cell = floor(vUv * uScale);
  float n = step(0.5, hash21(cell + vec2(uSeed, uSeed * 1.7)));
  float outBit = mix(bit, abs(bit - n), uStrength);
  gl_FragColor = vec4(vec3(outBit), 1.0);
}
`

function compile(gl, type, src){
  const s = gl.createShader(type)
  gl.shaderSource(s, src)
  gl.compileShader(s)
  if(!gl.getShaderParameter(s, gl.COMPILE_STATUS)){
    const err = gl.getShaderInfoLog(s)
    gl.deleteShader(s)
    throw new Error("shader: " + err)
  }
  return s
}

/** GLSL hash21 — must match fragment shader exactly. */
export function hash21Glsl(px, py){
  let qx = fract(px * 0.1031)
  let qy = fract(py * 0.1031)
  const dotVal = qx * (qy + 33.33) + qy * (qx + 33.33)
  qx = fract(qx + dotVal)
  qy = fract(qy + dotVal)
  return fract((qx + qy) * qy)
}

export function noiseBitAt(ux, uy, scale, seedNorm){
  const cx = Math.floor(ux * scale)
  const cy = Math.floor(uy * scale)
  return hash21Glsl(cx + seedNorm, cy + seedNorm * 1.7) >= 0.5 ? 1 : 0
}

export function otsuThreshold(data, w, h){
  const hist = new Uint32Array(256)
  const n = w * h
  for(let y = 0; y < h; y++){
    for(let x = 0; x < w; x++){
      const i = (y * w + x) * 4
      const lum = (data[i] * 299 + data[i + 1] * 587 + data[i + 2] * 114) / 1000 | 0
      hist[lum]++
    }
  }
  let sum = 0
  for(let i = 0; i < 256; i++) sum += i * hist[i]
  let sumB = 0, wB = 0, maxVar = 0, thr = 128
  for(let t = 0; t < 256; t++){
    wB += hist[t]
    if(!wB) continue
    const wF = n - wB
    if(!wF) break
    sumB += t * hist[t]
    const mB = sumB / wB
    const mF = (sum - sumB) / wF
    const v = wB * wF * (mB - mF) * (mB - mF)
    if(v > maxVar){ maxVar = v; thr = t }
  }
  return thr
}

/** Flip XOR output for dark-on-light display (TX dots mode). */
export function invertCanvasBinary(ctx, w, h){
  const img = ctx.getImageData(0, 0, w, h)
  const d = img.data
  for(let i = 0; i < d.length; i += 4){
    const v = d[i] >= 128 ? 0 : 255
    d[i] = d[i + 1] = d[i + 2] = v
  }
  ctx.putImageData(img, 0, 0)
}

/** Draw cyan L-brackets in the outer margin band — never over QR modules. */
export const QR_MARGIN_FRAC = 0.07

/** Draw cyan corner patches inside the margin, clear of CSS border-radius clip. */
export function drawCyanFiducialsInMargin(ctx, w, h, marginFrac = QR_MARGIN_FRAC){
  const margin = marginFrac * Math.min(w, h)
  // Keep patches fully inside the visible square (rounded clip eats ~5% of CSS edge).
  const inset = Math.max(4, Math.round(margin * 0.22))
  const s = Math.max(12, Math.round(margin * 0.55))
  ctx.save()
  ctx.fillStyle = "#5ac8fa"
  ctx.shadowColor = "rgba(90,200,250,0.85)"
  ctx.shadowBlur = Math.max(4, s * 0.2)
  ctx.fillRect(inset, inset, s, s)
  ctx.fillRect(w - inset - s, inset, s, s)
  ctx.fillRect(w - inset - s, h - inset - s, s, s)
  ctx.fillRect(inset, h - inset - s, s, s)
  ctx.restore()
}

/** @deprecated — draws over finder patterns; use drawCyanFiducialsInMargin */
export function drawCyanFiducials(ctx, w, h, inset = 0.04){
  drawCyanFiducialsInMargin(ctx, w, h, inset)
}

function fract(x){
  return x - Math.floor(x)
}

/**
 * CPU XOR — per-pixel binarize, cell-shared noise bit (matches WebGL shader).
 * Dotted QR + XOR yields fine salt-and-pepper static, not solid blocks.
 */
export function applyNoiseCpu(ctxOrImageData, w, h, {
  scale = NOISE_SCALE,
  seed = (NOISE_SEED % 10007) / 10007,
  strength = 1,
  threshold = null, // null = 0.45*255; number = fixed; 'otsu' computed from input
  cellAvg = false, // true on RX ball-cloud frames (moire + splat tolerant)
  darkOnLight = false // true when TX shows dark modules on white paper
} = {}){
  let img
  let ctx = null
  if(ctxOrImageData && ctxOrImageData.data && ctxOrImageData.width && !ctxOrImageData.canvas){
    img = ctxOrImageData
  }else{
    ctx = ctxOrImageData
    img = ctx.getImageData(0, 0, w, h)
  }
  const d = img.data
  let thr = typeof threshold === "number" ? threshold : 114.75
  if(threshold === "otsu") thr = otsuThreshold(d, w, h)

  if(cellAvg){
    const cellsX = scale
    const cellsY = scale
    const cellW = w / cellsX
    const cellH = h / cellsY
    for(let cy = 0; cy < cellsY; cy++){
      const y0 = Math.floor(cy * cellH)
      const y1 = Math.min(h, Math.floor((cy + 1) * cellH))
      const uy = (cy + 0.5) / cellsY
      for(let cx = 0; cx < cellsX; cx++){
        const x0 = Math.floor(cx * cellW)
        const x1 = Math.min(w, Math.floor((cx + 1) * cellW))
        let sum = 0, count = 0
        for(let y = y0; y < y1; y++){
          for(let x = x0; x < x1; x++){
            const i = (y * w + x) * 4
            sum += d[i] * 0.299 + d[i + 1] * 0.587 + d[i + 2] * 0.114
            count++
          }
        }
        const bit = count > 0 && (darkOnLight
          ? sum / count < thr
          : sum / count >= thr) ? 1 : 0
        const ux = (cx + 0.5) / cellsX
        const n = noiseBitAt(ux, uy, scale, seed)
        const out = strength >= 1 ? (bit ^ n) : bit
        const v = out ? 255 : 0
        for(let y = y0; y < y1; y++){
          for(let x = x0; x < x1; x++){
            const i = (y * w + x) * 4
            d[i] = d[i + 1] = d[i + 2] = v
            d[i + 3] = 255
          }
        }
      }
    }
  }else{
    const invW = 1 / w
    const invH = 1 / h
    for(let y = 0; y < h; y++){
      const uy = (y + 0.5) * invH
      for(let x = 0; x < w; x++){
        const i = (y * w + x) * 4
        const lum = d[i] * 0.299 + d[i + 1] * 0.587 + d[i + 2] * 0.114
        const bit = darkOnLight ? (lum < thr ? 1 : 0) : (lum >= thr ? 1 : 0)
        const ux = (x + 0.5) * invW
        const n = noiseBitAt(ux, uy, scale, seed)
        const out = strength >= 1 ? (bit ^ n) : bit
        const v = out ? 255 : 0
        d[i] = d[i + 1] = d[i + 2] = v
        d[i + 3] = 255
      }
    }
  }
  if(ctx) ctx.putImageData(img, 0, 0)
  return img
}

export class InvertibleNoiseFilter{
  constructor({ seed = NOISE_SEED, scale = NOISE_SCALE, strength = 1 } = {}){
    this.seed = seed >>> 0
    // Normalized seed for GLSL (avoid huge float precision loss)
    this.seedNorm = (this.seed % 10007) / 10007
    this.scale = scale
    this.strength = strength
    this.canvas = document.createElement("canvas")
    this.canvas.width = 64
    this.canvas.height = 64
    const gl = this.canvas.getContext("webgl", {
      alpha: false,
      premultipliedAlpha: false,
      preserveDrawingBuffer: true,
      antialias: false
    })
    if(!gl) throw new Error("WebGL unavailable for noise filter")
    this.gl = gl

    const vs = compile(gl, gl.VERTEX_SHADER, VERT)
    const fs = compile(gl, gl.FRAGMENT_SHADER, FRAG)
    const prog = gl.createProgram()
    gl.attachShader(prog, vs)
    gl.attachShader(prog, fs)
    gl.linkProgram(prog)
    if(!gl.getProgramParameter(prog, gl.LINK_STATUS)){
      throw new Error("program: " + gl.getProgramInfoLog(prog))
    }
    this.prog = prog
    this.aPos = gl.getAttribLocation(prog, "aPos")
    this.uTex = gl.getUniformLocation(prog, "uTex")
    this.uTexSize = gl.getUniformLocation(prog, "uTexSize")
    this.uSeed = gl.getUniformLocation(prog, "uSeed")
    this.uScale = gl.getUniformLocation(prog, "uScale")
    this.uStrength = gl.getUniformLocation(prog, "uStrength")

    const buf = gl.createBuffer()
    gl.bindBuffer(gl.ARRAY_BUFFER, buf)
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
      -1, -1, 1, -1, -1, 1,
      -1, 1, 1, -1, 1, 1
    ]), gl.STATIC_DRAW)
    this.buf = buf

    this.tex = gl.createTexture()
    gl.bindTexture(gl.TEXTURE_2D, this.tex)
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE)
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE)
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST)
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST)
  }

  apply(source){
    const gl = this.gl
    const w = source.width | 0
    const h = source.height | 0
    if(w < 1 || h < 1) return this.canvas
    if(this.canvas.width !== w || this.canvas.height !== h){
      this.canvas.width = w
      this.canvas.height = h
    }
    gl.viewport(0, 0, w, h)
    gl.useProgram(this.prog)
    gl.bindBuffer(gl.ARRAY_BUFFER, this.buf)
    gl.enableVertexAttribArray(this.aPos)
    gl.vertexAttribPointer(this.aPos, 2, gl.FLOAT, false, 0, 0)

    gl.activeTexture(gl.TEXTURE0)
    gl.bindTexture(gl.TEXTURE_2D, this.tex)
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true)
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, source)

    gl.uniform1i(this.uTex, 0)
    gl.uniform2f(this.uTexSize, w, h)
    gl.uniform1f(this.uSeed, this.seedNorm)
    gl.uniform1f(this.uScale, this.scale)
    gl.uniform1f(this.uStrength, this.strength)

    gl.drawArrays(gl.TRIANGLES, 0, 6)
    gl.finish()
    return this.canvas
  }

  readImageData(){
    const gl = this.gl
    const w = this.canvas.width
    const h = this.canvas.height
    const buf = new Uint8Array(w * h * 4)
    gl.readPixels(0, 0, w, h, gl.RGBA, gl.UNSIGNED_BYTE, buf)
    const data = new Uint8ClampedArray(w * h * 4)
    const row = w * 4
    for(let y = 0; y < h; y++){
      const src = (h - 1 - y) * row
      data.set(buf.subarray(src, src + row), y * row)
    }
    return new ImageData(data, w, h)
  }

  /** Filter source → write into dest 2d canvas via readPixels (reliable). */
  applyToCanvas(source, destCanvas){
    this.apply(source)
    const img = this.readImageData()
    if(destCanvas.width !== img.width || destCanvas.height !== img.height){
      destCanvas.width = img.width
      destCanvas.height = img.height
    }
    const ctx = destCanvas.getContext("2d")
    ctx.putImageData(img, 0, 0)
    return true
  }

  dispose(){
    const gl = this.gl
    if(!gl) return
    gl.deleteTexture(this.tex)
    gl.deleteBuffer(this.buf)
    gl.deleteProgram(this.prog)
  }
}

export function findCyanCentroid(data, W, H, x0, y0, w, h){
  let sx = 0, sy = 0, wsum = 0
  const x1 = Math.min(W, x0 + w)
  const y1 = Math.min(H, y0 + h)
  for(let y = Math.max(0, y0); y < y1; y++){
    for(let x = Math.max(0, x0); x < x1; x++){
      const p = (y * W + x) * 4
      const r = data[p], g = data[p + 1], b = data[p + 2]
      const peak = Math.max(r, g, b)
      const sat = peak - Math.min(r, g, b)
      if(!(g > r + 8 && b > r + 8)) continue
      if(Math.abs(g - b) > 70) continue
      if(sat < 18) continue
      const cyan = (g + b) * 0.5 - r
      if(cyan < 18) continue
      const weight = cyan * (0.5 + 0.5 * Math.min(1, sat / 80))
      if(weight < 16) continue
      sx += x * weight
      sy += y * weight
      wsum += weight
    }
  }
  if(wsum < 40) return null
  return { x: sx / wsum, y: sy / wsum }
}

/** Push quad corners outward — centroids sit inset from the true QR edge. */
export function expandQuad(quad, scale = 1.06){
  const cx = (quad.tl.x + quad.tr.x + quad.br.x + quad.bl.x) * 0.25
  const cy = (quad.tl.y + quad.tr.y + quad.br.y + quad.bl.y) * 0.25
  const ex = (p) => ({ x: cx + (p.x - cx) * scale, y: cy + (p.y - cy) * scale })
  return { tl: ex(quad.tl), tr: ex(quad.tr), br: ex(quad.br), bl: ex(quad.bl) }
}

/** 3×3 box blur — tames LCD moire before binarize/unfilter. */
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

export function detectCyanQuad(data, W, H){
  const pad = Math.round(Math.min(W, H) * 0.28)
  const tl = findCyanCentroid(data, W, H, 0, 0, pad, pad)
  const tr = findCyanCentroid(data, W, H, W - pad, 0, pad, pad)
  const br = findCyanCentroid(data, W, H, W - pad, H - pad, pad, pad)
  const bl = findCyanCentroid(data, W, H, 0, H - pad, pad, pad)
  if(!(tl && tr && br && bl)) return null
  return { tl, tr, br, bl }
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

  // Extreme bright pixels along diagonals ≈ perspective corners of the paper.
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
