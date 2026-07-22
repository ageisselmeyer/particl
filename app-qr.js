/**
 * PartiCl QR transfer mode — MDS fountain (any k of n QRs recover).
 * Particle codec lives in app.js for later.
 * RS is loaded dynamically so a failed import cannot blank the boot cloud.
 */
let rsEncode = null
let rsDecodeErasures = null

const canvasWrap = document.getElementById("canvasWrap")
const cloudCanvas = document.getElementById("cloud")
const qrImg = document.getElementById("qrImg")
const qrCanvas = document.getElementById("qrCanvas")
const fileInput = document.getElementById("fileInput")
const modeButtons = document.getElementById("modeButtons")
const statusEl = document.getElementById("status")
const video = document.getElementById("video")
const videoWrap = document.getElementById("videoWrap")
const downloadLink = document.getElementById("download")
const progressWrap = document.getElementById("decodeProgressWrap")
const progressBar = document.getElementById("decodeProgressBar")
const progressText = document.getElementById("decodeProgressText")
const decodeDebugEl = document.getElementById("decodeDebug")
const decodeMetersEl = document.getElementById("decodeMeters")
const meterAlignFill = document.getElementById("meterAlignFill")
const meterAlignVal = document.getElementById("meterAlignVal")
const meterSyncFill = document.getElementById("meterSyncFill")
const meterSyncVal = document.getElementById("meterSyncVal")
const meterSyncPeak = document.getElementById("meterSyncPeak")
const meterContrastFill = document.getElementById("meterContrastFill")
const meterContrastVal = document.getElementById("meterContrastVal")
const meterCrcFill = document.getElementById("meterCrcFill")
const meterCrcVal = document.getElementById("meterCrcVal")
const meterCrcPeak = document.getElementById("meterCrcPeak")

document.getElementById("btnEncode").addEventListener("click", () => {
  fileInput.value = ""
  setStatus("Choose a file to encode as QR frames.")
  fileInput.click()
})
document.getElementById("btnDecode").addEventListener("click", () => startDecoder())
fileInput.addEventListener("change", () => {
  if(fileInput.files?.[0]) encodeFile(fileInput.files[0])
})

function setStatus(msg){
  statusEl.textContent = msg || ""
}

// ~2KB file → 20 QR frames, any 10 recover (Reed–Solomon MDS across packets).
const TARGET_K = 10
const TARGET_N = 20
const MAX_N = 40 // hard cap — optical TX cannot usefully cycle thousands of frames
const MAX_SYMBOL_BYTES = 800 // larger QR capacity; keeps n small for bigger files
const PRERENDER_MAX = 48 // only prerender small transfers (bitmaps thrash past this)
const FRAME_HOLD_MS = 75
const QR_ECC = "Q"
const QR_CELL = 10
const QR_MARGIN = 8


let frames = [] // string payloads
let frameIndex = 0
let phaseStartedAt = 0
let txRun = 0
let meta = null
let txRaf = 0
let txBitmaps = [] // prerendered ImageBitmaps for fast blit
let txStatusAt = 0
let txLivePaint = false

function fountainRng(seed){
  let s = seed >>> 0
  return () => {
    s = (Math.imul(s, 1664525) + 1013904223) >>> 0
    return s / 4294967296
  }
}

function xorBytes(into, from){
  const n = Math.min(into.length, from.length)
  for(let i = 0; i < n; i++) into[i] ^= from[i]
}

/**
 * Decode fountain symbols → k source blocks.
 * Tries fast peel first, then GF(2) Gaussian elimination on the coefficient matrix
 * (works whenever received packets span the k sources — misses OK).
 */
function ltDecodePeel(k, symbolMap){
  const eqs = []
  for(const sym of symbolMap.values()){
    eqs.push({ indices: new Set(sym.indices), data: sym.data.slice() })
  }
  const known = new Array(k).fill(null)
  let changed = true
  while(changed){
    changed = false
    for(let e = eqs.length - 1; e >= 0; e--){
      const eq = eqs[e]
      for(const idx of [...eq.indices]){
        if(known[idx]){
          xorBytes(eq.data, known[idx])
          eq.indices.delete(idx)
        }
      }
      if(eq.indices.size === 0){
        eqs.splice(e, 1)
        continue
      }
      if(eq.indices.size === 1){
        const i = [...eq.indices][0]
        known[i] = eq.data
        eqs.splice(e, 1)
        changed = true
      }
    }
  }
  if(known.every(Boolean)) return known
  return ltDecodeGE(k, symbolMap)
}

/** Dense GF(2) Gauss–Jordan on packet coefficients; RHS is SYMBOL_SIZE-byte XOR vectors. */
function ltDecodeGE(k, symbolMap){
  const rows = []
  for(const sym of symbolMap.values()){
    const coef = new Uint8Array(k)
    for(const i of sym.indices) if(i >= 0 && i < k) coef[i] = 1
    // Skip empty equations
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
      const tmp = rows[row]
      rows[row] = rows[piv]
      rows[piv] = tmp
    }
    // Eliminate this column from every other row (RREF-style)
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
    // After RREF, pivot row should be e_col; still clear any higher 1s via knowns
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

/** Ideal+robust-ish degree: bias toward degree 1–3 for peelability, with some higher. */
function pickLtDegree(k, rnd){
  if(k <= 1) return 1
  const u = rnd()
  // ~40% degree-1 (systematic-like repair), ~30% deg 2, ~20% deg 3, rest up to min(k,8)
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

function utf8ToB64(str){
  return btoa(unescape(encodeURIComponent(str || "")))
}
function b64ToUtf8(b64){
  try{ return decodeURIComponent(escape(atob(b64))) }catch(_){ return atob(b64) }
}
function bytesToB64(bytes){
  let bin = ""
  const step = 0x8000
  for(let i = 0; i < bytes.length; i += step){
    bin += String.fromCharCode.apply(null, bytes.subarray(i, Math.min(i + step, bytes.length)))
  }
  return btoa(bin)
}
function b64ToBytes(b64){
  const bin = atob(b64)
  const out = new Uint8Array(bin.length)
  for(let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i)
  return out
}

function getQrCode(){
  const fn = globalThis.qrcode || window.qrcode
  if(typeof fn !== "function"){
    throw new Error("qrcode-generator not loaded (globalThis.qrcode missing)")
  }
  return fn
}

function getJsQR(){
  return typeof (globalThis.jsQR || window.jsQR) === "function"
    ? (globalThis.jsQR || window.jsQR)
    : null
}

function getZXing(){
  return globalThis.ZXing || window.ZXing || null
}

/** Morphological dilate — closes gaps between circular modules (main-thread fallback). */
function dilateImageDataInPlace(img, rad){
  const { data, width: w, height: h } = img
  const src = new Uint8ClampedArray(data)
  const r = Math.max(1, rad | 0)
  for(let y = r; y < h - r; y++){
    for(let x = r; x < w - r; x++){
      const i = (y * w + x) * 4
      if(src[i] < 140) continue
      let dark = false
      if(r === 1){
        if(src[i - 4] < 140 || src[i + 4] < 140 || src[i - w * 4] < 140 || src[i + w * 4] < 140) dark = true
        else if(src[i - w * 4 - 4] < 140 || src[i - w * 4 + 4] < 140 || src[i + w * 4 - 4] < 140 || src[i + w * 4 + 4] < 140) dark = true
      }else{
        for(let dy = -r; dy <= r && !dark; dy++){
          for(let dx = -r; dx <= r; dx++){
            if(src[((y + dy) * w + (x + dx)) * 4] < 140) dark = true
          }
        }
      }
      if(dark){
        data[i] = data[i + 1] = data[i + 2] = 0
        data[i + 3] = 255
      }
    }
  }
  return img
}

function rgbaToLuminance(img){
  const { data, width: w, height: h } = img
  const lum = new Uint8ClampedArray(w * h)
  for(let i = 0, j = 0; i < data.length; i += 4, j++){
    lum[j] = (data[i] * 3 + data[i + 1] * 4 + data[i + 2]) >> 3
  }
  return lum
}

function tryZXingOnImageData(img, w, h, tryHarder){
  const Z = getZXing()
  if(!Z || typeof Z.QRCodeReader !== "function") return null
  try{
    const src = new Z.RGBLuminanceSource(rgbaToLuminance(img), w, h)
    const bmp = new Z.BinaryBitmap(new Z.HybridBinarizer(src))
    const hints = new Map()
    if(tryHarder) hints.set(Z.DecodeHintType.TRY_HARDER, true)
    hints.set(Z.DecodeHintType.POSSIBLE_FORMATS, [Z.BarcodeFormat.QR_CODE])
    const result = new Z.QRCodeReader().decode(bmp, hints)
    return result && result.getText ? result.getText() : null
  }catch(_){
    return null
  }
}

function tryJsQROnImageData(jsQR, img, w, h){
  const code = jsQR(img.data, w, h, { inversionAttempts: "dontInvert" })
  return code && code.data ? code.data : null
}

// --- Decode workers + frame backlog ---
const DECODE_QUEUE_MAX = 10
const DECODE_WORKER_COUNT = Math.min(4, Math.max(2, (navigator.hardwareConcurrency || 4) >> 1))
let decodeWorkers = []
let decodeWorkersFree = []
let decodeJobId = 0
let decodeQueue = [] // {id, width, height, buffer, dilate, tryHarder}
let decodeUiTick = 0

function ensureDecodeWorkers(){
  if(decodeWorkers.length) return
  const url = new URL("decode-worker.js", import.meta.url)
  for(let i = 0; i < DECODE_WORKER_COUNT; i++){
    try{
      const w = new Worker(url)
      w.onmessage = onDecodeWorkerMessage
      w.onerror = () => {
        const idx = decodeWorkersFree.indexOf(w)
        if(idx >= 0) decodeWorkersFree.splice(idx, 1)
      }
      decodeWorkers.push(w)
      decodeWorkersFree.push(w)
    }catch(e){
      console.warn("decode worker unavailable", e)
      break
    }
  }
}

function stopDecodeWorkers(){
  for(const w of decodeWorkers){
    try{ w.terminate() }catch(_){}
  }
  decodeWorkers = []
  decodeWorkersFree = []
  decodeQueue = []
}

function onDecodeWorkerMessage(ev){
  const msg = ev.data
  if(!msg || msg.type !== "result") return
  const w = ev.target
  if(decodeWorkers.includes(w) && !decodeWorkersFree.includes(w)) decodeWorkersFree.push(w)
  pumpDecodeQueue()
  if(!decodeRunning || rxRecovered) return
  if(msg.text) handleDecodedText(msg.text, msg.engine ? `${msg.engine}@${msg.w}d${msg.dilate}` : "worker")
}

function pumpDecodeQueue(){
  while(decodeWorkersFree.length && decodeQueue.length){
    const worker = decodeWorkersFree.pop()
    const job = decodeQueue.shift()
    try{
      worker.postMessage({
        type: "decode",
        id: job.id,
        width: job.width,
        height: job.height,
        dilate: job.dilate,
        tryHarder: job.tryHarder,
        buffer: job.buffer
      }, [job.buffer])
    }catch(e){
      decodeWorkersFree.push(worker)
      console.warn(e)
    }
  }
}

function enqueueDecodeJob(imgData, dilate, tryHarder){
  // Drop oldest when backlog is full — prefer freshest frames at high TX fps
  while(decodeQueue.length >= DECODE_QUEUE_MAX) decodeQueue.shift()
  const copy = imgData.data.slice(0) // detachable copy
  decodeQueue.push({
    id: ++decodeJobId,
    width: imgData.width,
    height: imgData.height,
    dilate,
    tryHarder,
    buffer: copy.buffer
  })
  pumpDecodeQueue()
}

function handleDecodedText(text, engineLabel){
  qrHitStreak++
  qrMissStreak = 0
  decodeDbg.hits++
  decodeDbg.engine = engineLabel || decodeDbg.engine
  decodeDbg.last = text.slice(0, 48) + (text.length > 48 ? "…" : "")
  if(text !== lastQrText){
    lastQrText = text
    if(ingestPayloadText(text)){
      rxPayloadOk = true
      setStatus(`MDS ${rxSymbols.size}/${rxN} · need any ${rxK} · q${decodeQueue.length}`)
      tryFinish()
    }else{
      decodeDbg.last = `ignored: ${text.slice(0, 40)}`
    }
  }else if(rxFountain && rxSymbols.size >= (rxK || 0)){
    tryFinish()
  }
}

/** Grab one camera frame into the backlog (non-blocking decode). */
function captureFrameToQueue(){
  if(!video.videoWidth) return
  const w = video.videoWidth
  const h = video.videoHeight
  // Single lean capture size — workers try dilate variants via alternating jobs
  const max = 720
  const scale = Math.min(1, max / Math.max(w, h))
  const cw = Math.max(1, (w * scale) | 0)
  const ch = Math.max(1, (h * scale) | 0)
  ensureScanCanvas(cw, ch)
  scanCtx.drawImage(video, 0, 0, w, h, 0, 0, cw, ch)
  const img = scanCtx.getImageData(0, 0, cw, ch)
  const variant = decodeFrameNo % 3
  const dilate = variant === 0 ? 1 : (variant === 1 ? 2 : 0)
  const tryHarder = qrMissStreak > 8 || variant === 1
  enqueueDecodeJob(img, dilate, tryHarder)
}

async function scanNativeDetector(){
  if(!detector || !video.videoWidth) return null
  try{
    const codes = await detector.detect(video)
    if(codes && codes.length){
      decodeDbg.engine = "BarcodeDetector"
      return codes[0].rawValue || null
    }
  }catch(_){}
  return null
}

/** Main-thread fallback when workers unavailable. */
function scanQrOnMainThread(){
  const jsQR = getJsQR()
  const hasZx = !!getZXing()
  if(!jsQR && !hasZx) return null
  const w = video.videoWidth
  const h = video.videoHeight
  if(!w) return null
  const scale = Math.min(1, 640 / Math.max(w, h))
  const cw = Math.max(1, (w * scale) | 0)
  const ch = Math.max(1, (h * scale) | 0)
  ensureScanCanvas(cw, ch)
  scanCtx.drawImage(video, 0, 0, w, h, 0, 0, cw, ch)
  const img = scanCtx.getImageData(0, 0, cw, ch)
  dilateImageDataInPlace(img, 1)
  if(hasZx){
    const zx = tryZXingOnImageData(img, cw, ch, qrMissStreak > 5)
    if(zx){ decodeDbg.engine = `ZXing@${cw}`; return zx }
  }
  if(jsQR){
    const data = tryJsQROnImageData(jsQR, img, cw, ch)
    if(data){ decodeDbg.engine = `jsQR@${cw}`; return data }
  }
  return null
}

const CLOUD_PIXEL = 1024
const PARTICLES_ON = 5
const PARTICLES_FINDER = 9
const PARTICLES_OFF = 0.02

let cloudParticles = null
let cloudMeta = null
let cloudAnimT0 = 0

function hash01local(a, b){
  let x = Math.imul(a ^ (b * 0x9e3779b9), 0x85ebca6b) >>> 0
  x ^= x >>> 16
  x = Math.imul(x, 0xc2b2ae35) >>> 0
  return ((x >>> 0) / 4294967296)
}

function isFinderCell(r, c, n){
  const inPat = (rr, cc) => rr >= 0 && rr < 7 && cc >= 0 && cc < 7
  return inPat(r, c) || inPat(r, c - (n - 7)) || inPat(r - (n - 7), c)
}

function buildQrMatrix(text){
  const qrcode = getQrCode()
  const qr = qrcode(0, QR_ECC)
  qr.addData(String(text), "Byte")
  qr.make()
  return qr
}

/**
 * Watch-pairing style: the QR *is* a cloud of blue particles.
 * Keep modules sparse enough that the field stays dark (not a washed-out white square).
 */
function spawnCloudFromText(text){
  const qr = buildQrMatrix(text)
  const n = qr.getModuleCount()
  const particles = []
  for(let r = 0; r < n; r++){
    for(let c = 0; c < n; c++){
      const on = qr.isDark(r, c)
      const finder = on && isFinderCell(r, c, n)
      const count = on
        ? (finder ? PARTICLES_FINDER : PARTICLES_ON)
        : (hash01local(r, c + 17) < PARTICLES_OFF ? 1 : 0)
      for(let i = 0; i < count; i++){
        const u = hash01local(r * 131 + c, i * 17 + 3)
        const v = hash01local(c * 97 + r, i * 29 + 11)
        const ox = (u - 0.5) * (on ? 0.45 : 0.8)
        const oy = (v - 0.5) * (on ? 0.45 : 0.8)
        particles.push({
          r, c, on, finder,
          ox, oy,
          phase: u * Math.PI * 2,
          spin: 0.5 + v * 1.1,
          size: on ? (finder ? 0.95 : 0.65 + u * 0.25) : 0.28,
          bright: on ? (finder ? 0.9 : 0.55 + v * 0.2) : 0.05
        })
      }
    }
  }
  cloudParticles = particles
  cloudMeta = { n, margin: 0.12 }
  cloudAnimT0 = performance.now()
  return { n, particles }
}

function ensureCloudCanvas(){
  if(!cloudCanvas) throw new Error("cloud canvas missing")
  cloudCanvas.hidden = false
  cloudCanvas.style.display = "block"
  cloudCanvas.style.background = "#fff"
  // Fixed backing store. Do NOT pass {alpha:false} — if a 2d context was
  // already created (classic boot script), mismatched attrs return null and
  // leave a cleared white canvas.
  if(cloudCanvas.width !== CLOUD_PIXEL || cloudCanvas.height !== CLOUD_PIXEL){
    cloudCanvas.width = CLOUD_PIXEL
    cloudCanvas.height = CLOUD_PIXEL
  }
  const ctx = cloudCanvas.getContext("2d")
  if(!ctx) throw new Error("2d context unavailable")
  return ctx
}

function paintParticleCloud(now){
  const ctx = ensureCloudCanvas()
  const W = cloudCanvas.width

  // Always paint black first so a failed spawn never leaves a white bitmap
  ctx.globalCompositeOperation = "source-over"
  ctx.fillStyle = "#000000"
  ctx.fillRect(0, 0, W, W)

  if(!cloudParticles || !cloudMeta) return

  const { n, margin } = cloudMeta
  const t = ((now || performance.now()) - cloudAnimT0) * 0.001

  const bg = ctx.createRadialGradient(W * 0.5, W * 0.48, W * 0.08, W * 0.5, W * 0.5, W * 0.7)
  bg.addColorStop(0, "#071526")
  bg.addColorStop(0.6, "#03080f")
  bg.addColorStop(1, "#000000")
  ctx.fillStyle = bg
  ctx.fillRect(0, 0, W, W)

  const field = W * (1 - 2 * margin)
  const cell = field / n
  const origin = W * margin

  ctx.beginPath()
  ctx.arc(W / 2, W / 2, field * 0.52, 0, Math.PI * 2)
  ctx.strokeStyle = "rgba(60,150,255,0.1)"
  ctx.lineWidth = Math.max(2, W * 0.006)
  ctx.stroke()

  // Soft discs per ON module (QR silhouette), then sparkle particles
  ctx.globalCompositeOperation = "source-over"
  const seen = new Set()
  for(const p of cloudParticles){
    if(!p.on) continue
    const key = p.r * 1024 + p.c
    if(seen.has(key)) continue
    seen.add(key)
    const x = origin + (p.c + 0.5) * cell
    const y = origin + (p.r + 0.5) * cell
    const rad = cell * (p.finder ? 0.42 : 0.34)
    const g = ctx.createRadialGradient(x, y, 0, x, y, rad)
    g.addColorStop(0, p.finder ? "rgba(200,236,255,0.95)" : "rgba(140,210,255,0.88)")
    g.addColorStop(0.55, p.finder ? "rgba(40,160,255,0.75)" : "rgba(20,120,255,0.55)")
    g.addColorStop(1, "rgba(0,30,80,0)")
    ctx.fillStyle = g
    ctx.beginPath()
    ctx.arc(x, y, rad, 0, Math.PI * 2)
    ctx.fill()
  }

  ctx.globalCompositeOperation = "lighter"
  for(const p of cloudParticles){
    const drift = p.on ? 0.08 : 0.15
    const jx = Math.sin(t * p.spin + p.phase) * drift
    const jy = Math.cos(t * (p.spin * 0.87) + p.phase * 1.3) * drift
    const x = origin + (p.c + 0.5 + p.ox + jx) * cell
    const y = origin + (p.r + 0.5 + p.oy + jy) * cell
    const rad = Math.max(1.1, cell * 0.18 * p.size)
    const g = ctx.createRadialGradient(x, y, 0, x, y, rad)
    if(p.on){
      g.addColorStop(0, `rgba(220,245,255,${0.7 * p.bright})`)
      g.addColorStop(0.35, `rgba(80,190,255,${0.45 * p.bright})`)
      g.addColorStop(1, "rgba(0,50,140,0)")
    }else{
      g.addColorStop(0, `rgba(80,160,255,${p.bright})`)
      g.addColorStop(1, "rgba(0,40,100,0)")
    }
    ctx.fillStyle = g
    ctx.beginPath()
    ctx.arc(x, y, rad, 0, Math.PI * 2)
    ctx.fill()
  }

  ctx.globalCompositeOperation = "source-over"
}

function drawQrToCanvas(text){
  if(typeof window.__particlPaintCloud === "function"){
    if(window.__particlPaintCloud(text)) return
  }
  spawnCloudFromText(text)
  paintParticleCloud(performance.now())
}

function blitTxBitmap(index){
  const bmp = txBitmaps[index]
  if(!bmp || !cloudCanvas) return false
  if(cloudCanvas.width !== bmp.width || cloudCanvas.height !== bmp.height){
    cloudCanvas.width = bmp.width
    cloudCanvas.height = bmp.height
  }
  const ctx = cloudCanvas.getContext("2d")
  if(!ctx) return false
  ctx.drawImage(bmp, 0, 0)
  return true
}

function clearTxBitmaps(){
  for(const b of txBitmaps){
    try{ b.close() }catch(_){}
  }
  txBitmaps = []
}

async function prerenderTxFrames(texts){
  clearTxBitmaps()
  if(typeof window.__particlPaintCloud !== "function") return false
  if(texts.length > PRERENDER_MAX) return false
  setStatus(`Rendering ${texts.length} QR frames…`)
  for(let i = 0; i < texts.length; i++){
    window.__particlPaintCloud(texts[i])
    const bmp = await createImageBitmap(cloudCanvas)
    txBitmaps.push(bmp)
    if((i & 1) === 0){
      setStatus(`Rendering QR frames… ${i + 1}/${texts.length}`)
      await new Promise((r) => requestAnimationFrame(r))
    }
  }
  return txBitmaps.length === texts.length
}

function showQrUi(){
  if(qrImg) qrImg.hidden = true
  if(cloudCanvas){
    cloudCanvas.hidden = false
    cloudCanvas.style.display = "block"
    cloudCanvas.style.background = "#fff"
  }
  const align = document.getElementById("alignFrame")
  if(align) align.hidden = true
  canvasWrap.classList.remove("tx-cloud")
  canvasWrap.classList.add("tx-paper")
  canvasWrap.style.background = "#fff"
  canvasWrap.style.display = ""
  videoWrap.hidden = true
}

function planCoding(fileLen){
  let k = TARGET_K
  let n = TARGET_N
  let sym = Math.max(1, Math.ceil(fileLen / k))
  while(sym > MAX_SYMBOL_BYTES && n < MAX_N){
    k += 1
    n = Math.min(MAX_N, k * 2)
    if(n >= MAX_N){
      k = Math.floor(MAX_N / 2)
      n = MAX_N
    }
    sym = Math.max(1, Math.ceil(fileLen / k))
  }
  return { k, n, sym, nsym: n - k }
}

async function ensureRs(){
  if(typeof rsEncode === "function" && typeof rsDecodeErasures === "function") return
  const mod = await import("./rs.js")
  rsEncode = mod.rsEncode
  rsDecodeErasures = mod.rsDecodeErasures
}

/** Per-byte-column RS: n packets, any k recover the k source blocks. */
function encodeRsPackets(sources, n){
  if(typeof rsEncode !== "function") throw new Error("Reed-Solomon not loaded yet")
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
  if(typeof rsDecodeErasures !== "function") throw new Error("Reed-Solomon not loaded yet")
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
    if(!col || col.length !== k) return null
    for(let j = 0; j < k; j++) sources[j][b] = col[j]
  }
  return sources
}

function buildFrames(fileBytes, fileMeta){
  const fileId = (crypto.getRandomValues(new Uint32Array(1))[0] >>> 0).toString(36)
  const { k, n, sym } = planCoding(fileBytes.length)
  const padded = new Uint8Array(k * sym)
  padded.set(fileBytes)
  const sources = []
  for(let i = 0; i < k; i++) sources.push(padded.subarray(i * sym, (i + 1) * sym))
  const packetData = encodeRsPackets(sources, n)

  const order = Array.from({ length: n }, (_, i) => i)
  for(let i = order.length - 1; i > 0; i--){
    const j = Math.floor(hash01(i, 91) * (i + 1))
    const t = order[i]; order[i] = order[j]; order[j] = t
  }

  const out = []
  for(let pi = 0; pi < order.length; pi++){
    const seq = order[pi]
    // Meta (incl. filename) on every frame so download name survives missed packets
    const dataB64 = bytesToB64(packetData[seq])
    const payload = [
      "PC7M",
      fileId,
      String(k),
      String(n),
      String(fileMeta.size >>> 0),
      utf8ToB64(fileMeta.name || "file"),
      utf8ToB64(fileMeta.type || "application/octet-stream"),
      String(seq),
      dataB64
    ].join("|")
    out.push(payload)
  }
  out._fountain = { k, n, r: n - k, sym, total: n, need: k }
  return out
}

function encodeFile(file){
  const reader = new FileReader()
  reader.onload = async () => {
    try{
      await ensureRs()
      const bytes = new Uint8Array(reader.result)
      meta = {
        name: file.name || "recovered_file",
        type: file.type || "application/octet-stream",
        size: bytes.length
      }
      frames = buildFrames(bytes, meta)
      const qrcode = getQrCode()
      const longest = frames.reduce((a, b) => (a.length >= b.length ? a : b), "")
      let probe
      try{
        probe = qrcode(0, QR_ECC)
        probe.addData(longest, "Byte")
        probe.make()
      }catch(e){
        throw new Error(
          `File too large for one QR burst (${(bytes.length / 1024).toFixed(0)} KB → ${frames.length} frames). ` +
          `Try a smaller file (a few KB works best).`
        )
      }
      window.__particlQrType = Math.round((probe.getModuleCount() - 17) / 4)

      frameIndex = 0
      txRun++
      modeButtons.classList.add("is-hidden")
      showQrUi()

      txLivePaint = frames.length > PRERENDER_MAX
      if(!txLivePaint){
        const ok = await prerenderTxFrames(frames)
        if(!ok){
          clearTxBitmaps()
          txLivePaint = true
        }
      }else{
        clearTxBitmaps()
      }
      if(txLivePaint) drawQrToCanvas(frames[0])
      else blitTxBitmap(0)

      // Start clock AFTER prerender so we don't catch up a huge elapsed gap
      phaseStartedAt = performance.now()
      txStatusAt = 0

      if(txRaf) cancelAnimationFrame(txRaf)
      const run = txRun
      const loop = (now) => {
        if(run !== txRun) return
        tickTx(now)
        txRaf = requestAnimationFrame(loop)
      }
      txRaf = requestAnimationFrame(loop)
      const ft = frames._fountain || {}
      setStatus(
        `QR · “${meta.name}” · ${frames.length} frames · ` +
        `need any ${ft.need} of ${ft.total} · point camera here`
      )
    }catch(err){
      console.error(err)
      modeButtons.classList.remove("is-hidden")
      setStatus(`Encode failed: ${err.message || err}`)
    }
  }
  reader.readAsArrayBuffer(file)
}

function tickTx(now){
  if(!frames.length) return
  if(!phaseStartedAt) phaseStartedAt = now
  let elapsed = now - phaseStartedAt
  // Advance at most one frame per rAF — no catch-up skip after a hitch
  if(elapsed >= FRAME_HOLD_MS){
    phaseStartedAt = now
    frameIndex = (frameIndex + 1) % frames.length
    if(txLivePaint || txBitmaps.length !== frames.length) drawQrToCanvas(frames[frameIndex])
    else blitTxBitmap(frameIndex)
    if(now - txStatusAt > 200){
      txStatusAt = now
      setStatus(`Cloud frame ${frameIndex + 1} / ${frames.length} · “${meta?.name || "file"}”`)
    }
  }
}

// --- Decode ---
let rxChunks = new Map()
let rxHave = new Set()
let rxTotal = null
let rxFileId = null
let rxMeta = null
let rxFountain = false
let rxK = null
let rxN = null
let rxR = null
let rxSymLen = null
let rxSymbols = new Map()
let rxDecodeCount = 0
let rxPayloadOk = false
let rxRecovered = false
let decodeRunning = false
let detector = null
let decodeFrameNo = 0
let lastQrText = ""
let qrHitStreak = 0
let qrMissStreak = 0
let scanCanvas = null
let scanCtx = null

const decodeDbg = {
  video: "—",
  engine: "—",
  hits: 0,
  unique: 0,
  last: "idle",
  fps: "—"
}
let decodeDbgLastT = 0
let decodeDbgFpsEma = 0

const decodeQuality = {
  alignPct: 0,
  syncNow: 0,
  syncPeak: 0,
  contrastPeak: 0,
  crcPeak: 0,
  crcScore: 0
}

function resetDecodeQuality(){
  decodeQuality.alignPct = 0
  decodeQuality.syncNow = 0
  decodeQuality.syncPeak = 0
  decodeQuality.contrastPeak = 0
  decodeQuality.crcPeak = 0
  decodeQuality.crcScore = 0
}

function setMeter(fill, valEl, peakEl, pct, label, peakPct){
  if(fill) fill.style.width = `${Math.max(0, Math.min(100, pct))}%`
  if(valEl) valEl.textContent = label
  if(peakEl && peakPct != null) peakEl.style.left = `${Math.max(0, Math.min(100, peakPct))}%`
}

function updateDecodeMeters(){
  const align = qrHitStreak > 0 ? 100 : Math.max(0, 40 - qrMissStreak * 2)
  decodeQuality.alignPct = align
  setMeter(meterAlignFill, meterAlignVal, null, align, qrHitStreak > 0 ? "100% · QR lock" : `${align|0}% · searching`)

  const syncNow = qrHitStreak > 0 ? 32 : 0
  decodeQuality.syncNow = syncNow
  if(syncNow > decodeQuality.syncPeak) decodeQuality.syncPeak = syncNow
  setMeter(
    meterSyncFill, meterSyncVal, meterSyncPeak,
    (syncNow / 32) * 100,
    qrHitStreak > 0 ? `QR hit · streak ${qrHitStreak}` : `waiting · best ${decodeQuality.syncPeak ? "yes" : "no"}`,
    (decodeQuality.syncPeak / 32) * 100
  )

  setMeter(meterContrastFill, meterContrastVal, null, qrHitStreak > 0 ? 100 : 10, `QR · ${decodeDbg.engine}`)

  let crcScore = 0
  let crcLabel = "waiting"
  if(rxRecovered || rxPayloadOk){
    const need = Math.max(1, rxK || 1)
    crcScore = rxRecovered ? 100 : Math.min(95, Math.round((rxSymbols.size / need) * 95))
    crcLabel = rxRecovered
      ? "recovered"
      : `${rxSymbols.size}/${rxK} of ${rxN ?? "?"}`
  }
  decodeQuality.crcScore = crcScore
  if(crcScore > decodeQuality.crcPeak) decodeQuality.crcPeak = crcScore
  setMeter(
    meterCrcFill, meterCrcVal, meterCrcPeak,
    crcScore,
    `${crcLabel} · best ${decodeQuality.crcPeak}%`,
    decodeQuality.crcPeak
  )
}

function updateDecodeDebug(){
  if(!decodeDebugEl) return
  decodeDebugEl.textContent = [
    `frame ${decodeFrameNo} · ${decodeDbg.video} · ~${decodeDbg.fps} fps`,
    `engine ${decodeDbg.engine} · hits ${decodeDbg.hits} · streak ${qrHitStreak}`,
    `mds unique=${rxSymbols.size}/${rxN ?? "?"} · need ${rxK ?? "?"} · scans=${rxDecodeCount}`,
    `last: ${decodeDbg.last}`
  ].join("\n")
}

function resetRxState(){
  rxChunks = new Map()
  rxHave = new Set()
  rxTotal = null
  rxFileId = null
  rxMeta = null
  rxFountain = false
  rxK = null
  rxN = null
  rxR = null
  rxSymLen = null
  rxSymbols = new Map()
  rxDecodeCount = 0
  rxPayloadOk = false
  rxRecovered = false
  lastQrText = ""
  qrHitStreak = 0
  qrMissStreak = 0
}

function ingestMdsSymbol(fileId, k, n, seq, data){
  if(!Number.isFinite(k) || !Number.isFinite(n) || k < 1 || n < k) return false
  if(!Number.isFinite(seq) || seq < 0 || seq >= n) return false
  if(!data || !data.length) return false
  if(rxFileId == null) rxFileId = fileId
  if(fileId !== rxFileId) return false
  if(rxSymLen != null && data.length !== rxSymLen) return false
  rxFountain = true
  rxK = k
  rxN = n
  rxR = n - k
  rxTotal = k
  rxSymLen = data.length
  rxDecodeCount++
  if(rxSymbols.has(seq)) return true
  rxSymbols.set(seq, Uint8Array.from(data))
  rxHave.add(seq)
  return true
}

function ingestPayloadText(text){
  if(!text || typeof text !== "string") return false
  if(text.startsWith("PC7M|")){
    const parts = text.split("|")
    if(parts.length < 9) return false
    const fileId = parts[1]
    const k = parseInt(parts[2], 10)
    const n = parseInt(parts[3], 10)
    const size = parseInt(parts[4], 10)
    const name = b64ToUtf8(parts[5])
    const type = b64ToUtf8(parts[6])
    const seq = parseInt(parts[7], 10)
    const data = b64ToBytes(parts.slice(8).join("|"))
    if(!ingestMdsSymbol(fileId, k, n, seq, data)) return false
    rxMeta = {
      name: (name && name.trim()) ? name.trim() : (rxMeta?.name || "recovered_file"),
      type: (type && type.trim()) ? type.trim() : (rxMeta?.type || "application/octet-stream"),
      size: Number.isFinite(size) ? size : (rxMeta?.size ?? null)
    }
    return true
  }
  if(text.startsWith("PC7|")){
    const parts = text.split("|")
    if(parts.length < 6) return false
    const fileId = parts[1]
    const k = parseInt(parts[2], 10)
    const n = parseInt(parts[3], 10)
    const seq = parseInt(parts[4], 10)
    const data = b64ToBytes(parts.slice(5).join("|"))
    return ingestMdsSymbol(fileId, k, n, seq, data)
  }
  return false
}

function tryRecoverSources(){
  if(!rxFountain || rxK == null || rxN == null || rxSymLen == null) return null
  if(rxSymbols.size < rxK) return null
  return decodeRsPackets(rxSymbols, rxK, rxN, rxSymLen)
}

function tryFinishFountain(){
  const sources = tryRecoverSources()
  if(!sources) return false
  if(!rxMeta) rxMeta = { name: "recovered_file", type: "application/octet-stream", size: null }
  const merged = new Uint8Array(rxK * rxSymLen)
  for(let i = 0; i < rxK; i++) merged.set(sources[i], i * rxSymLen)
  const finalBytes = rxMeta.size != null ? merged.slice(0, rxMeta.size) : merged
  const blob = new Blob([finalBytes], { type: rxMeta.type || "application/octet-stream" })
  const url = URL.createObjectURL(blob)
  const rawName = String(rxMeta.name || "recovered_file").trim() || "recovered_file"
  const safeName = rawName.replace(/[/\\?%*:|"<>]/g, "_")
  downloadLink.href = url
  downloadLink.download = safeName
  downloadLink.hidden = false
  progressBar.style.width = "100%"
  progressText.textContent = "Done"
  setStatus(
    `Recovered “${safeName}” (${finalBytes.length} bytes) · ` +
    `${rxSymbols.size}/${rxN} QRs (need ${rxK})`
  )
  try{ downloadLink.click() }catch(_){}
  rxRecovered = true
  decodeRunning = false
  stopDecodeWorkers()
  return true
}

function tryFinish(){
  return tryFinishFountain()
}

async function tuneDecoderCamera(stream){
  const track = stream.getVideoTracks()[0]
  if(!track) return {}
  const caps = typeof track.getCapabilities === "function" ? track.getCapabilities() : {}
  const advanced = {}
  if(Array.isArray(caps.focusMode) && caps.focusMode.includes("continuous")) advanced.focusMode = "continuous"
  if(Array.isArray(caps.exposureMode) && caps.exposureMode.includes("continuous")) advanced.exposureMode = "continuous"
  if(Array.isArray(caps.whiteBalanceMode) && caps.whiteBalanceMode.includes("continuous")) advanced.whiteBalanceMode = "continuous"
  if(Object.keys(advanced).length){
    try{ await track.applyConstraints({ advanced: [advanced] }) }catch(_){}
  }
  try{ await track.applyConstraints({ frameRate: { ideal: 30 } }) }catch(_){}
  try{
    await track.applyConstraints({
      width: { ideal: 1920 },
      height: { ideal: 1080 },
      facingMode: { ideal: "environment" }
    })
  }catch(_){}
  return typeof track.getSettings === "function" ? track.getSettings() : {}
}

function formatCaptureLabel(settings, vw, vh){
  const w = settings.width || vw || 0
  const h = settings.height || vh || 0
  const fps = settings.frameRate != null ? settings.frameRate.toFixed(0) : "?"
  return `${w}×${h} @ ~${fps} fps`
}

function ensureScanCanvas(w, h){
  if(!scanCanvas){
    scanCanvas = document.createElement("canvas")
    scanCtx = scanCanvas.getContext("2d", { willReadFrequently: true })
  }
  if(scanCanvas.width !== w || scanCanvas.height !== h){
    scanCanvas.width = w
    scanCanvas.height = h
  }
  return { sw: w, sh: h }
}

async function startDecoder(){
  try{ await ensureRs() }catch(e){
    setStatus(`RS load failed: ${e.message || e}`)
    return
  }
  txRun = 0
  frames = []
  clearTxBitmaps()
  if(txRaf) cancelAnimationFrame(txRaf)
  modeButtons.classList.add("is-hidden")
  canvasWrap.style.display = "none"
  videoWrap.hidden = false
  progressWrap.hidden = false
  downloadLink.hidden = true
  resetRxState()
  resetDecodeQuality()
  decodeFrameNo = 0
  progressBar.style.width = "0%"
  progressText.textContent = "QR: 0"
  if(decodeMetersEl) decodeMetersEl.hidden = true
  if(decodeDebugEl) decodeDebugEl.hidden = true
  lastQrText = ""
  qrHitStreak = 0
  qrMissStreak = 0
  ensureDecodeWorkers()

  let captureSettings = {}
  try{
    const stream = await navigator.mediaDevices.getUserMedia({
      video: {
        facingMode: { ideal: "environment" },
        width: { ideal: 1280 },
        height: { ideal: 720 },
        frameRate: { ideal: 30 }
      },
      audio: false
    })
    video.srcObject = stream
    await video.play().catch(() => {})
    captureSettings = await tuneDecoderCamera(stream)
  }catch(_){
    try{
      const stream = await navigator.mediaDevices.getUserMedia({
        video: { facingMode: "environment" },
        audio: false
      })
      video.srcObject = stream
      await video.play().catch(() => {})
      captureSettings = await tuneDecoderCamera(stream)
    }catch(__){
      setStatus("Could not access camera.")
      modeButtons.classList.remove("is-hidden")
      canvasWrap.style.display = ""
      videoWrap.hidden = true
      return
    }
  }

  detector = null
  if("BarcodeDetector" in window){
    try{ detector = new BarcodeDetector({ formats: ["qr_code"] }) }catch(_){ detector = null }
  }

  decodeRunning = true
  const showCaptureStatus = () => {
    const capLabel = formatCaptureLabel(captureSettings, video.videoWidth, video.videoHeight)
    const wlab = decodeWorkers.length ? `${decodeWorkers.length} workers` : "main-thread"
    setStatus(`Decode · ${wlab} · ${capLabel}`)
  }
  showCaptureStatus()
  video.addEventListener("loadedmetadata", () => {
    captureSettings = { ...captureSettings, width: video.videoWidth, height: video.videoHeight }
    decodeDbg.video = `${video.videoWidth}x${video.videoHeight}`
    showCaptureStatus()
  }, { once: true })
  decodeLoop()
}

async function decodeLoop(){
  if(!decodeRunning || rxRecovered) return
  decodeFrameNo++
  const now = performance.now()
  if(decodeDbgLastT){
    const inst = 1000 / Math.max(1, now - decodeDbgLastT)
    decodeDbgFpsEma = decodeDbgFpsEma ? decodeDbgFpsEma * 0.85 + inst * 0.15 : inst
    decodeDbg.fps = decodeDbgFpsEma.toFixed(1)
  }
  decodeDbgLastT = now

  // Progress UI every few frames only
  decodeUiTick++
  if((decodeUiTick & 3) === 0){
    const need = rxK != null
      ? `${rxSymbols.size}/${rxN} · need ${rxK} · q${decodeQueue.length}`
      : `waiting · q${decodeQueue.length}`
    progressText.textContent = need
    if(rxFountain && rxK){
      const pct = Math.min(99, Math.floor((Math.min(rxSymbols.size, rxK) / rxK) * 100))
      progressBar.style.width = pct + "%"
    }
  }

  // Native detector occasionally (cheap on Safari) — don't block capture
  if(detector && (decodeFrameNo % 4) === 0){
    const nativeText = await scanNativeDetector()
    if(nativeText) handleDecodedText(nativeText, "BarcodeDetector")
    if(rxRecovered) return
  }

  // Capture into backlog; workers decode in parallel
  if(decodeWorkers.length){
    captureFrameToQueue()
  }else{
    const text = scanQrOnMainThread()
    if(text) handleDecodedText(text, decodeDbg.engine)
    else{
      qrHitStreak = 0
      qrMissStreak++
    }
    if(rxRecovered) return
  }

  // Miss accounting when workers are silent is approximate; bump on empty queue + no recent hit
  if(decodeWorkers.length && decodeQueue.length === 0 && decodeWorkersFree.length === decodeWorkers.length){
    if(qrHitStreak === 0) qrMissStreak++
  }

  if(video.requestVideoFrameCallback){
    video.requestVideoFrameCallback(() => decodeLoop())
  }else{
    requestAnimationFrame(() => decodeLoop())
  }
}

// Boot — keep the classic blue-on-black cloud (do not overwrite with washed particle RAF)
function bootQr(){
  try{
    showQrUi()
    if(typeof (globalThis.qrcode || window.qrcode) !== "function"){
      throw new Error("vendor/qrcode/qrcode.js did not expose window.qrcode")
    }
    window.__particlQrType = 0
    drawQrToCanvas(window.__particlIdlePayload || "PartiCl QR ready - Encode a file")
    ensureRs().catch((e) => console.warn("RS preload failed", e))
    setStatus("QR · Encode a file — or Decode with the camera.")
  }catch(err){
    console.error(err)
    setStatus(`Cloud failed: ${err.message || err}`)
    if(typeof window.__particlPaintCloud === "function"){
      window.__particlPaintCloud("PartiCl fallback")
    }
  }
}
if(document.readyState === "loading"){
  document.addEventListener("DOMContentLoaded", () => setTimeout(bootQr, 0))
}else{
  setTimeout(bootQr, 0)
}
