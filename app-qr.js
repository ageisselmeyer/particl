/**
 * PartiCl QR transfer mode — same UI + fountain packets, real QR encode/decode.
 * Particle codec lives in app.js for later; this path is for reliable E2E success.
 */
const canvasWrap = document.getElementById("canvasWrap")
const cloudCanvas = document.getElementById("cloud")
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

// Larger symbols than the particle path — QR carries more payload per frame.
const SYMBOL_SIZE = 96
const FRAME_HOLD_MS = 1400
const FOUNTAIN_SOURCE_COPIES = 2
const FOUNTAIN_REPAIR_BASE = 0.4
const QR_ECC = "M" // L/M/Q/H — M is a good phone default
const QR_PIXEL = 1024

let frames = [] // string payloads
let frameIndex = 0
let phaseStartedAt = 0
let txRun = 0
let meta = null
let txRaf = 0

function fountainRng(seed){
  let s = seed >>> 0
  return () => {
    s = (Math.imul(s, 1664525) + 1013904223) >>> 0
    return s / 4294967296
  }
}

function pickLtDegree(k, rnd){
  const u = rnd()
  if(u < 1 / k) return 1
  let d = 2
  let cum = 1 / k
  while(d < k){
    cum += 1 / (d * (d - 1))
    if(u < cum) return d
    d++
  }
  return Math.min(k, 2 + ((rnd() * Math.min(k, 8)) | 0))
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
        let ok = true
        for(let i = 0; i < eq.data.length; i++) if(eq.data[i]){ ok = false; break }
        if(!ok) return null
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
  for(let i = 0; i < k; i++) if(!known[i]) return null
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

function requireQrLib(){
  if(typeof qrcode !== "function"){
    throw new Error("qrcode-generator not loaded")
  }
}

function drawQrToCanvas(text){
  requireQrLib()
  const qr = qrcode(0, QR_ECC)
  qr.addData(text, "Byte")
  qr.make()
  const n = qr.getModuleCount()
  const canvas = qrCanvas
  canvas.width = QR_PIXEL
  canvas.height = QR_PIXEL
  const ctx = canvas.getContext("2d")
  const margin = Math.floor(QR_PIXEL * 0.08)
  const cell = (QR_PIXEL - margin * 2) / n
  ctx.fillStyle = "#ffffff"
  ctx.fillRect(0, 0, QR_PIXEL, QR_PIXEL)
  ctx.fillStyle = "#000000"
  for(let r = 0; r < n; r++){
    for(let c = 0; c < n; c++){
      if(qr.isDark(r, c)){
        const x = margin + c * cell
        const y = margin + r * cell
        ctx.fillRect(x, y, cell + 0.6, cell + 0.6)
      }
    }
  }
}

function showQrUi(){
  if(cloudCanvas) cloudCanvas.hidden = true
  qrCanvas.hidden = false
  canvasWrap.classList.add("tx-paper")
  canvasWrap.style.display = ""
  videoWrap.hidden = true
}

function buildFrames(fileBytes, fileMeta){
  const fileId = (crypto.getRandomValues(new Uint32Array(1))[0] >>> 0).toString(36)
  const k = Math.max(1, Math.ceil(fileBytes.length / SYMBOL_SIZE))
  const padded = new Uint8Array(k * SYMBOL_SIZE)
  padded.set(fileBytes)
  const sources = []
  for(let i = 0; i < k; i++){
    sources.push(padded.subarray(i * SYMBOL_SIZE, (i + 1) * SYMBOL_SIZE))
  }
  const r = Math.max(3, Math.ceil(k * FOUNTAIN_REPAIR_BASE))

  const packets = []
  for(let copy = 0; copy < FOUNTAIN_SOURCE_COPIES; copy++){
    for(let i = 0; i < k; i++){
      packets.push({ seq: i, seed: 0, data: sources[i].slice() })
    }
  }
  for(let j = 0; j < r; j++){
    const seed = fileIdSeed(fileId, j)
    const indices = ltIndices(k, seed)
    const data = new Uint8Array(SYMBOL_SIZE)
    for(const idx of indices) xorBytes(data, sources[idx])
    packets.push({ seq: k + j, seed, data })
  }
  for(let i = packets.length - 1; i > 0; i--){
    const j = Math.floor(hash01(i, 91) * (i + 1))
    const t = packets[i]; packets[i] = packets[j]; packets[j] = t
  }

  const out = []
  for(let pi = 0; pi < packets.length; pi++){
    const p = packets[pi]
    const includeMeta = pi === 0 || pi % 6 === 0 || pi === packets.length - 1
    let payload
    if(includeMeta){
      payload = [
        "PC6M",
        fileId,
        String(k),
        String(r),
        String(fileMeta.size >>> 0),
        utf8ToB64(fileMeta.name || "file"),
        utf8ToB64(fileMeta.type || "application/octet-stream"),
        String(p.seq),
        String(p.seed >>> 0),
        bytesToB64(p.data)
      ].join("|")
    }else{
      payload = [
        "PC6",
        fileId,
        String(k),
        String(r),
        String(p.seq),
        String(p.seed >>> 0),
        bytesToB64(p.data)
      ].join("|")
    }
    out.push(payload)
  }
  out._fountain = { k, r, copies: FOUNTAIN_SOURCE_COPIES, total: packets.length }
  return out
}

function encodeFile(file){
  const reader = new FileReader()
  reader.onload = () => {
    try{
      const bytes = new Uint8Array(reader.result)
      meta = {
        name: file.name || "recovered_file",
        type: file.type || "application/octet-stream",
        size: bytes.length
      }
      frames = buildFrames(bytes, meta)
      // Sanity: ensure QR can encode the longest packet
      requireQrLib()
      const longest = frames.reduce((a, b) => (a.length >= b.length ? a : b), "")
      const probe = qrcode(0, QR_ECC)
      probe.addData(longest, "Byte")
      probe.make()

      frameIndex = 0
      phaseStartedAt = 0
      txRun++
      modeButtons.style.display = "none"
      showQrUi()
      drawQrToCanvas(frames[0])
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
        `QR mode · “${meta.name}” · ${frames.length} frames (k=${ft.k}) · point camera here`
      )
    }catch(err){
      console.error(err)
      setStatus(`Encode failed: ${err.message || err}`)
      modeButtons.style.display = ""
    }
  }
  reader.readAsArrayBuffer(file)
}

function tickTx(now){
  if(!frames.length) return
  if(!phaseStartedAt) phaseStartedAt = now
  let elapsed = now - phaseStartedAt
  while(elapsed >= FRAME_HOLD_MS){
    elapsed -= FRAME_HOLD_MS
    phaseStartedAt += FRAME_HOLD_MS
    frameIndex = (frameIndex + 1) % frames.length
    drawQrToCanvas(frames[frameIndex])
  }
  if((tickTx._lastStatus | 0) !== frameIndex){
    tickTx._lastStatus = frameIndex
    setStatus(`QR frame ${frameIndex + 1} / ${frames.length} · “${meta?.name || "file"}”`)
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
let rxR = null
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
    crcScore = rxRecovered ? 100 : Math.min(95, Math.round((rxSymbols.size / Math.max(1, rxK || 1)) * 95))
    crcLabel = rxRecovered ? "recovered" : `${rxSymbols.size}/${rxK || "?"} symbols`
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
    `fountain ok=${rxDecodeCount} unique=${rxSymbols.size} sources=${countUniqueSources()}/${rxK ?? "?"}`,
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
  rxR = null
  rxSymbols = new Map()
  rxDecodeCount = 0
  rxPayloadOk = false
  rxRecovered = false
  lastQrText = ""
  qrHitStreak = 0
  qrMissStreak = 0
}

function ingestFountainSymbol(fileId, k, r, seq, seed, data){
  if(!Number.isFinite(k) || !Number.isFinite(r) || k < 1 || r < 0) return false
  if(!Number.isFinite(seq) || seq < 0 || seq >= k + r) return false
  if(rxFileId == null) rxFileId = fileId
  if(fileId !== rxFileId) return false
  rxFountain = true
  rxK = k
  rxR = r
  rxTotal = k
  rxDecodeCount++
  if(rxSymbols.has(seq)) return true
  const sym = new Uint8Array(SYMBOL_SIZE)
  sym.set(data.subarray(0, Math.min(SYMBOL_SIZE, data.length)))
  const indices = seq < k ? [seq] : ltIndices(k, seed >>> 0)
  rxSymbols.set(seq, { data: sym, seed: seed >>> 0, indices })
  rxHave.add(seq)
  return true
}

function ingestPayloadText(text){
  if(!text || typeof text !== "string") return false
  if(text.startsWith("PC6M|")){
    const parts = text.split("|")
    if(parts.length < 10) return false
    const fileId = parts[1]
    const k = parseInt(parts[2], 10)
    const r = parseInt(parts[3], 10)
    const size = parseInt(parts[4], 10)
    const name = b64ToUtf8(parts[5])
    const type = b64ToUtf8(parts[6])
    const seq = parseInt(parts[7], 10)
    const seed = parseInt(parts[8], 10)
    const data = b64ToBytes(parts.slice(9).join("|"))
    if(!ingestFountainSymbol(fileId, k, r, seq, seed, data)) return false
    rxMeta = { name, type, size }
    return true
  }
  if(text.startsWith("PC6|")){
    const parts = text.split("|")
    if(parts.length < 7) return false
    const fileId = parts[1]
    const k = parseInt(parts[2], 10)
    const r = parseInt(parts[3], 10)
    const seq = parseInt(parts[4], 10)
    const seed = parseInt(parts[5], 10)
    const data = b64ToBytes(parts.slice(6).join("|"))
    return ingestFountainSymbol(fileId, k, r, seq, seed, data)
  }
  return false
}

function countUniqueSources(){
  if(rxK == null) return 0
  let n = 0
  for(let i = 0; i < rxK; i++) if(rxSymbols.has(i)) n++
  return n
}

function fountainDecodeReady(){
  if(!rxFountain || rxK == null) return false
  if(countUniqueSources() >= rxK) return true
  const sent = rxK * FOUNTAIN_SOURCE_COPIES + (rxR || 0)
  if(rxDecodeCount < Math.ceil(sent * 0.75)) return false
  return rxSymbols.size >= rxK
}

function tryFinishFountain(){
  if(!fountainDecodeReady()) return false
  const k = rxK
  let sources = null
  let haveAllDirect = true
  const direct = new Array(k)
  for(let i = 0; i < k; i++){
    const s = rxSymbols.get(i)
    if(s) direct[i] = s.data
    else haveAllDirect = false
  }
  if(haveAllDirect) sources = direct
  else{
    sources = ltDecodePeel(k, rxSymbols)
    if(!sources) return false
  }
  if(!rxMeta) rxMeta = { name: "recovered_file", type: "application/octet-stream", size: null }
  const merged = new Uint8Array(rxK * SYMBOL_SIZE)
  for(let i = 0; i < rxK; i++) merged.set(sources[i], i * SYMBOL_SIZE)
  const finalBytes = rxMeta.size != null ? merged.slice(0, rxMeta.size) : merged
  const blob = new Blob([finalBytes], { type: rxMeta.type || "application/octet-stream" })
  const url = URL.createObjectURL(blob)
  downloadLink.href = url
  downloadLink.download = rxMeta.name || "recovered_file"
  downloadLink.hidden = false
  progressBar.style.width = "100%"
  progressText.textContent = "Done"
  setStatus(`Recovered “${downloadLink.download}” (${finalBytes.length} bytes) · ${rxDecodeCount} QR hits.`)
  try{ downloadLink.click() }catch(_){}
  rxRecovered = true
  updateDecodeMeters()
  decodeRunning = false
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
  // Downscale for jsQR speed on phone
  const maxW = 720
  const scale = Math.min(1, maxW / w)
  const sw = Math.max(1, (w * scale) | 0)
  const sh = Math.max(1, (h * scale) | 0)
  if(scanCanvas.width !== sw || scanCanvas.height !== sh){
    scanCanvas.width = sw
    scanCanvas.height = sh
  }
  return { sw, sh }
}

async function scanQrFromVideo(){
  if(!video.videoWidth) return null

  // Prefer native detector (Safari / Chromium)
  if(detector){
    try{
      const codes = await detector.detect(video)
      if(codes && codes.length){
        decodeDbg.engine = "BarcodeDetector"
        return codes[0].rawValue || null
      }
    }catch(_){}
  }

  // jsQR fallback
  if(typeof jsQR === "function"){
    const w = video.videoWidth
    const h = video.videoHeight
    const { sw, sh } = ensureScanCanvas(w, h)
    scanCtx.drawImage(video, 0, 0, sw, sh)
    const img = scanCtx.getImageData(0, 0, sw, sh)
    const code = jsQR(img.data, sw, sh, { inversionAttempts: "attemptBoth" })
    if(code && code.data){
      decodeDbg.engine = "jsQR"
      return code.data
    }
  }

  decodeDbg.engine = detector ? "BarcodeDetector" : (typeof jsQR === "function" ? "jsQR" : "none")
  return null
}

async function startDecoder(){
  txRun = 0
  frames = []
  if(txRaf) cancelAnimationFrame(txRaf)
  modeButtons.style.display = "none"
  canvasWrap.style.display = "none"
  videoWrap.hidden = false
  progressWrap.hidden = false
  downloadLink.hidden = true
  resetRxState()
  resetDecodeQuality()
  decodeFrameNo = 0
  progressBar.style.width = "0%"
  progressText.textContent = "QR: 0"
  if(decodeMetersEl) decodeMetersEl.hidden = false
  if(decodeDebugEl){
    decodeDebugEl.hidden = false
    decodeDbg.last = "decoder started"
    updateDecodeDebug()
  }
  updateDecodeMeters()

  let captureSettings = {}
  try{
    const stream = await navigator.mediaDevices.getUserMedia({
      video: {
        facingMode: { ideal: "environment" },
        width: { ideal: 1920, min: 1280 },
        height: { ideal: 1080, min: 720 },
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
    setStatus(`Point at the QR on the Mac · fill the view · ${capLabel}.`)
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
  if(!decodeRunning) return
  decodeFrameNo++
  const now = performance.now()
  if(decodeDbgLastT){
    const inst = 1000 / Math.max(1, now - decodeDbgLastT)
    decodeDbgFpsEma = decodeDbgFpsEma ? decodeDbgFpsEma * 0.85 + inst * 0.15 : inst
    decodeDbg.fps = decodeDbgFpsEma.toFixed(1)
  }
  decodeDbgLastT = now
  if(video.videoWidth) decodeDbg.video = `${video.videoWidth}x${video.videoHeight}`

  const need = rxK != null ? `${countUniqueSources()}/${rxK} sources` : "?"
  progressText.textContent = `QR hits: ${rxDecodeCount} · ${need}`
  if(rxFountain && rxK){
    const sent = rxK * FOUNTAIN_SOURCE_COPIES + (rxR || 0)
    const pct = Math.min(100, Math.floor((rxDecodeCount / Math.ceil(sent * 0.8)) * 100))
    progressBar.style.width = pct + "%"
  }

  const text = await scanQrFromVideo()
  if(text){
    qrHitStreak++
    qrMissStreak = 0
    decodeDbg.hits++
    decodeDbg.last = text.slice(0, 48) + (text.length > 48 ? "…" : "")
    if(text !== lastQrText){
      lastQrText = text
      if(ingestPayloadText(text)){
        rxPayloadOk = true
        setStatus(`QR locked · ${rxSymbols.size} symbols · peeling…`)
        if(tryFinish()) return
      }else{
        decodeDbg.last = `ignored: ${text.slice(0, 40)}`
      }
    }else if(rxFountain && rxSymbols.size >= (rxK || 0)){
      if(tryFinish()) return
    }
  }else{
    qrHitStreak = 0
    qrMissStreak++
    if(qrMissStreak % 30 === 0) decodeDbg.last = "no QR in view"
  }

  updateDecodeMeters()
  updateDecodeDebug()

  if(video.requestVideoFrameCallback){
    video.requestVideoFrameCallback(() => decodeLoop())
  }else{
    requestAnimationFrame(() => decodeLoop())
  }
}

// Boot
if(cloudCanvas) cloudCanvas.hidden = true
qrCanvas.hidden = false
canvasWrap.classList.add("tx-paper")
try{
  drawQrToCanvas("PartiCl QR ready — Encode a file")
}catch(_){
  // libs may still be loading if scripts deferred oddly
}
setStatus("QR mode · Encode a file to stream QR frames — or Decode with the camera.")
