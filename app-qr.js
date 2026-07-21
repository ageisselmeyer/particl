/**
 * PartiCl QR transfer mode — MDS fountain (any k of n QRs recover).
 * Particle codec lives in app.js for later.
 */
import { rsEncode, rsDecodeErasures } from "./rs.js"

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
const MAX_SYMBOL_BYTES = 220
const FRAME_HOLD_MS = 1500
const QR_ECC = "Q"
const QR_CELL = 10
const QR_MARGIN = 8


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

/** Render QR into the visible <img> via GIF data-URL (no canvas required). */
function drawQrToCanvas(text){
  const qrcode = getQrCode()
  const qr = qrcode(0, QR_ECC)
  qr.addData(String(text), "Byte")
  qr.make()
  if(!qrImg) throw new Error("qrImg missing from DOM")
  qrImg.src = qr.createDataURL(QR_CELL, QR_MARGIN)
  qrImg.hidden = false
  qrImg.style.display = "block"
}

function showQrUi(){
  if(cloudCanvas) cloudCanvas.hidden = true
  if(qrImg) qrImg.hidden = false
  // Cyan corner marks sit on QR finders and break camera decode — keep them off.
  const align = document.getElementById("alignFrame")
  if(align) align.hidden = true
  canvasWrap.classList.add("tx-paper")
  canvasWrap.style.display = ""
  videoWrap.hidden = true
}

function planCoding(fileLen){
  let k = TARGET_K
  let n = TARGET_N
  let sym = Math.max(1, Math.ceil(fileLen / k))
  while(sym > MAX_SYMBOL_BYTES){
    k += 1
    n = k * 2
    sym = Math.max(1, Math.ceil(fileLen / k))
  }
  return { k, n, sym, nsym: n - k }
}

/** Per-byte-column RS: n packets, any k recover the k source blocks. */
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
    const includeMeta = pi === 0 || pi === order.length - 1
    const dataB64 = bytesToB64(packetData[seq])
    let payload
    if(includeMeta){
      payload = [
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
    }else{
      payload = [
        "PC7",
        fileId,
        String(k),
        String(n),
        String(seq),
        dataB64
      ].join("|")
    }
    out.push(payload)
  }
  out._fountain = { k, n, r: n - k, sym, total: n, need: k }
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
      const qrcode = getQrCode()
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
        `MDS QR · “${meta.name}” · ${frames.length} frames · ` +
        `need any ${ft.need} of ${ft.total} · point camera here`
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
    rxMeta = { name, type, size }
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
  downloadLink.href = url
  downloadLink.download = rxMeta.name || "recovered_file"
  downloadLink.hidden = false
  progressBar.style.width = "100%"
  progressText.textContent = "Done"
  setStatus(
    `Recovered “${downloadLink.download}” (${finalBytes.length} bytes) · ` +
    `${rxSymbols.size}/${rxN} QRs (need ${rxK})`
  )
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
  if(scanCanvas.width !== w || scanCanvas.height !== h){
    scanCanvas.width = w
    scanCanvas.height = h
  }
  return { sw: w, sh: h }
}

function tryJsQROnImageData(jsQR, img, w, h){
  const code = jsQR(img.data, w, h, { inversionAttempts: "attemptBoth" })
  return code && code.data ? code.data : null
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

  // jsQR: try a few scales / a center crop — dense QRs fail more often at one resolution
  const jsQR = getJsQR()
  if(jsQR){
    const w = video.videoWidth
    const h = video.videoHeight
    const attempts = [
      { max: 640, crop: 1 },
      { max: 960, crop: 1 },
      { max: 720, crop: 0.78 } // center square-ish crop
    ]
    // Rotate which attempt we try first so we don't always burn the same path
    const start = decodeFrameNo % attempts.length
    for(let n = 0; n < attempts.length; n++){
      const a = attempts[(start + n) % attempts.length]
      const scale = Math.min(1, a.max / Math.max(w, h))
      const cw = Math.max(1, (w * scale * a.crop) | 0)
      const ch = Math.max(1, (h * scale * a.crop) | 0)
      const sx = ((w - w * a.crop) / 2) | 0
      const sy = ((h - h * a.crop) / 2) | 0
      ensureScanCanvas(cw, ch)
      scanCtx.drawImage(video, sx, sy, w * a.crop, h * a.crop, 0, 0, cw, ch)
      const img = scanCtx.getImageData(0, 0, cw, ch)
      const data = tryJsQROnImageData(jsQR, img, cw, ch)
      if(data){
        decodeDbg.engine = `jsQR@${cw}`
        return data
      }
    }
  }

  decodeDbg.engine = detector ? "BarcodeDetector" : (getJsQR() ? "jsQR" : "none")
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

  const need = rxK != null
    ? `${rxSymbols.size}/${rxN} unique · need any ${rxK}`
    : "waiting for first QR"
  progressText.textContent = need
  if(rxFountain && rxK){
    const pct = Math.min(99, Math.floor((Math.min(rxSymbols.size, rxK) / rxK) * 100))
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
        setStatus(`MDS ${rxSymbols.size}/${rxN} · need any ${rxK} · misses OK`)
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

// Boot — wait a tick so classic vendor scripts definitely finished
function bootQr(){
  if(cloudCanvas) cloudCanvas.hidden = true
  canvasWrap.classList.add("tx-paper")
  try{
    if(typeof (globalThis.qrcode || window.qrcode) !== "function"){
      throw new Error("vendor/qrcode/qrcode.js did not expose window.qrcode")
    }
    drawQrToCanvas("PartiCl QR ready - Encode a file")
    setStatus("QR mode · Encode a file to stream QR frames — or Decode with the camera.")
  }catch(err){
    console.error(err)
    setStatus(`QR library failed: ${err.message || err}`)
    if(qrImg){
      // Visible failure pattern so the box is never blank white
      qrImg.src = "data:image/svg+xml," + encodeURIComponent(
        `<svg xmlns="http://www.w3.org/2000/svg" width="512" height="512">
          <rect width="100%" height="100%" fill="#fff"/>
          <rect x="32" y="32" width="448" height="448" fill="none" stroke="#000" stroke-width="16"/>
          <text x="256" y="250" text-anchor="middle" font-size="28" font-family="sans-serif">QR lib failed</text>
          <text x="256" y="290" text-anchor="middle" font-size="18" font-family="sans-serif">check console</text>
        </svg>`
      )
    }
  }
}
if(document.readyState === "loading"){
  document.addEventListener("DOMContentLoaded", () => setTimeout(bootQr, 0))
}else{
  setTimeout(bootQr, 0)
}
