import * as THREE from "three"
import { EffectComposer } from "three/addons/postprocessing/EffectComposer.js"
import { RenderPass } from "three/addons/postprocessing/RenderPass.js"
import { UnrealBloomPass } from "three/addons/postprocessing/UnrealBloomPass.js"

// --- DOM ---
const canvas = document.getElementById("cloud")
const canvasWrap = document.getElementById("canvasWrap")
const fileInput = document.getElementById("fileInput")
const modeButtons = document.getElementById("modeButtons")
const statusEl = document.getElementById("status")
const video = document.getElementById("video")
const videoWrap = document.getElementById("videoWrap")
const downloadLink = document.getElementById("download")
const progressWrap = document.getElementById("decodeProgressWrap")
const progressBar = document.getElementById("decodeProgressBar")
const progressText = document.getElementById("decodeProgressText")

document.getElementById("btnEncode").addEventListener("click", () => {
  fileInput.value = ""
  setStatus("Choose a file to encode into the particle cloud.")
  fileInput.click()
})
document.getElementById("btnDecode").addEventListener("click", () => startDecoder())
fileInput.addEventListener("change", () => {
  if(fileInput.files?.[0]) encodeFile(fileInput.files[0])
})

function setStatus(msg){
  statusEl.textContent = msg || ""
}

// --- Protocol ---
const PARTICLE_COUNT = 22000
const DATA_COUNT = 4096 // bits carried per frame (subset of particles)
const FRAME_HOLD_MS = 480
const FRAME_BLEND_MS = 220

const SYNC = "11001100111100001010101011001100" // 32-bit

function hash01(i, salt){
  let x = Math.imul(i ^ (salt * 0x9e3779b9), 0x85ebca6b) >>> 0
  x ^= x >>> 16
  x = Math.imul(x, 0xc2b2ae35) >>> 0
  x ^= x >>> 13
  return (x >>> 0) / 4294967296
}

// R2 (plastic-constant) Weyl sequence — simple, stable LDS in 2D
function r2(i){
  const g = 1.32471795724474602596
  const a1 = 1 / g
  const a2 = 1 / (g * g)
  const n = i + 1
  return [(0.5 + a1 * n) % 1, (0.5 + a2 * n) % 1]
}

function fibonacciSphere(n){
  // Uniform sphere coverage (golden spiral). Tiny R2 jitter breaks lattice look
  // without collapsing into a hemisphere the way a bad Sobol map did.
  const pts = new Float32Array(n * 3)
  const golden = Math.PI * (3 - Math.sqrt(5))
  for(let i = 0; i < n; i++){
    const y0 = 1 - (i / Math.max(1, n - 1)) * 2
    const r0 = Math.sqrt(Math.max(0, 1 - y0 * y0))
    const theta0 = golden * i
    const [ju, jv] = r2(i + 17)
    // Small tangential jitter (~0.8°) — stochastic, not stripy
    const jit = 0.014
    const y = Math.max(-1, Math.min(1, y0 + (ju - 0.5) * jit))
    const r = Math.sqrt(Math.max(0, 1 - y * y))
    const theta = theta0 + (jv - 0.5) * jit * 2
    pts[i * 3] = Math.cos(theta) * r
    pts[i * 3 + 1] = y
    pts[i * 3 + 2] = Math.sin(theta) * r
  }
  return pts
}

// Data carriers: hash-scrambled subset of all particles (no latitude bias)
const DATA_INDICES = (() => {
  const order = new Int32Array(PARTICLE_COUNT)
  for(let i = 0; i < PARTICLE_COUNT; i++) order[i] = i
  // Deterministic Fisher–Yates with hash PRNG
  for(let i = PARTICLE_COUNT - 1; i > 0; i--){
    const j = Math.floor(hash01(i, 42) * (i + 1))
    const t = order[i]; order[i] = order[j]; order[j] = t
  }
  return order.subarray(0, DATA_COUNT)
})()
const IS_DATA = (() => {
  const m = new Uint8Array(PARTICLE_COUNT)
  for(let i = 0; i < DATA_COUNT; i++) m[DATA_INDICES[i]] = 1
  return m
})()

let particleDirs = null // set in initCloud; used by decoder sampling

function bytesToBits(bytes){
  let s = ""
  for(let i = 0; i < bytes.length; i++){
    s += bytes[i].toString(2).padStart(8, "0")
  }
  return s
}

function bitsToBytes(bits){
  const n = (bits.length / 8) | 0
  const out = new Uint8Array(n)
  for(let i = 0; i < n; i++){
    out[i] = parseInt(bits.slice(i * 8, i * 8 + 8), 2) || 0
  }
  return out
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

function crc32(bytes){
  let c = 0xffffffff
  for(let i = 0; i < bytes.length; i++){
    c ^= bytes[i]
    for(let k = 0; k < 8; k++) c = (c >>> 1) ^ (0xedb88320 & -(c & 1))
  }
  return (c ^ 0xffffffff) >>> 0
}

// --- Cloud renderer ---
let renderer, scene, camera, points, uniforms, composer, bloomPass
let signalAttr, signalTarget
let cloudReady = false
let txRun = 0
let frames = []
let frameIndex = 0
let phaseStartedAt = 0
let animPhase = "hold" // hold | blend
let meta = null

const vertexShader = /* glsl */`
attribute float aPhase;
attribute float aRadius;
attribute float aSignal;
attribute float aFill;

uniform float uTime;
uniform float uSpin;

varying float vSignal;
varying float vFill;
varying float vDepth;
varying float vBright;

void main(){
  vSignal = aSignal;
  vFill = aFill;

  vec3 dir = normalize(position);
  float t = uTime;

  // Layered shell + swirl — readable particles, not a solid blob
  float shell = 0.72 + aRadius * 0.38;
  float n1 = sin(t * 0.55 + aPhase * 6.2831853 + dir.y * 2.5);
  float n2 = cos(t * 0.41 + aPhase * 5.2 + dir.x * 3.0);
  float n3 = sin(t * 0.29 + dir.x * 4.5 + dir.z * 3.8 + aPhase);
  float breathe = shell * (1.0 + n1 * 0.035 + n2 * 0.025);
  vec3 up = abs(dir.y) > 0.92 ? vec3(1.0, 0.0, 0.0) : vec3(0.0, 1.0, 0.0);
  vec3 tangential = normalize(cross(dir, up));
  vec3 bitangent = normalize(cross(dir, tangential));
  vec3 pos = dir * breathe
    + tangential * (n3 * 0.055)
    + bitangent * (n2 * 0.04);

  float cs = cos(uSpin), sn = sin(uSpin);
  pos = vec3(pos.x * cs - pos.z * sn, pos.y, pos.x * sn + pos.z * cs);

  vec4 mv = modelViewMatrix * vec4(pos, 1.0);
  vDepth = -mv.z;

  // Compact sparks — density from count, not giant discs
  float size = mix(2.2, 4.8, aSignal) * mix(0.65, 1.05, aFill);
  size *= mix(0.75, 1.15, aRadius);
  gl_PointSize = clamp(size * (220.0 / max(50.0, -mv.z)), 1.5, 9.0);

  // Front hemisphere a bit brighter (parallax / depth cue)
  vBright = 0.55 + 0.45 * smoothstep(-0.2, 0.85, -normalize((modelViewMatrix * vec4(dir, 0.0)).z));
  gl_Position = projectionMatrix * mv;
}
`

const fragmentShader = /* glsl */`
precision highp float;
varying float vSignal;
varying float vFill;
varying float vDepth;
varying float vBright;

void main(){
  vec2 uv = gl_PointCoord * 2.0 - 1.0;
  float d = dot(uv, uv);
  if(d > 1.0) discard;

  float core = exp(-d * 4.5);
  float halo = exp(-d * 1.8) * 0.35;
  float glow = core + halo;

  // Off bits nearly invisible; on bits read as cyan sparks
  float live = smoothstep(0.12, 0.55, vSignal);
  float alpha = glow * mix(0.04, 0.95, live) * mix(0.5, 1.0, vFill);

  vec3 cyan = vec3(0.25, 0.85, 1.0);
  vec3 blue = vec3(0.10, 0.40, 1.0);
  vec3 white = vec3(0.85, 0.95, 1.0);
  vec3 col = mix(blue, cyan, core);
  col = mix(col, white, core * live * 0.55);
  col *= vBright;

  float fog = smoothstep(5.8, 1.6, vDepth);
  alpha *= 0.35 + 0.65 * fog;
  col *= 0.65 + 0.35 * fog;

  gl_FragColor = vec4(col * (0.55 + 0.7 * live), alpha);
}
`

function initCloud(){
  const w = canvasWrap.clientWidth || 560
  const h = canvasWrap.clientHeight || 560
  canvas.width = w * devicePixelRatio
  canvas.height = h * devicePixelRatio

  renderer = new THREE.WebGLRenderer({
    canvas,
    antialias: false,
    alpha: false,
    powerPreference: "high-performance"
  })
  renderer.setPixelRatio(Math.min(2, devicePixelRatio))
  renderer.setSize(w, h, false)
  renderer.setClearColor(0x000000, 1)
  renderer.toneMapping = THREE.NoToneMapping

  scene = new THREE.Scene()
  camera = new THREE.PerspectiveCamera(38, w / h, 0.1, 100)
  camera.position.set(0, 0.08, 4.15)

  const dirs = fibonacciSphere(PARTICLE_COUNT)
  particleDirs = dirs
  const positions = new Float32Array(PARTICLE_COUNT * 3)
  const phase = new Float32Array(PARTICLE_COUNT)
  const radius = new Float32Array(PARTICLE_COUNT)
  const signal = new Float32Array(PARTICLE_COUNT)
  const fill = new Float32Array(PARTICLE_COUNT)
  signalTarget = new Float32Array(PARTICLE_COUNT)

  for(let i = 0; i < PARTICLE_COUNT; i++){
    positions[i * 3] = dirs[i * 3]
    positions[i * 3 + 1] = dirs[i * 3 + 1]
    positions[i * 3 + 2] = dirs[i * 3 + 2]
    const [u, v] = r2(i + 101)
    phase[i] = u
    radius[i] = Math.pow(v, 0.55)
    fill[i] = IS_DATA[i] ? 1 : 0.35 + hash01(i, 7) * 0.65
    signal[i] = IS_DATA[i] ? 0.1 : 0.08 + hash01(i, 8) * 0.2
    signalTarget[i] = signal[i]
  }

  const geo = new THREE.BufferGeometry()
  geo.setAttribute("position", new THREE.BufferAttribute(positions, 3))
  geo.setAttribute("aPhase", new THREE.BufferAttribute(phase, 1))
  geo.setAttribute("aRadius", new THREE.BufferAttribute(radius, 1))
  signalAttr = new THREE.BufferAttribute(signal, 1)
  signalAttr.setUsage(THREE.DynamicDrawUsage)
  geo.setAttribute("aSignal", signalAttr)
  geo.setAttribute("aFill", new THREE.BufferAttribute(fill, 1))

  uniforms = {
    uTime: { value: 0 },
    uSpin: { value: 0 }
  }

  const mat = new THREE.ShaderMaterial({
    vertexShader,
    fragmentShader,
    uniforms,
    transparent: true,
    depthWrite: false,
    blending: THREE.AdditiveBlending
  })

  points = new THREE.Points(geo, mat)
  scene.add(points)

  const renderPass = new RenderPass(scene, camera)
  // Soft glow without washing the sphere into a white disc
  bloomPass = new UnrealBloomPass(new THREE.Vector2(w, h), 0.72, 0.42, 0.28)
  composer = new EffectComposer(renderer)
  composer.addPass(renderPass)
  composer.addPass(bloomPass)

  cloudReady = true
  window.addEventListener("resize", onResize)
  requestAnimationFrame(renderLoop)
}

function onResize(){
  if(!renderer) return
  const w = canvasWrap.clientWidth || 560
  const h = canvasWrap.clientHeight || 560
  camera.aspect = w / h
  camera.updateProjectionMatrix()
  renderer.setSize(w, h, false)
  composer.setSize(w, h)
  bloomPass.resolution.set(w, h)
}

function setSignalBits(bitStr){
  // Decorative ambient first, then stamp data bits onto Sobol-scattered indices
  for(let i = 0; i < PARTICLE_COUNT; i++){
    if(IS_DATA[i]) continue
    const twinkle = 0.5 + 0.5 * Math.sin(hash01(i, 11) * 6.283 + performance.now() * 0.00045)
    signalTarget[i] = 0.05 + 0.16 * twinkle
  }
  for(let b = 0; b < DATA_COUNT; b++){
    const pi = DATA_INDICES[b]
    signalTarget[pi] = bitStr[b] === "1" ? 1 : 0.04
  }
}

function lerpSignals(dt){
  const arr = signalAttr.array
  const k = 1 - Math.exp(-dt * 7)
  for(let i = 0; i < PARTICLE_COUNT; i++){
    arr[i] += (signalTarget[i] - arr[i]) * k
  }
  signalAttr.needsUpdate = true
}

function renderLoop(now){
  requestAnimationFrame(renderLoop)
  if(!cloudReady) return
  const t = now * 0.001
  uniforms.uTime.value = t
  uniforms.uSpin.value = t * 0.18
  points.rotation.y = t * 0.12
  points.rotation.x = Math.sin(t * 0.15) * 0.08

  const dt = Math.min(0.05, (renderLoop._last ? (now - renderLoop._last) : 16) / 1000)
  renderLoop._last = now
  lerpSignals(dt)

  // TX frame machine
  if(frames.length && txRun){
    tickTx(now)
  }

  composer.render()
}

// --- Encode ---
function buildFrames(fileBytes, fileMeta){
  const fileId = (crypto.getRandomValues(new Uint32Array(1))[0] >>> 0).toString(36)
  const chunkSize = 180
  const total = Math.max(1, Math.ceil(fileBytes.length / chunkSize))
  const out = []

  for(let i = 0; i < total; i++){
    const start = i * chunkSize
    const chunk = fileBytes.slice(start, Math.min(fileBytes.length, start + chunkSize))
    const includeMeta = i === 0 || i % 5 === 0 || i === total - 1
    let payload
    if(includeMeta){
      payload = [
        "PC5M",
        fileId,
        String(i),
        String(total),
        String(fileMeta.size >>> 0),
        utf8ToB64(fileMeta.name || "file"),
        utf8ToB64(fileMeta.type || "application/octet-stream"),
        bytesToB64(chunk)
      ].join("|")
    }else{
      payload = ["PC5D", fileId, String(i), String(total), bytesToB64(chunk)].join("|")
    }
    const raw = new TextEncoder().encode(payload)
    const crc = crc32(raw)
    const body = new Uint8Array(raw.length + 4)
    body.set(raw, 0)
    body[raw.length] = (crc >>> 24) & 255
    body[raw.length + 1] = (crc >>> 16) & 255
    body[raw.length + 2] = (crc >>> 8) & 255
    body[raw.length + 3] = crc & 255

    let bits = SYNC + bytesToBits(body)
    if(bits.length < DATA_COUNT) bits = bits.padEnd(DATA_COUNT, "0")
    else bits = bits.slice(0, DATA_COUNT)
    out.push(bits)
  }
  return out
}

function encodeFile(file){
  const reader = new FileReader()
  reader.onload = () => {
    const bytes = new Uint8Array(reader.result)
    meta = {
      name: file.name || "recovered_file",
      type: file.type || "application/octet-stream",
      size: bytes.length
    }
    frames = buildFrames(bytes, meta)
    frameIndex = 0
    animPhase = "hold"
    phaseStartedAt = 0
    txRun++
    modeButtons.style.display = "none"
    videoWrap.hidden = true
    canvasWrap.style.display = ""
    setSignalBits(frames[0])
    setStatus(`Streaming “${meta.name}” · ${frames.length} cloud frames · point another device’s camera here`)
  }
  reader.readAsArrayBuffer(file)
}

function tickTx(now){
  if(!phaseStartedAt) phaseStartedAt = now
  let elapsed = now - phaseStartedAt
  const dur = animPhase === "hold" ? FRAME_HOLD_MS : FRAME_BLEND_MS
  while(elapsed >= dur){
    elapsed -= dur
    phaseStartedAt += dur
    if(animPhase === "hold"){
      animPhase = "blend"
      const next = frames[(frameIndex + 1) % frames.length]
      setSignalBits(next)
    }else{
      frameIndex = (frameIndex + 1) % frames.length
      animPhase = "hold"
      setSignalBits(frames[frameIndex])
    }
  }
  if((tickTx._lastStatus | 0) !== frameIndex){
    tickTx._lastStatus = frameIndex
    setStatus(`Cloud frame ${frameIndex + 1} / ${frames.length} · “${meta?.name || "file"}”`)
  }
}

// --- Decode (camera + BarcodeDetector fallback via payload reassembly from sampled bits) ---
let rxChunks = new Map()
let rxHave = new Set()
let rxTotal = null
let rxFileId = null
let rxMeta = null
let decodeRunning = false
let detector = null

function ingestPayloadText(text){
  if(!text || typeof text !== "string") return false
  if(!(text.startsWith("PC5M|") || text.startsWith("PC5D|"))) return false
  const parts = text.split("|")
  if(parts[0] === "PC5M"){
    if(parts.length < 8) return false
    const fileId = parts[1]
    const idx = parseInt(parts[2], 10)
    const total = parseInt(parts[3], 10)
    const size = parseInt(parts[4], 10)
    const name = b64ToUtf8(parts[5])
    const type = b64ToUtf8(parts[6])
    const chunk = b64ToBytes(parts.slice(7).join("|"))
    if(!Number.isFinite(idx) || !Number.isFinite(total) || total < 1) return false
    if(rxFileId == null) rxFileId = fileId
    if(fileId !== rxFileId) return false
    rxTotal = total
    rxMeta = { name, type, size }
    if(!rxHave.has(idx)){
      rxChunks.set(idx, chunk)
      rxHave.add(idx)
    }
    return true
  }
  if(parts[0] === "PC5D"){
    if(parts.length < 5) return false
    const fileId = parts[1]
    const idx = parseInt(parts[2], 10)
    const total = parseInt(parts[3], 10)
    const chunk = b64ToBytes(parts.slice(4).join("|"))
    if(!Number.isFinite(idx) || !Number.isFinite(total) || total < 1) return false
    if(rxFileId == null) rxFileId = fileId
    if(fileId !== rxFileId) return false
    rxTotal = total
    if(!rxHave.has(idx)){
      rxChunks.set(idx, chunk)
      rxHave.add(idx)
    }
    return true
  }
  return false
}

function tryFinish(){
  if(rxTotal == null || rxHave.size < rxTotal) return false
  if(!rxMeta) rxMeta = { name: "recovered_file", type: "application/octet-stream", size: null }
  const parts = []
  let len = 0
  for(let i = 0; i < rxTotal; i++){
    const c = rxChunks.get(i)
    if(!c) return false
    parts.push(c)
    len += c.length
  }
  const merged = new Uint8Array(len)
  let off = 0
  for(const p of parts){ merged.set(p, off); off += p.length }
  const finalBytes = rxMeta.size != null ? merged.slice(0, rxMeta.size) : merged
  const blob = new Blob([finalBytes], { type: rxMeta.type || "application/octet-stream" })
  const url = URL.createObjectURL(blob)
  downloadLink.href = url
  downloadLink.download = rxMeta.name || "recovered_file"
  downloadLink.hidden = false
  progressBar.style.width = "100%"
  progressText.textContent = "Done"
  setStatus(`Recovered “${downloadLink.download}” (${finalBytes.length} bytes).`)
  try{ downloadLink.click() }catch(_){}
  decodeRunning = false
  return true
}

function bitsToPayload(bits){
  if(!bits || bits.length < SYNC.length + 16) return null
  // Find sync
  let start = -1
  for(let i = 0; i <= bits.length - SYNC.length; i++){
    let ok = 0
    for(let j = 0; j < SYNC.length; j++) if(bits[i + j] === SYNC[j]) ok++
    if(ok >= 28){ start = i; break }
  }
  if(start < 0) return null
  const bodyBits = bits.slice(start + SYNC.length)
  const body = bitsToBytes(bodyBits)
  if(body.length < 5) return null
  const raw = body.subarray(0, body.length - 4)
  const crc =
    ((body[body.length - 4] << 24) |
      (body[body.length - 3] << 16) |
      (body[body.length - 2] << 8) |
      body[body.length - 1]) >>> 0
  if(crc32(raw) !== crc) return null
  try{
    return new TextDecoder().decode(raw)
  }catch(_){
    return null
  }
}

function sampleCloudBitsFromVideo(){
  // Orthographic-ish sample of fibonacci directions projected to a disk in frame center.
  const vw = video.videoWidth, vh = video.videoHeight
  if(!vw || !vh) return null
  const side = Math.min(vw, vh)
  const sx = ((vw - side) / 2) | 0
  const sy = ((vh - side) / 2) | 0
  const scan = sampleCloudBitsFromVideo._c || (sampleCloudBitsFromVideo._c = document.createElement("canvas"))
  const S = 256
  scan.width = S
  scan.height = S
  const c = scan.getContext("2d", { willReadFrequently: true })
  c.drawImage(video, sx, sy, side, side, 0, 0, S, S)
  const img = c.getImageData(0, 0, S, S)
  const data = img.data

  // Collect blue-ish luminance samples for data particles
  const vals = new Float32Array(DATA_COUNT)
  if(!particleDirs) return null
  for(let b = 0; b < DATA_COUNT; b++){
    const i = DATA_INDICES[b]
    const x = particleDirs[i * 3]
    const y = particleDirs[i * 3 + 1]
    const z = particleDirs[i * 3 + 2]
    const depth = z + 1.4
    const px = (x / depth) * 0.92
    const py = (y / depth) * 0.92
    const ix = ((px * 0.5 + 0.5) * (S - 1)) | 0
    const iy = ((-py * 0.5 + 0.5) * (S - 1)) | 0
    if(ix < 1 || iy < 1 || ix >= S - 1 || iy >= S - 1){
      vals[b] = 0
      continue
    }
    let acc = 0, n = 0
    for(let dy = -1; dy <= 1; dy++){
      for(let dx = -1; dx <= 1; dx++){
        const p = ((iy + dy) * S + (ix + dx)) * 4
        const bb = data[p + 2], g = data[p + 1], r8 = data[p]
        acc += bb * 0.55 + g * 0.3 + r8 * 0.15
        n++
      }
    }
    vals[b] = acc / n
  }

  // Adaptive threshold
  let sum = 0
  for(let i = 0; i < DATA_COUNT; i++) sum += vals[i]
  const mean = sum / DATA_COUNT
  let varSum = 0
  for(let i = 0; i < DATA_COUNT; i++){
    const d = vals[i] - mean
    varSum += d * d
  }
  const std = Math.sqrt(varSum / DATA_COUNT)
  const thr = mean + std * 0.15
  let bits = ""
  for(let i = 0; i < DATA_COUNT; i++) bits += vals[i] > thr ? "1" : "0"
  return bits
}

async function startDecoder(){
  txRun = 0
  frames = []
  modeButtons.style.display = "none"
  canvasWrap.style.display = "none"
  videoWrap.hidden = false
  progressWrap.hidden = false
  downloadLink.hidden = true
  rxChunks = new Map()
  rxHave = new Set()
  rxTotal = null
  rxFileId = null
  rxMeta = null
  progressBar.style.width = "0%"
  progressText.textContent = "Frames: 0"

  try{
    const stream = await navigator.mediaDevices.getUserMedia({
      video: { facingMode: { ideal: "environment" }, width: { ideal: 1920 }, height: { ideal: 1080 } }
    })
    video.srcObject = stream
  }catch(_){
    setStatus("Could not access camera.")
    return
  }

  if("BarcodeDetector" in window){
    try{ detector = new BarcodeDetector({ formats: ["qr_code"] }) }catch(_){ detector = null }
  }

  decodeRunning = true
  setStatus("Point the camera at the glowing particle cloud. Keep it centered and steady.")
  decodeLoop()
}

async function decodeLoop(){
  if(!decodeRunning) return
  const have = rxHave.size
  const need = rxTotal || "?"
  progressText.textContent = `Frames decoded: ${have} / ${need}`
  if(rxTotal) progressBar.style.width = Math.min(100, Math.floor((have / rxTotal) * 100)) + "%"

  // Primary: sample cloud bits
  if(video.videoWidth){
    const bits = sampleCloudBitsFromVideo()
    if(bits){
      const text = bitsToPayload(bits)
      if(text && ingestPayloadText(text)){
        setStatus(`Locked cloud signal · ${rxHave.size}${rxTotal ? " / " + rxTotal : ""} frames`)
        if(tryFinish()) return
      }
    }
  }

  // Optional: if a QR ever appears in view, accept PC5 payloads too
  if(detector && video.videoWidth){
    try{
      const codes = await detector.detect(video)
      for(const c of codes){
        if(ingestPayloadText(c.rawValue)){
          if(tryFinish()) return
        }
      }
    }catch(_){}
  }

  if(video.requestVideoFrameCallback){
    video.requestVideoFrameCallback(() => decodeLoop())
  }else{
    requestAnimationFrame(() => decodeLoop())
  }
}

// Idle demo cloud before encode — spatial hash noise, no latitude bands
function idleDemoBits(){
  let bits = ""
  const t = performance.now() * 0.001
  for(let b = 0; b < DATA_COUNT; b++){
    const i = DATA_INDICES[b]
    const x = particleDirs ? particleDirs[i * 3] : 0
    const y = particleDirs ? particleDirs[i * 3 + 1] : 0
    const z = particleDirs ? particleDirs[i * 3 + 2] : 0
    // 3D value noise-ish from hashes — isotropic, no Y stripes
    const n1 = Math.sin((x * 7.1 + z * 5.3) * 3.1 + t * 1.2 + hash01(i, 3) * 6.28)
    const n2 = Math.cos((y * 6.4 + x * 4.7) * 2.7 - t * 0.9 + hash01(i, 4) * 6.28)
    const n3 = Math.sin((z * 5.9 + y * 3.8 + t * 0.55) * 2.2 + hash01(i, 5) * 6.28)
    const v = n1 * 0.45 + n2 * 0.35 + n3 * 0.3
    bits += v > 0.12 ? "1" : "0"
  }
  return bits
}

initCloud()
setSignalBits(idleDemoBits())
setInterval(() => {
  if(!frames.length) setSignalBits(idleDemoBits())
}, 400)
setStatus("Encode a file to stream it as a glowing particle cloud — or decode with the camera.")
