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
const lockQuadEl = document.getElementById("lockQuad")
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
const BIT_REPS = 3 // each logical bit painted on 3 front particles (majority vote)
const DATA_COUNT = 2048 // logical bits per frame
const PHYS_COUNT = DATA_COUNT * BIT_REPS
const FRAME_HOLD_MS = 1100
const FRAME_BLEND_MS = 0
const SYMBOL_SIZE = 64

// Corner brackets on TX match these normalized positions (center of L-mark).
const ALIGN_MARKER_UV = 0.075
const SAMPLE_INSET = 0.11

const SYNC = "11001100111100001010101011001100" // 32-bit

// Fountain (LT-style): k source symbols + repair → recover from ~80% of sent frames.
const FOUNTAIN_SOURCE_COPIES = 2
const FOUNTAIN_REPAIR_BASE = 0.4

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

const PARTICLE_DIRS = fibonacciSphere(PARTICLE_COUNT)
let particleDirs = PARTICLE_DIRS

// Data on camera-facing particles only (z toward +Z). Back-hemisphere bits are invisible.
// Groups of BIT_REPS particles share one logical bit (majority vote on decode).
const DATA_INDICES = (() => {
  const front = []
  for(let i = 0; i < PARTICLE_COUNT; i++){
    if(PARTICLE_DIRS[i * 3 + 2] > 0.18) front.push(i)
  }
  for(let i = front.length - 1; i > 0; i--){
    const j = Math.floor(hash01(i, 42) * (i + 1))
    const t = front[i]; front[i] = front[j]; front[j] = t
  }
  if(front.length < PHYS_COUNT){
    throw new Error(`Need ${PHYS_COUNT} front particles, got ${front.length}`)
  }
  return Int32Array.from(front.slice(0, PHYS_COUNT))
})()
const IS_DATA = (() => {
  const m = new Uint8Array(PARTICLE_COUNT)
  for(let i = 0; i < PHYS_COUNT; i++) m[DATA_INDICES[i]] = 1
  return m
})()

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

const CAMERA_BASE = { x: 0, y: 0.08, z: 4.15 }

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

  float r = sqrt(d);
  // Orb sprite: white hot core → cyan → soft transparent edge
  float core = exp(-d * 5.5);
  float mid = exp(-d * 2.2);
  float edge = smoothstep(1.0, 0.35, r);

  vec3 cWhite = vec3(1.0, 1.0, 1.0);
  vec3 cCyan  = vec3(0.659, 0.953, 1.0);   // #A8F3FF
  vec3 cBlue  = vec3(0.082, 0.486, 1.0);   // #157CFF

  vec3 col = mix(cBlue, cCyan, smoothstep(0.15, 0.72, 1.0 - r));
  col = mix(col, cWhite, core * 0.92 + mid * 0.08);

  float live = smoothstep(0.12, 0.55, vSignal);
  float alpha = edge * (core * 0.85 + mid * 0.45);
  alpha *= mix(0.05, 1.0, live) * mix(0.45, 1.0, vFill);

  col *= vBright * (0.7 + 0.55 * live);
  float fog = smoothstep(5.8, 1.6, vDepth);
  alpha *= 0.35 + 0.65 * fog;
  col *= 0.68 + 0.32 * fog;

  gl_FragColor = vec4(col * (0.65 + 0.75 * live), alpha);
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
  camera.position.set(CAMERA_BASE.x, CAMERA_BASE.y, CAMERA_BASE.z)

  const dirs = PARTICLE_DIRS
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
  // Stronger bloom on bright cores only (high threshold avoids full-sphere washout)
  bloomPass = new UnrealBloomPass(new THREE.Vector2(w, h), 1.12, 0.48, 0.52)
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

function setSignalBits(bitStr, snap){
  // Decorative ambient first, then stamp data bits onto front carriers.
  for(let i = 0; i < PARTICLE_COUNT; i++){
    if(IS_DATA[i]) continue
    const twinkle = 0.5 + 0.5 * Math.sin(hash01(i, 11) * 6.283 + performance.now() * 0.00045)
    signalTarget[i] = txRun ? 0.02 : (0.05 + 0.16 * twinkle)
  }
  for(let b = 0; b < DATA_COUNT; b++){
    const on = bitStr[b] === "1" ? 1 : 0.0
    const base = b * BIT_REPS
    for(let r = 0; r < BIT_REPS; r++){
      signalTarget[DATA_INDICES[base + r]] = on
    }
  }
  if(snap && signalAttr){
    const arr = signalAttr.array
    for(let i = 0; i < PARTICLE_COUNT; i++) arr[i] = signalTarget[i]
    signalAttr.needsUpdate = true
  }
}

function lerpSignals(dt){
  // During TX hold, keep bits hard — no soft blend that mixes frames optically.
  if(txRun && frames.length && animPhase === "hold"){
    const arr = signalAttr.array
    let dirty = false
    for(let i = 0; i < PARTICLE_COUNT; i++){
      if(arr[i] !== signalTarget[i]){ arr[i] = signalTarget[i]; dirty = true }
    }
    if(dirty) signalAttr.needsUpdate = true
    return
  }
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
  const encoding = !!(frames.length && txRun)
  const t = now * 0.001
  // Freeze pose during encode so decoder's static projection can match.
  if(encoding){
    uniforms.uTime.value = 0
    uniforms.uSpin.value = 0
    points.rotation.set(0, 0, 0)
    camera.position.set(CAMERA_BASE.x, CAMERA_BASE.y, CAMERA_BASE.z)
    if(bloomPass){
      bloomPass.strength = 0.55
      bloomPass.threshold = 0.62
    }
  }else{
    uniforms.uTime.value = t
    uniforms.uSpin.value = t * 0.18
    points.rotation.y = t * 0.12
    points.rotation.x = Math.sin(t * 0.15) * 0.08
    camera.position.x = CAMERA_BASE.x + Math.sin(t * 0.15) * 0.12
    camera.position.y = CAMERA_BASE.y + Math.cos(t * 0.18) * 0.08
    camera.position.z = CAMERA_BASE.z
    if(bloomPass){
      bloomPass.strength = 1.12
      bloomPass.threshold = 0.52
    }
  }
  camera.lookAt(0, 0, 0)

  const dt = Math.min(0.05, (renderLoop._last ? (now - renderLoop._last) : 16) / 1000)
  renderLoop._last = now
  lerpSignals(dt)

  // TX frame machine
  if(encoding){
    tickTx(now)
  }

  composer.render()
}

// --- Encode (fountain / LT-style) ---
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
  out._fountain = { k, r, copies: FOUNTAIN_SOURCE_COPIES, total: packets.length }
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
    const ft = frames._fountain || {}
    frameIndex = 0
    animPhase = "hold"
    phaseStartedAt = 0
    txRun++
    modeButtons.style.display = "none"
    videoWrap.hidden = true
    canvasWrap.style.display = ""
    setSignalBits(frames[0], true)
    setStatus(
      `Streaming “${meta.name}” · ${frames.length} frames (${ft.k || "?"}×${ft.copies || 2} + ${ft.r || "?"} repair) · ~80% decode OK · point camera here`
    )
  }
  reader.readAsArrayBuffer(file)
}

function tickTx(now){
  if(!phaseStartedAt) phaseStartedAt = now
  let elapsed = now - phaseStartedAt
  const dur = animPhase === "hold" ? FRAME_HOLD_MS : Math.max(1, FRAME_BLEND_MS)
  while(elapsed >= dur){
    elapsed -= dur
    phaseStartedAt += dur
    if(FRAME_BLEND_MS <= 0){
      frameIndex = (frameIndex + 1) % frames.length
      animPhase = "hold"
      setSignalBits(frames[frameIndex], true)
    }else if(animPhase === "hold"){
      animPhase = "blend"
      const next = frames[(frameIndex + 1) % frames.length]
      setSignalBits(next, false)
    }else{
      frameIndex = (frameIndex + 1) % frames.length
      animPhase = "hold"
      setSignalBits(frames[frameIndex], true)
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
let rxFountain = false
let rxK = null
let rxR = null
let rxSymbols = new Map() // seq -> { data, seed, indices }
let rxDecodeCount = 0
let rxPayloadOk = false
let rxRecovered = false
let decodeRunning = false
let detector = null
let decodeBitAccum = null
let decodeBitFrames = 0
let decodeAlignLocked = false
let decodeAlignMiss = 0
const DECODE_ACCUM_MIN = 4
const DECODE_ACCUM_MAX = 8
let decodeFrameNo = 0
let lastGoodQuad = null
let lastGoodQuadAge = 0
const decodeDbg = {
  video: "—",
  align: "no",
  miss: 0,
  sticky: 0,
  accum: 0,
  mean: 0,
  std: 0,
  sync: 0,
  crc: "—",
  last: "idle",
  fps: "—"
}
let decodeDbgLastT = 0
let decodeDbgFpsEma = 0

function updateDecodeDebug(){
  if(!decodeDebugEl) return
  const lines = [
    `frame ${decodeFrameNo} · ${decodeDbg.video} · ~${decodeDbg.fps} fps`,
    `align ${decodeDbg.align} · miss ${decodeDbg.miss} · stickyAge ${decodeDbg.sticky}`,
    `accum ${decodeDbg.accum}/${DECODE_ACCUM_MIN} · mean ${decodeDbg.mean.toFixed(1)} · std ${decodeDbg.std.toFixed(1)}`,
    `syncHits ${decodeDbg.sync} · crc ${decodeDbg.crc}`,
    rxFountain
      ? `fountain ok=${rxDecodeCount} unique=${rxSymbols.size} sources=${countUniqueSources()}/${rxK ?? "?"}`
      : `legacy chunks=${rxHave.size}/${rxTotal ?? "?"}`,
    `last: ${decodeDbg.last}`
  ]
  decodeDebugEl.textContent = lines.join("\n")
}

function bilinearInQuad(u, v, tl, tr, br, bl){
  const x =
    (1 - u) * (1 - v) * tl.x + u * (1 - v) * tr.x + u * v * br.x + (1 - u) * v * bl.x
  const y =
    (1 - u) * (1 - v) * tl.y + u * (1 - v) * tr.y + u * v * br.y + (1 - u) * v * bl.y
  return { x, y }
}

function orderQuadCorners(pts){
  const byY = pts.slice().sort((a, b) => a.y - b.y)
  const top = byY.slice(0, 2).sort((a, b) => a.x - b.x)
  const bot = byY.slice(2, 4).sort((a, b) => a.x - b.x)
  return { tl: top[0], tr: top[1], br: bot[1], bl: bot[0] }
}

function findBrightRegion(data, W, H, ox, oy, dw, dh){
  let minX = W, minY = H, maxX = 0, maxY = 0, n = 0
  const step = 2
  const x1 = (ox + dw) | 0
  const y1 = (oy + dh) | 0
  for(let y = oy | 0; y < y1; y += step){
    for(let x = ox | 0; x < x1; x += step){
      if(x < 0 || y < 0 || x >= W || y >= H) continue
      const p = (y * W + x) * 4
      const r8 = data[p], g = data[p + 1], b = data[p + 2]
      const peak = Math.max(r8, g, b)
      const luma = r8 * 0.299 + g * 0.587 + b * 0.114
      // Particle cloud / bloom — ignore dark chrome around the Mac window.
      if(peak < 55 || luma < 35) continue
      minX = Math.min(minX, x)
      minY = Math.min(minY, y)
      maxX = Math.max(maxX, x)
      maxY = Math.max(maxY, y)
      n++
    }
  }
  if(n < 30) return null
  const bw = maxX - minX
  const bh = maxY - minY
  if(bw < Math.min(dw, dh) * 0.12 || bh < Math.min(dw, dh) * 0.12) return null
  const pad = Math.round(Math.min(bw, bh) * 0.08)
  const x = Math.max(ox, minX - pad)
  const y = Math.max(oy, minY - pad)
  const r = Math.min(ox + dw, maxX + pad)
  const btm = Math.min(oy + dh, maxY + pad)
  return { x, y, w: r - x, h: btm - y }
}

function findCornerCentroid(data, W, H, x0, y0, w, h){
  let sx = 0, sy = 0, wsum = 0
  for(let y = y0; y < y0 + h; y++){
    for(let x = x0; x < x0 + w; x++){
      if(x < 0 || y < 0 || x >= W || y >= H) continue
      const p = (y * W + x) * 4
      const r8 = data[p], g = data[p + 1], b = data[p + 2]
      const peak = Math.max(r8, g, b)
      const sat = peak - Math.min(r8, g, b)
      // Glossy screen: skip white specular blobs (they are not cyan brackets).
      if(peak > 210 && sat < 35 && r8 > peak * 0.88) continue
      const cyan = Math.max(0, (g + b) * 0.5 - r8 * 0.35)
      if(cyan < 18) continue
      // Soft cyan bias — phone cameras often wash brackets toward white-blue.
      const blueBias = (b + g) - r8 * 1.5
      if(blueBias < 8) continue
      const weight = cyan * 0.7 + blueBias * 0.3 + sat * 0.15
      if(weight < 16) continue
      sx += x * weight
      sy += y * weight
      wsum += weight
    }
  }
  if(wsum < 25) return null
  return { x: sx / wsum, y: sy / wsum }
}

function detectAlignQuad(data, W, H, rect){
  const { ox, oy, dw, dh } = rect
  // Prefer the bright cloud/Mac region (portrait cameras place it mid-frame).
  const region = findBrightRegion(data, W, H, ox, oy, dw, dh)
  const rx = region ? region.x : ox
  const ry = region ? region.y : oy
  const rw = region ? region.w : dw
  const rh = region ? region.h : dh
  const pad = Math.round(Math.min(rw, rh) * 0.3)
  const cTL = findCornerCentroid(data, W, H, rx | 0, ry | 0, pad, pad)
  const cTR = findCornerCentroid(data, W, H, (rx + rw - pad) | 0, ry | 0, pad, pad)
  const cBR = findCornerCentroid(data, W, H, (rx + rw - pad) | 0, (ry + rh - pad) | 0, pad, pad)
  const cBL = findCornerCentroid(data, W, H, rx | 0, (ry + rh - pad) | 0, pad, pad)
  if(cTL && cTR && cBR && cBL){
    const q = orderQuadCorners([cTL, cTR, cBR, cBL])
    const wTop = Math.hypot(q.tr.x - q.tl.x, q.tr.y - q.tl.y)
    const wBot = Math.hypot(q.br.x - q.bl.x, q.br.y - q.bl.y)
    const hL = Math.hypot(q.bl.x - q.tl.x, q.bl.y - q.tl.y)
    const hR = Math.hypot(q.br.x - q.tr.x, q.br.y - q.tr.y)
    const minSide = Math.min(wTop, wBot, hL, hR)
    const maxSide = Math.max(wTop, wBot, hL, hR)
    if(minSide >= Math.min(rw, rh) * 0.35 && maxSide <= minSide * 1.75) return q
  }
  // Soft lock: sample through the bright Mac-window region even without brackets.
  if(region && Math.min(rw, rh) > Math.min(dw, dh) * 0.15){
    return {
      tl: { x: rx, y: ry },
      tr: { x: rx + rw, y: ry },
      br: { x: rx + rw, y: ry + rh },
      bl: { x: rx, y: ry + rh },
      _soft: true
    }
  }
  return null
}

function sampleLumaAt(data, W, H, x, y){
  const ix = Math.max(0, Math.min(W - 1, x | 0))
  const iy = Math.max(0, Math.min(H - 1, y | 0))
  let acc = 0, n = 0
  for(let dy = -1; dy <= 1; dy++){
    for(let dx = -1; dx <= 1; dx++){
      const xx = ix + dx, yy = iy + dy
      if(xx < 0 || yy < 0 || xx >= W || yy >= H) continue
      const p = (yy * W + xx) * 4
      const bb = data[p + 2], g = data[p + 1], r8 = data[p]
      const peak = Math.max(r8, g, bb)
      const sat = peak - Math.min(r8, g, bb)
      if(peak > 195 && sat < 35 && r8 > peak * 0.9) continue
      const luma = r8 * 0.299 + g * 0.587 + bb * 0.114
      const cyan = Math.max(0, (g + bb) * 0.5 - r8 * 0.3)
      acc += luma * 0.35 + peak * 0.35 + cyan * 0.3
      n++
    }
  }
  return n ? acc / n : 0
}

function syncScoreAt(bits, start){
  if(!bits || start < 0 || start + SYNC.length > bits.length) return 0
  let ok = 0
  for(let j = 0; j < SYNC.length; j++) if(bits[start + j] === SYNC[j]) ok++
  return ok
}

function bitsFromVals(vals){
  let sum = 0
  for(let i = 0; i < DATA_COUNT; i++) sum += vals[i]
  const mean = sum / DATA_COUNT
  let varSum = 0
  for(let i = 0; i < DATA_COUNT; i++){
    const d = vals[i] - mean
    varSum += d * d
  }
  const std = Math.sqrt(varSum / DATA_COUNT)
  decodeDbg.mean = mean
  decodeDbg.std = std

  let bestBits = null
  let bestScore = -1
  let bestThr = mean
  let bestConf = null
  const lo = mean - std * 1.2
  const hi = mean + std * 1.2
  for(let s = 0; s < 17; s++){
    const thr = lo + (hi - lo) * (s / 16)
    let bits = ""
    const conf = new Float32Array(DATA_COUNT)
    for(let i = 0; i < DATA_COUNT; i++){
      bits += vals[i] > thr ? "1" : "0"
      conf[i] = Math.abs(vals[i] - thr)
    }
    const score = syncScoreAt(bits, 0)
    if(score > bestScore){
      bestScore = score
      bestBits = bits
      bestThr = thr
      bestConf = conf
    }
  }
  if(bestScore < 30 && bestBits){
    for(const slip of [1, 2, 3]){
      const shifted = "0".repeat(slip) + bestBits.slice(0, DATA_COUNT - slip)
      const score = syncScoreAt(shifted, 0)
      if(score > bestScore){
        bestScore = score
        bestBits = shifted
      }
    }
  }
  decodeDbg.sync = bestScore
  decodeDbg.last = `thr ${bestThr.toFixed(1)} · SYNC0 ${bestScore}/32`
  bitsFromVals._thr = bestThr
  bitsFromVals._conf = bestConf
  bitsFromVals._vals = vals
  return bestBits
}

function bitsFromAccum(accum, frames){
  if(!accum || frames < 1) return null
  const vals = new Float32Array(DATA_COUNT)
  for(let i = 0; i < DATA_COUNT; i++) vals[i] = accum[i] / frames
  decodeDbg.accum = frames
  return bitsFromVals(vals)
}

function updateLockOverlay(quad, meta){
  if(!lockQuadEl || !videoWrap || !quad || !meta) return
  const wrapW = videoWrap.clientWidth
  const wrapH = videoWrap.clientHeight
  // Preview uses object-fit:cover; map cover-crop scan coords back to the video element.
  const cover = Math.max(wrapW / meta.vw, wrapH / meta.vh)
  const offX = (wrapW - meta.vw * cover) * 0.5
  const offY = (wrapH - meta.vh * cover) * 0.5
  const toScreen = (p) => {
    const vx = meta.sx + (p.x / meta.W) * meta.side
    const vy = meta.sy + (p.y / meta.H) * meta.side
    return { x: offX + vx * cover, y: offY + vy * cover }
  }
  const tl = toScreen(quad.tl), tr = toScreen(quad.tr), br = toScreen(quad.br), bl = toScreen(quad.bl)
  const minX = Math.min(tl.x, tr.x, br.x, bl.x)
  const minY = Math.min(tl.y, tr.y, br.y, bl.y)
  const maxX = Math.max(tl.x, tr.x, br.x, bl.x)
  const maxY = Math.max(tl.y, tr.y, br.y, bl.y)
  lockQuadEl.style.display = "block"
  lockQuadEl.style.left = minX + "px"
  lockQuadEl.style.top = minY + "px"
  lockQuadEl.style.width = Math.max(0, maxX - minX) + "px"
  lockQuadEl.style.height = Math.max(0, maxY - minY) + "px"
}

function sampleCloudBitsFromVideo(){
  const vw = video.videoWidth, vh = video.videoHeight
  if(!vw || !vh || !particleDirs) return null
  const scan = sampleCloudBitsFromVideo._c || (sampleCloudBitsFromVideo._c = document.createElement("canvas"))
  const S = 512
  scan.width = S
  scan.height = S
  const c = scan.getContext("2d", { willReadFrequently: true })
  // Match #video { object-fit: cover } so cyan corners land near the scan edges.
  const side = Math.min(vw, vh)
  const sx = ((vw - side) / 2) | 0
  const sy = ((vh - side) / 2) | 0
  c.drawImage(video, sx, sy, side, side, 0, 0, S, S)
  const img = c.getImageData(0, 0, S, S)
  const data = img.data
  const W = S, H = S
  const ox = 0, oy = 0, dw = S, dh = S

  let quad = detectAlignQuad(data, W, H, { ox, oy, dw, dh })
  let useQuad = quad
  const overlayMeta = { vw, vh, W, H, dw, dh, ox, oy, sx, sy, side }
  if(quad){
    lastGoodQuad = quad
    lastGoodQuadAge = 0
    decodeAlignMiss = 0
    decodeAlignLocked = !quad._soft
    decodeDbg.align = quad._soft ? "region" : "locked"
    decodeDbg.sticky = 0
    updateLockOverlay(useQuad, overlayMeta)
  }else if(lastGoodQuad && lastGoodQuadAge < 18){
    // Glare can temporarily hide the corners; re-use the last stable quad.
    useQuad = lastGoodQuad
    lastGoodQuadAge++
    decodeAlignMiss++
    decodeAlignLocked = lastGoodQuadAge <= 3
    decodeDbg.align = "sticky"
    decodeDbg.sticky = lastGoodQuadAge
    updateLockOverlay(useQuad, overlayMeta)
  }else{
    decodeAlignMiss++
    decodeAlignLocked = false
    lastGoodQuadAge++
    decodeDbg.align = "fallback-center"
    decodeDbg.sticky = lastGoodQuadAge
    if(lockQuadEl) lockQuadEl.style.display = "none"
    // Cover crop already fills the scan — sample the full square.
    useQuad = {
      tl: { x: 0, y: 0 },
      tr: { x: S, y: 0 },
      br: { x: S, y: S },
      bl: { x: 0, y: S }
    }
  }
  decodeDbg.miss = decodeAlignMiss
  decodeDbg.video = `${vw}×${vh}`
  decodeDbg.accum = decodeBitFrames

  const inset = SAMPLE_INSET
  const camY = CAMERA_BASE.y
  const camZ = CAMERA_BASE.z

  function sampleOne(pi, shellR, f){
    const x = particleDirs[pi * 3] * shellR
    const y = particleDirs[pi * 3 + 1] * shellR
    const z = particleDirs[pi * 3 + 2] * shellR
    const ey = y - camY
    const ez = z - camZ
    const invZ = 1 / Math.max(0.35, -ez)
    const ndcX = f * x * invZ
    const ndcY = f * ey * invZ
    let u = ndcX * 0.5 + 0.5
    let v = -ndcY * 0.5 + 0.5
    u = inset + u * (1 - inset * 2)
    v = inset + v * (1 - inset * 2)
    const p = bilinearInQuad(u, v, useQuad.tl, useQuad.tr, useQuad.br, useQuad.bl)
    return sampleLumaAt(data, W, H, p.x, p.y)
  }

  function sampleVals(shellR, fov){
    const f = 1 / Math.tan(fov * 0.5)
    const vals = new Float32Array(DATA_COUNT)
    for(let b = 0; b < DATA_COUNT; b++){
      const base = b * BIT_REPS
      let acc = 0
      for(let r = 0; r < BIT_REPS; r++){
        acc += sampleOne(DATA_INDICES[base + r], shellR, f)
      }
      vals[b] = acc / BIT_REPS
    }
    return vals
  }

  // Lock projection once SYNC@0 is strong — saves FPS on phone.
  let proj = sampleCloudBitsFromVideo._proj
  let bestBits = null
  let bestScore = -1
  let bestVals = null
  const tryProj = (shellR, fovDeg) => {
    const vals = sampleVals(shellR, fovDeg * Math.PI / 180)
    const bits = bitsFromVals(vals)
    const score = syncScoreAt(bits, 0)
    if(score > bestScore){
      bestScore = score
      bestBits = bits
      bestVals = vals
      sampleCloudBitsFromVideo._proj = { shellR, fovDeg }
    }
    return score
  }

  if(proj && decodeAlignLocked){
    tryProj(proj.shellR, proj.fovDeg)
    if(bestScore < 26){
      for(const shellR of [0.84, 0.90, 0.96]){
        for(const fovDeg of [36, 38, 40]) tryProj(shellR, fovDeg)
      }
    }
  }else{
    for(const shellR of [0.84, 0.90, 0.96]){
      for(const fovDeg of [36, 38, 40]){
        if(tryProj(shellR, fovDeg) >= 30) break
      }
      if(bestScore >= 30) break
    }
  }

  if(!decodeBitAccum) decodeBitAccum = new Float32Array(DATA_COUNT)
  if(bestVals){
    for(let i = 0; i < DATA_COUNT; i++) decodeBitAccum[i] += bestVals[i]
  }
  decodeBitFrames++
  if(decodeBitFrames > DECODE_ACCUM_MAX){
    const keep = DECODE_ACCUM_MAX - 1
    const scale = keep / decodeBitFrames
    for(let i = 0; i < DATA_COUNT; i++) decodeBitAccum[i] *= scale
    decodeBitFrames = keep
  }
  sampleCloudBitsFromVideo._meta = { quad: useQuad, aligned: !!quad }

  if(decodeBitFrames < DECODE_ACCUM_MIN) return null
  if(bestScore >= 28 && bestBits) return bestBits
  return bitsFromAccum(decodeBitAccum, decodeBitFrames)
}

function resetDecodeAccum(){
  decodeBitAccum = new Float32Array(DATA_COUNT)
  decodeBitFrames = 0
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
}

const decodeQuality = {
  syncPeak: 0,
  contrastPeak: 0,
  alignPeak: 0,
  crcPeak: 0,
  crcScore: 0
}

function resetDecodeQuality(){
  decodeQuality.syncPeak = 0
  decodeQuality.contrastPeak = 0
  decodeQuality.alignPeak = 0
  decodeQuality.crcPeak = 0
  decodeQuality.crcScore = 0
}

function setMeter(fillEl, valEl, peakEl, pct, label, peakPct){
  const p = Math.max(0, Math.min(100, pct))
  if(fillEl) fillEl.style.width = p + "%"
  if(valEl && label != null) valEl.textContent = label
  if(peakEl && peakPct != null) peakEl.style.left = Math.max(0, Math.min(100, peakPct)) + "%"
}

function updateDecodeMeters(){
  if(!decodeMetersEl) return

  let alignPct = 0
  if(decodeDbg.align === "locked") alignPct = 100
  else if(decodeDbg.align === "sticky") alignPct = 70
  else if(decodeDbg.align === "region") alignPct = 55
  else alignPct = Math.max(0, 25 - Math.min(25, decodeDbg.miss / 40))
  if(alignPct > decodeQuality.alignPeak) decodeQuality.alignPeak = alignPct
  setMeter(
    meterAlignFill,
    meterAlignVal,
    null,
    alignPct,
    `${Math.round(alignPct)}% · ${decodeDbg.align}`
  )

  const syncNow = decodeDbg.sync || 0
  if(syncNow > decodeQuality.syncPeak) decodeQuality.syncPeak = syncNow
  const syncPct = (syncNow / 32) * 100
  const syncPeakPct = (decodeQuality.syncPeak / 32) * 100
  setMeter(
    meterSyncFill,
    meterSyncVal,
    meterSyncPeak,
    syncPct,
    `${syncNow}/32 · best ${decodeQuality.syncPeak}/32`,
    syncPeakPct
  )

  // Contrast: useful optical separation; peak ~30+ is strong on phone captures.
  const contrast = decodeDbg.std || 0
  if(contrast > decodeQuality.contrastPeak) decodeQuality.contrastPeak = contrast
  const contrastPct = Math.min(100, (contrast / 40) * 100)
  setMeter(
    meterContrastFill,
    meterContrastVal,
    null,
    contrastPct,
    `${contrast.toFixed(1)} · best ${decodeQuality.contrastPeak.toFixed(1)}`
  )

  // CRC meter: rises with SYNC@0 quality (getting closer), snaps to 100 on CRC ok.
  let crcScore = 0
  if(rxRecovered || decodeDbg.crc === "ok" || rxPayloadOk){
    crcScore = 100
  }else{
    // Map SYNC 0..32 → 0..85, reserving the top for a real CRC hit.
    crcScore = Math.min(85, Math.round((syncNow / 32) * 85))
    if(decodeDbg.crc === "fail" && syncNow >= 24) crcScore = Math.max(crcScore, 60)
    if(rxFountain && rxSymbols.size > 0){
      const need = rxK || 1
      crcScore = Math.max(crcScore, Math.min(95, Math.round((rxSymbols.size / need) * 95)))
    }
  }
  decodeQuality.crcScore = crcScore
  if(crcScore > decodeQuality.crcPeak) decodeQuality.crcPeak = crcScore
  const crcLabel = rxRecovered
    ? "recovered"
    : decodeDbg.crc === "ok"
      ? "CRC ok"
      : `~${crcScore}% · best ${decodeQuality.crcPeak}%`
  setMeter(
    meterCrcFill,
    meterCrcVal,
    meterCrcPeak,
    crcScore,
    crcLabel,
    decodeQuality.crcPeak
  )
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
  sym.set(data.subarray(0, SYMBOL_SIZE))
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
  const decodedFrames = rxDecodeCount
  if(decodedFrames < Math.ceil(sent * 0.75)) return false
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
  setStatus(
    `Recovered “${downloadLink.download}” (${finalBytes.length} bytes) · ${rxDecodeCount} frames decoded.`
  )
  try{ downloadLink.click() }catch(_){}
  rxRecovered = true
  updateDecodeMeters()
  decodeRunning = false
  return true
}

function tryFinish(){
  if(rxFountain) return tryFinishFountain()
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
  rxRecovered = true
  updateDecodeMeters()
  decodeRunning = false
  return true
}

function decodeBodyText(bodyBits, startLabel){
  const maxBytes = Math.min(520, (bodyBits.length / 8) | 0)
  let tried = 0
  for(let blen = 8; blen <= maxBytes; blen++){
    const body = bitsToBytes(bodyBits.slice(0, blen * 8))
    if(body.length < 5) continue
    tried++
    const raw = body.subarray(0, body.length - 4)
    const crc =
      ((body[body.length - 4] << 24) |
        (body[body.length - 3] << 16) |
        (body[body.length - 2] << 8) |
        body[body.length - 1]) >>> 0
    if(crc32(raw) !== crc) continue
    try{
      const text = new TextDecoder().decode(raw)
      if(text.startsWith("PC6M|") || text.startsWith("PC6|") ||
         text.startsWith("PC5M|") || text.startsWith("PC5D|")){
        return { text, tried, startLabel }
      }
    }catch(_){}
  }
  return { text: null, tried, startLabel }
}

function bitsToPayload(bits){
  if(!bits || bits.length < SYNC.length + 16) return null
  const candidates = []
  let bestOk = 0
  const limit = bits.length - SYNC.length
  for(let i = 0; i <= limit; i++){
    const ok = syncScoreAt(bits, i)
    if(ok > bestOk) bestOk = ok
    if(i <= 12 && ok >= 20) candidates.push({ i, ok })
    else if(ok >= 30) candidates.push({ i, ok })
  }
  decodeDbg.sync = bestOk
  if(!candidates.length){
    decodeDbg.crc = "no-sync"
    decodeDbg.last = `no SYNC (best ${bestOk}/32)`
    return null
  }
  candidates.sort((a, b) => b.ok - a.ok || a.i - b.i)

  let triedLens = 0
  const conf = bitsFromVals._conf
  for(const cand of candidates.slice(0, 6)){
    const bodyBits = bits.slice(cand.i + SYNC.length)
    let hit = decodeBodyText(bodyBits, `SYNC@${cand.i}(${cand.ok}/32)`)
    triedLens += hit.tried
    if(hit.text){
      decodeDbg.crc = "ok"
      decodeDbg.last = `${hit.startLabel} ${hit.text.slice(0, 24)}…`
      return hit.text
    }

    // Soft chase: flip the most ambiguous body bits (near threshold).
    if(conf && cand.i === 0 && cand.ok >= 24){
      const amb = []
      for(let i = SYNC.length; i < Math.min(bits.length, SYNC.length + 1600); i++){
        amb.push({ i, c: conf[i] ?? 1e9 })
      }
      amb.sort((a, b) => a.c - b.c)
      const top = amb.slice(0, 10).map(x => x.i)
      const flipAt = (src, idx) => {
        const arr = src.split("")
        arr[idx] = arr[idx] === "1" ? "0" : "1"
        return arr.join("")
      }
      // Singles
      for(const idx of top){
        const b2 = flipAt(bits, idx)
        hit = decodeBodyText(b2.slice(SYNC.length), `flip1@${idx}`)
        triedLens += hit.tried
        if(hit.text){
          decodeDbg.crc = "ok"
          decodeDbg.last = `${hit.startLabel} ${hit.text.slice(0, 24)}…`
          return hit.text
        }
      }
      // Pairs among top 8
      for(let a = 0; a < Math.min(8, top.length); a++){
        for(let b = a + 1; b < Math.min(8, top.length); b++){
          let b2 = flipAt(bits, top[a])
          b2 = flipAt(b2, top[b])
          hit = decodeBodyText(b2.slice(SYNC.length), `flip2`)
          triedLens += hit.tried
          if(hit.text){
            decodeDbg.crc = "ok"
            decodeDbg.last = `${hit.startLabel} ${hit.text.slice(0, 24)}…`
            return hit.text
          }
        }
      }
    }
  }
  decodeDbg.crc = "fail"
  decodeDbg.last = `best SYNC ${bestOk}/32 @${candidates[0].i} · CRC miss (${triedLens} lens)`
  return null
}

async function tuneDecoderCamera(stream){
  const track = stream.getVideoTracks()[0]
  if(!track) return {}
  const caps = typeof track.getCapabilities === "function" ? track.getCapabilities() : {}
  const advanced = {}
  const focusModes = caps.focusMode
  if(Array.isArray(focusModes) && focusModes.includes("continuous")) advanced.focusMode = "continuous"
  const exposureModes = caps.exposureMode
  if(Array.isArray(exposureModes) && exposureModes.includes("continuous")) advanced.exposureMode = "continuous"
  const wbModes = caps.whiteBalanceMode
  if(Array.isArray(wbModes) && wbModes.includes("continuous")) advanced.whiteBalanceMode = "continuous"
  if(Object.keys(advanced).length){
    try{ await track.applyConstraints({ advanced: [advanced] }) }catch(_){}
  }
  // Safari on iPhone often caps at ~30 fps; asking for 60 is harmless if ignored.
  try{
    await track.applyConstraints({ frameRate: { ideal: 60, max: 60 } })
  }catch(_){
    try{ await track.applyConstraints({ frameRate: { ideal: 30 } }) }catch(__){}
  }
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

async function startDecoder(){
  txRun = 0
  frames = []
  modeButtons.style.display = "none"
  canvasWrap.style.display = "none"
  videoWrap.hidden = false
  progressWrap.hidden = false
  downloadLink.hidden = true
  resetRxState()
  resetDecodeAccum()
  decodeAlignLocked = false
  decodeAlignMiss = 0
  lastGoodQuad = null
  lastGoodQuadAge = 0
  sampleCloudBitsFromVideo._proj = null
  decodeFrameNo = 0
  progressBar.style.width = "0%"
  progressText.textContent = "Frames: 0"
  if(decodeMetersEl) decodeMetersEl.hidden = false
  resetDecodeQuality()
  if(decodeDebugEl){
    decodeDebugEl.hidden = false
    decodeDbg.last = "decoder started"
    decodeDbg.crc = "—"
    decodeDbg.sync = 0
    decodeDbg.align = "no"
    decodeDbg.miss = 0
    decodeDbg.sticky = 0
    decodeDbg.accum = 0
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
        frameRate: { ideal: 60, max: 60 }
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

  if("BarcodeDetector" in window){
    try{ detector = new BarcodeDetector({ formats: ["qr_code"] }) }catch(_){ detector = null }
  }

  decodeRunning = true
  const showCaptureStatus = () => {
    const capLabel = formatCaptureLabel(captureSettings, video.videoWidth, video.videoHeight)
    setStatus(`Point at the cloud · fill view with screen · cyan corners visible · ${capLabel}. Tilt to kill glare.`)
  }
  showCaptureStatus()
  video.addEventListener("loadedmetadata", () => {
    captureSettings = { ...captureSettings, width: video.videoWidth, height: video.videoHeight }
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
  const have = rxFountain ? rxDecodeCount : rxHave.size
  const need = rxFountain
    ? (rxK != null
      ? `${countUniqueSources()}/${rxK} sources`
      : "?")
    : (rxTotal || "?")
  const alignHint = decodeAlignLocked ? " · corners locked" : decodeAlignMiss > 8 ? " · find cyan corners" : " · align corners"
  progressText.textContent = rxFountain
    ? `Fountain: ${rxDecodeCount} OK · ${need}${alignHint}`
    : `Frames decoded: ${have} / ${need}${alignHint}`
  if(rxFountain && rxK){
    const sent = rxK * FOUNTAIN_SOURCE_COPIES + (rxR || 0)
    const pct = Math.min(100, Math.floor((rxDecodeCount / Math.ceil(sent * 0.8)) * 100))
    progressBar.style.width = pct + "%"
  }else if(rxTotal){
    progressBar.style.width = Math.min(100, Math.floor((have / rxTotal) * 100)) + "%"
  }

  updateDecodeMeters()
  updateDecodeDebug()

  // Primary: sample cloud bits
  if(video.videoWidth){
    const bits = sampleCloudBitsFromVideo()
    if(bits){
      const text = bitsToPayload(bits)
      if(text && ingestPayloadText(text)){
        rxPayloadOk = true
        resetDecodeAccum()
        const prog = rxFountain
          ? `${rxSymbols.size} symbols · peeling…`
          : `${rxHave.size}${rxTotal ? " / " + rxTotal : ""} frames`
        setStatus(`Locked cloud signal · ${prog}`)
        decodeDbg.last = `ingested · ${prog}`
        updateDecodeDebug()
        if(tryFinish()) return
      }else if(rxFountain && rxSymbols.size >= (rxK || 0)){
        if(tryFinish()) return
      }
      updateDecodeDebug()
    }else{
      decodeDbg.last = decodeBitFrames < DECODE_ACCUM_MIN
        ? `warming accum ${decodeBitFrames}/${DECODE_ACCUM_MIN}`
        : "no bits yet"
      updateDecodeDebug()
    }
  }

  // Optional: if a QR ever appears in view, accept PC5 payloads too
  if(detector && video.videoWidth && decodeFrameNo % 24 === 0){
    try{
      const codes = await detector.detect(video)
      for(const c of codes){
        if(ingestPayloadText(c.rawValue)){
          rxPayloadOk = true
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
    const i = DATA_INDICES[b * BIT_REPS]
    const x = particleDirs ? particleDirs[i * 3] : 0
    const y = particleDirs ? particleDirs[i * 3 + 1] : 0
    const z = particleDirs ? particleDirs[i * 3 + 2] : 0
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
