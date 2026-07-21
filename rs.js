/**
 * Reed-Solomon over GF(256) — QR-style ECC (Wikiversity / Berlekamp-Massey).
 * Corrects up to floor(nsym/2) byte errors in a codeword.
 */
const EXP = new Uint8Array(512)
const LOG = new Uint8Array(256)
;(function(){
  let x = 1
  for(let i = 0; i < 255; i++){
    EXP[i] = x
    LOG[x] = i
    x = (x << 1) ^ (x & 0x80 ? 0x11d : 0)
  }
  for(let i = 255; i < 512; i++) EXP[i] = EXP[i - 255]
})()

const mul = (a, b) => (a && b ? EXP[LOG[a] + LOG[b]] : 0)
const div = (a, b) => {
  if(!b) throw new Error("div0")
  return a ? EXP[(LOG[a] + 255 - LOG[b]) % 255] : 0
}
const inv = a => EXP[255 - LOG[a]]
const pow2 = i => EXP[i % 255]

function polyMul(p, q){
  const out = new Uint8Array(p.length + q.length - 1)
  for(let j = 0; j < q.length; j++)
    for(let i = 0; i < p.length; i++) out[i + j] ^= mul(p[i], q[j])
  return out
}

function polyEval(p, x){
  let y = p[0]
  for(let i = 1; i < p.length; i++) y = mul(y, x) ^ p[i]
  return y
}

function generator(nsym){
  let g = new Uint8Array([1])
  for(let i = 0; i < nsym; i++) g = polyMul(g, new Uint8Array([1, pow2(i)]))
  return g
}

export function rsEncode(data, nsym){
  const gen = generator(nsym)
  const msg = new Uint8Array(data.length + nsym)
  msg.set(data)
  for(let i = 0; i < data.length; i++){
    const coef = msg[i]
    if(!coef) continue
    for(let j = 1; j < gen.length; j++) msg[i + j] ^= mul(gen[j], coef)
  }
  msg.set(data) // restore systematic message
  return msg
}

function syndromes(msg, nsym){
  const syn = new Array(nsym)
  let err = false
  for(let i = 0; i < nsym; i++){
    syn[i] = polyEval(msg, pow2(i))
    if(syn[i]) err = true
  }
  return { syn, err }
}

/** Berlekamp-Massey → error locator C(x), degree L. */
function berlekampMassey(syn){
  const N = syn.length
  const C = new Array(N + 1).fill(0)
  const B = new Array(N + 1).fill(0)
  C[0] = 1
  B[0] = 1
  let L = 0, m = 1, b = 1
  for(let n = 0; n < N; n++){
    let delta = syn[n]
    for(let i = 1; i <= L; i++) delta ^= mul(C[i], syn[n - i])
    if(delta === 0){
      m++
      continue
    }
    const T = C.slice()
    const scale = div(delta, b)
    for(let i = 0; i <= N - m; i++) C[i + m] ^= mul(scale, B[i])
    if(2 * L <= n){
      L = n + 1 - L
      for(let i = 0; i <= N; i++) B[i] = T[i]
      b = delta
      m = 1
    }else{
      m++
    }
  }
  return { C: C.slice(0, L + 1), L }
}

export function rsDecode(codeword, nsym){
  if(!codeword || codeword.length <= nsym) return null
  const msg = Uint8Array.from(codeword)
  const { syn, err } = syndromes(msg, nsym)
  if(!err) return msg.subarray(0, msg.length - nsym)

  const { C, L } = berlekampMassey(syn)
  if(L === 0 || L * 2 > nsym) return null

  // Chien: C(α^i)==0 → error at position n-1-i
  const n = msg.length
  const errPos = []
  for(let i = 0; i < n; i++){
    if(polyEval(C, pow2(i)) === 0) errPos.push(n - 1 - i)
  }
  if(errPos.length !== L) return null

  if(!forneyCorrect(msg, syn, C, errPos)) return null
  if(syndromes(msg, nsym).err) return null
  return msg.subarray(0, msg.length - nsym)
}

/** Forney magnitudes for known errata positions (errors or erasures). */
function forneyCorrect(msg, syn, C, errPos){
  const nsym = syn.length
  const L = C.length - 1
  const n = msg.length
  const omega = new Array(nsym).fill(0)
  for(let i = 0; i < nsym; i++){
    omega[i] = syn[i]
    for(let j = 1; j <= Math.min(i, L); j++) omega[i] ^= mul(C[j], syn[i - j])
  }
  for(const pos of errPos){
    const Xi = pow2(n - 1 - pos)
    const XiInv = inv(Xi)
    let num = 0, p = 1
    for(let i = 0; i < Math.min(L, nsym); i++){
      num ^= mul(omega[i], p)
      p = mul(p, XiInv)
    }
    let den = 0
    for(let i = 1; i < C.length; i += 2){
      let xp = 1
      for(let k = 0; k < i - 1; k++) xp = mul(xp, XiInv)
      den ^= mul(C[i], xp)
    }
    if(!den) return false
    msg[pos] ^= mul(Xi, div(num, den))
  }
  return true
}

/**
 * Decode with known erasure positions — recovers up to nsym missing bytes
 * (MDS: any k of k+nsym systematically encoded symbols).
 */
export function rsDecodeErasures(codeword, nsym, erasePos){
  if(!codeword || codeword.length <= nsym) return null
  const msg = Uint8Array.from(codeword)
  const n = msg.length
  const erasures = [...new Set(erasePos)].filter(p => p >= 0 && p < n)
  if(erasures.length > nsym) return null
  for(const p of erasures) msg[p] = 0

  const { syn, err } = syndromes(msg, nsym)
  if(!err) return msg.subarray(0, n - nsym)
  if(!erasures.length) return null

  // Erasure locator Λ(x) = Π (1 + X_i x), X_i = α^{n-1-pos}
  let C = new Uint8Array([1])
  for(const pos of erasures){
    const X = pow2(n - 1 - pos)
    C = polyMul(C, new Uint8Array([1, X]))
  }
  if(C.length - 1 > nsym) return null

  if(!forneyCorrect(msg, syn, Array.from(C), erasures)) return null
  if(syndromes(msg, nsym).err) return null
  return msg.subarray(0, n - nsym)
}

/** Parity bytes per codeword — corrects up to floor(nsym/2) unknown errors. */
export const RS_NSYM = 24
