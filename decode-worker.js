/* Decode worker: dilate + ZXing / jsQR off the main thread. */
/* global jsQR, ZXing */

importScripts("vendor/jsqr/jsQR.js", "vendor/zxing/zxing.min.js")

function dilateRgba(data, w, h, rad){
  const src = new Uint8ClampedArray(data)
  const r = Math.max(1, rad | 0)
  for(let y = r; y < h - r; y++){
    for(let x = r; x < w - r; x++){
      const i = (y * w + x) * 4
      if(src[i] < 140) continue
      let dark = false
      // Fast path rad=1: 4-neighbor + self already known light — check cross first
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
}

function rgbaToLum(data, w, h){
  const lum = new Uint8ClampedArray(w * h)
  for(let i = 0, j = 0; i < data.length; i += 4, j++){
    lum[j] = (data[i] * 3 + data[i + 1] * 4 + data[i + 2]) >> 3
  }
  return lum
}

function tryZXing(data, w, h, hard){
  if(typeof ZXing === "undefined" || typeof ZXing.QRCodeReader !== "function") return null
  try{
    const src = new ZXing.RGBLuminanceSource(rgbaToLum(data, w, h), w, h)
    const bmp = new ZXing.BinaryBitmap(new ZXing.HybridBinarizer(src))
    const hints = new Map()
    if(hard) hints.set(ZXing.DecodeHintType.TRY_HARDER, true)
    hints.set(ZXing.DecodeHintType.POSSIBLE_FORMATS, [ZXing.BarcodeFormat.QR_CODE])
    const result = new ZXing.QRCodeReader().decode(bmp, hints)
    return result && result.getText ? result.getText() : null
  }catch(_){
    return null
  }
}

function tryJsQR(data, w, h){
  if(typeof jsQR !== "function") return null
  const code = jsQR(data, w, h, { inversionAttempts: "dontInvert" })
  return code && code.data ? code.data : null
}

self.onmessage = (ev) => {
  const msg = ev.data
  if(!msg || msg.type !== "decode") return
  const { id, width: w, height: h, dilate, tryHarder } = msg
  const data = new Uint8ClampedArray(msg.buffer)
  if(dilate > 0) dilateRgba(data, w, h, dilate)
  let text = tryZXing(data, w, h, !!tryHarder)
  let engine = text ? "ZXing" : null
  if(!text){
    text = tryJsQR(data, w, h)
    if(text) engine = "jsQR"
  }
  self.postMessage({ type: "result", id, text: text || null, engine, w, dilate })
}
