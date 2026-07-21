# PartiCl

Encode a file as an **Apple Watch–style glowing blue particle cloud**, then recover it with a phone camera.

## Run

Serve the folder over HTTP (ES modules):

```bash
python3 -m http.server 8765
```

Open `http://localhost:8765`.

## Encode

1. Click **Encode** and pick a file.
2. The cloud streams high-entropy frames (particle brightness carries the payload).
3. Point another device’s camera at the display to decode.

## Decode

1. Click **Decode** and allow camera access.
2. Keep the cloud centered and steady.
3. Progress updates as frames lock; the file downloads when complete.

## Stack

- Three.js points + custom shaders (additive cyan/blue glow)
- UnrealBloomPass for soft bloom
- Fibonacci sphere layout; data bits on a particle subset
