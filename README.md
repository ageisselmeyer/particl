# PartiCl

Particle-stipple QR file transfer — encode on a desktop browser, decode with your phone camera.

## Run locally (camera needs HTTPS)

```bash
python3 serve-https.py 8443
```

Open `https://localhost:8443` on the Mac and `https://<your-mac-ip>:8443` on iPhone. Trust the self-signed cert once, then allow Camera.

## Tests

```bash
node test/fountain.mjs
```

## URL flags

| Param | Effect |
|-------|--------|
| `?plain=1` | Solid QR modules (no stipple) |
| `?omitfinders=1` | Omit TX corner finders; RX stamps them before decode |
