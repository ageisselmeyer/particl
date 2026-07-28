#!/usr/bin/env python3
"""Local HTTPS static server for iPhone camera (getUserMedia needs secure context)."""
from __future__ import annotations

import http.server
import os
import ssl
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(ROOT, "certs", "cert.pem")
KEY = os.path.join(ROOT, "certs", "key.pem")
PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8443


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=ROOT, **kwargs)

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()


def main():
    if not (os.path.isfile(CERT) and os.path.isfile(KEY)):
        print("Missing certs/cert.pem or certs/key.pem — regenerate first.", file=sys.stderr)
        sys.exit(1)
    server = http.server.ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    ctx.load_cert_chain(certfile=CERT, keyfile=KEY)
    server.socket = ctx.wrap_socket(server.socket, server_side=True)
    print(f"HTTPS serving {ROOT}")
    print(f"  Mac:    https://localhost:{PORT}")
    print(f"  iPhone: https://<this-mac-lan-ip>:{PORT}")
    print("Trust the cert warning once on iOS (Advanced → Proceed), then allow Camera.")
    server.serve_forever()


if __name__ == "__main__":
    main()
