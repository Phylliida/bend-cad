#!/usr/bin/env python3
"""bend-cad GUI server: serves the sketcher page and runs the verified
solver (gui/solve_cli, built from gui/solve_cli.bend) on POST /api/solve.

Usage: python3 gui/serve.py [port]      (default port 8480)

The page sends the sketch as JSON:
  vars: [kind]                0 coord, 1 length, 2 param, 3 aux
  ents: [[id, construction, kind, a, b, c?]]
  cons: [[driven, kind, args...]]  dimension values as decimal strings
  g0:   [float]               the drawn value of each variable
and gets back {ok, red, pins, cls, own, gc, gr, ms}: red as constraint
positions; cls one class per constraint position, {k: "kept" | "amber" |
"over" | "conflict", drops: equation positions, j, s, w for over (its
equation, its set of equations, its variables), s for conflict (its
support, constraint positions)}; own each equation's constraint position.
"""
import json, os, subprocess, sys, tempfile, time
from fractions import Fraction
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CLI = os.path.join(HERE, "solve_cli")
SRC = os.path.join(HERE, "solve_cli.bend")

# constraint kinds and which arguments are rational values (by position)
KINDS = ["Coincident", "Horizontal", "Vertical", "Concentric", "EqualRadius",
         "Fix", "Distance", "HDistance", "VDistance", "Radius", "Diameter",
         "LineDistance", "Angle", "EqualLength", "Perpendicular", "Parallel",
         "OnLine", "OnCircle", "Midpoint", "Symmetric"]
QARGS = {5: [1], 6: [2], 7: [2], 8: [2], 9: [1], 10: [1], 11: [3], 12: [4, 5]}


def sbin(n):
    """a signed integer in binary, most significant bit first"""
    if n == 0:
        return "0"
    return ("-" if n < 0 else "") + bin(abs(n))[2:]


def qstr(v):
    """an exact rational from "n/d" or a decimal string"""
    f = Fraction(str(v))
    return sbin(f.numerator) + "/" + bin(f.denominator)[2:]


def dyadic(x, e=40):
    return sbin(int(round(float(x) * (1 << e)))) + ":" + str(e)


def undyadic(s):
    m, e = s.split(":")
    neg = m.startswith("-")
    mv = int(m.lstrip("-"), 2) if m.lstrip("-") else 0
    return (-mv if neg else mv) / float(1 << int(e))


def sketch_text(sk):
    vars_ = " ".join(str(int(k)) for k in sk["vars"])
    ents = ",".join(" ".join(str(int(t)) for t in e) for e in sk["ents"])
    cons = []
    for i, c in enumerate(sk["cons"]):
        driven, kind, args = int(c[0]), int(c[1]), c[2:]
        qs = QARGS.get(kind, [])
        out = [str(i), str(driven), str(kind)]
        for j, a in enumerate(args):
            out.append(qstr(a) if j in qs else str(int(a)))
        cons.append(" ".join(out))
    g0 = " ".join(dyadic(x) for x in sk["g0"])
    return "\n".join([vars_, ents, ",".join(cons), g0]) + "\n"


def nums(t):
    return [int(x) for x in t.split(",") if x != ""]


def parse_cls(tok):
    """one class token of solve_cli's cls line: K, K/d, A, A/d, O/j/s/w, C/s"""
    f = tok.split("/")
    if f[0] in ("K", "A"):
        return {"k": "kept" if f[0] == "K" else "amber", "drops": nums(f[1]) if len(f) > 1 else []}
    if f[0] == "O":
        return {"k": "over", "drops": [], "j": int(f[1]), "s": nums(f[2]), "w": nums(f[3])}
    return {"k": "conflict", "drops": [], "s": nums(f[1])}


def parse_out(text):
    res = {"ok": False, "red": [], "pins": [], "cls": [], "own": [], "gc": [], "gr": []}
    for line in text.splitlines():
        parts = line.split()
        if not parts:
            continue
        tag, rest = parts[0], parts[1:]
        if tag == "ok":
            res["ok"] = rest[:1] == ["True"]
        elif tag in ("red", "pins", "own"):
            res[tag] = [int(t) for t in rest]
        elif tag == "cls":
            res["cls"] = [parse_cls(t) for t in rest]
        elif tag in ("gc", "gr"):
            res[tag] = [undyadic(t) for t in rest]
    return res


def sources():
    """the files the solver binary is built from: the CLI and every .bend it
    can import (a change to the solver in lib/ must rebuild it too)"""
    out = [SRC, os.path.join(ROOT, "proto", "block.bend")]
    for sub in ("lib", "spec"):
        d = os.path.join(ROOT, sub)
        out += [os.path.join(d, f) for f in os.listdir(d) if f.endswith(".bend")]
    return out


def ensure_cli():
    if os.path.exists(CLI) and os.path.getmtime(CLI) >= max(os.path.getmtime(f) for f in sources()):
        return
    print("building the solver (about 20 s) ...", flush=True)
    r = subprocess.run([os.path.join(ROOT, "bin", "bend"), SRC, "-o", CLI],
                       cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(CLI):
        print(r.stdout, r.stderr)
        sys.exit("could not build gui/solve_cli")
    print("solver built", flush=True)


def solve(sk):
    text = sketch_text(sk)
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, "sketch.in"), "w") as f:
            f.write(text)
        t0 = time.time()
        try:
            r = subprocess.run([CLI, "--threads", "1"], cwd=d, capture_output=True,
                               text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return {"error": "the solver timed out"}
        ms = int((time.time() - t0) * 1000)
    if r.returncode != 0:
        return {"error": (r.stderr or r.stdout)[-2000:], "input": text}
    res = parse_out(r.stdout)
    res["ms"] = ms
    res["input"] = text
    return res


TYPES = {".html": "text/html; charset=utf-8", ".js": "text/javascript; charset=utf-8",
         ".css": "text/css; charset=utf-8", ".svg": "image/svg+xml"}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def send_body(self, code, body, ctype):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = self.path.split("?")[0]
        if path == "/":
            path = "/index.html"
        name = os.path.normpath(path.lstrip("/"))
        full = os.path.join(HERE, name)
        if name.startswith("..") or not os.path.isfile(full):
            self.send_body(404, b"not found", "text/plain")
            return
        with open(full, "rb") as f:
            body = f.read()
        self.send_body(200, body, TYPES.get(os.path.splitext(full)[1], "application/octet-stream"))

    def do_POST(self):
        if self.path != "/api/solve":
            self.send_body(404, b"not found", "text/plain")
            return
        n = int(self.headers.get("Content-Length", "0"))
        try:
            sk = json.loads(self.rfile.read(n))
            res = solve(sk)
        except Exception as e:  # report malformed requests to the page
            res = {"error": repr(e)}
        self.send_body(200, json.dumps(res).encode(), "application/json")


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8480
    ensure_cli()
    srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    print(f"bend-cad sketcher: http://localhost:{port}/", flush=True)
    srv.serve_forever()


if __name__ == "__main__":
    main()
