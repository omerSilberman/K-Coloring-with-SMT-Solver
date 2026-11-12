#!/usr/bin/env python3
"""K-Coloring Explorer: a small local web UI for smt_solver_cvc5 (and the dReal trig solver).

Pick a graph, a solver and K; the page shows the asserted formulas in mathematical notation,
a live timer while the solver runs, and then SAT/UNSAT with the coloring.

    ./gui/kcolor_gui.py [--port N] [--no-browser]

Standard library only. The server runs the solver binary as a subprocess with
--print-asserts --model and streams its output to the page (Server-Sent Events).
"""
import argparse
import json
import os
import queue
import re
import subprocess
import sys
import threading
import time
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATIC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "static")
sys.path.insert(0, os.path.join(ROOT, "common"))
from graph import read_dimacs  # noqa: E402  (shared with dreal/)
K_FILE = os.path.join(ROOT, "optimal_k_values.json")
BENCHMARKS = os.path.join(ROOT, "benchmarks")

MAX_ASSERTS_SENT = 5000      # the page gets at most this many assertions; the rest are only counted
DRAW_MAX_NODES = 300         # graphs up to this size are sent to the page for drawing
DRAW_MAX_EDGES = 6000

# The SMT solvers the page can pick. Each runs as `command THEORY graph K --print-asserts
# --model`, and its encodings come from `command --help`. `options`: takes --opt NAME=VALUE.
ENGINES = {
    "cvc5": {"label": "cvc5", "command": [os.path.join(ROOT, "build", "smt_solver_cvc5")], "options": True,
             "about": "cvc5, through its C++ API: every encoding"},
    "z3": {"label": "Z3", "command": [os.path.join(ROOT, "build", "smt_solver_z3")], "options": True,
           "about": "Z3, through its C++ API: the same encodings, minus the theories Z3 lacks (finite fields, bags, separation logic, trigonometry)"},
    "dreal": {"label": "dReal", "command": [sys.executable, os.path.join(ROOT, "dreal", "smt_solver_dreal.py")],
              "options": False, "about": "dReal, a delta-complete solver for the trig encodings: finds the SAT models cvc5 cannot"},
}

CONTENT_TYPES = {".html": "text/html", ".css": "text/css", ".js": "application/javascript", ".svg": "image/svg+xml"}


# ---------------------------------------------------------------------------
# Graphs and solvers
# ---------------------------------------------------------------------------
def read_graph(path):
    """(num_nodes, edges) of a DIMACS file, read the same way as the solvers."""
    return read_dimacs(path)


def graph_header(path):
    """(nodes, edges) from the 'p' line only, without reading the whole file."""
    with open(path) as f:
        for line in f:
            if line.startswith("p"):
                parts = line.split()
                return int(parts[2]), int(parts[3])
    return 0, 0


def list_graphs():
    known_k = {}
    if os.path.exists(K_FILE):
        with open(K_FILE) as f:
            for path, data in json.load(f).items():
                k = data.get("k") if isinstance(data, dict) else data
                known_k[os.path.normpath(path)] = (k, data.get("status") if isinstance(data, dict) else None)

    graphs = []
    candidates = [os.path.join(ROOT, "test.col")]
    for folder, _, files in os.walk(BENCHMARKS):
        candidates += [os.path.join(folder, name) for name in files if name.endswith((".col", ".clq"))]
    for full in candidates:
        if not os.path.isfile(full):
            continue
        rel = os.path.relpath(full, ROOT)
        try:
            nodes, edges = graph_header(full)
        except (OSError, ValueError, IndexError):
            continue
        k, status = known_k.get(os.path.normpath(rel), (None, None))
        graphs.append({"path": rel, "name": os.path.basename(rel), "folder": os.path.dirname(rel) or ".",
                       "nodes": nodes, "edges": edges, "k": k, "status": status})
    graphs.sort(key=lambda g: (g["folder"], g["name"].lower()))
    return graphs


def parse_help(text):
    """The encodings an engine's --help lists (common/registry.h writes that format)."""
    specific_part, _, generic_part = text.partition("Theory-independent")
    specific_part = specific_part.split("Available Theories:", 1)[-1]
    names = lambda s: re.findall(r"[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*", s)
    generic_lines = generic_part.splitlines()
    encodings = names(generic_lines[1]) if len(generic_lines) > 1 else []
    elements_line = next((l for l in generic_lines if "element theory:" in l), "")
    elements = names(elements_line.split(":", 1)[-1])
    # "(default UF for OR and SEP, INT otherwise; ...)"
    defaults = {}
    match = re.search(r"\(default (.*?);", generic_part)
    for part in (match.group(1).split(", ") if match else []):
        element, _, users = part.partition(" ")
        if users == "otherwise":
            defaults = {**{e: element for e in encodings}, **defaults}
        else:
            defaults.update({e: element for e in users.removeprefix("for ").split(" and ")})
    return {"specific": names(specific_part), "generic": encodings, "elements": elements, "defaults": defaults}


def list_engines():
    """Each engine with its encodings, or why it is not available."""
    engines = []
    for key, engine in ENGINES.items():
        entry = {"id": key, "label": engine["label"], "about": engine["about"], "options": engine["options"]}
        program = engine["command"][-1]
        if not os.path.exists(program):
            entry["error"] = f"{os.path.relpath(program, ROOT)} not found (build it first)"
        elif engine["options"]:
            # the C++ engines describe themselves: encodings, their colors, the strategies
            listing = json.loads(subprocess.run(engine["command"] + ["--list-json"], capture_output=True, text=True).stdout)
            encodings = listing["encodings"]
            entry.update({
                "specific": [e["name"] for e in encodings if not e["generic"]],
                "generic": [e["name"] for e in encodings if e["generic"]],
                "defaults": {e["name"]: e["default_element"] for e in encodings if e["generic"]},
                "elements": listing["elements"],
                "colors": {e["name"]: e["colors"] for e in encodings},
                "strategies": listing["strategies"],
            })
        else:
            text = subprocess.run(engine["command"] + ["--help"], capture_output=True, text=True).stdout
            entry.update(parse_help(text))
            entry.update({"colors": {}, "strategies": []})
        engines.append(entry)
    return engines


def check_coloring(edges, colors):
    """Edges whose two ends got the same value (colors: node id -> printed value)."""
    return [(u, v) for u, v in edges if u in colors and v in colors and colors[u] == colors[v]]


# ---------------------------------------------------------------------------
# HTTP
# ---------------------------------------------------------------------------
class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):  # keep the terminal quiet
        pass

    def send_json(self, obj, status=200):
        body = json.dumps(obj).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        url = urlparse(self.path)
        query = parse_qs(url.query)
        if url.path == "/api/options":
            return self.send_json({"graphs": list_graphs(), "engines": list_engines()})
        if url.path == "/api/graph":
            return self.serve_graph(query.get("path", [""])[0])
        if url.path == "/api/run":
            return self.run_solver(query)
        return self.serve_static(url.path)

    def serve_static(self, path):
        name = "index.html" if path in ("", "/") else path.lstrip("/")
        full = os.path.normpath(os.path.join(STATIC, name))
        if not full.startswith(STATIC) or not os.path.isfile(full):
            self.send_error(404)
            return
        with open(full, "rb") as f:
            body = f.read()
        self.send_response(200)
        self.send_header("Content-Type", CONTENT_TYPES.get(os.path.splitext(full)[1], "application/octet-stream"))
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-cache")
        self.end_headers()
        self.wfile.write(body)

    def graph_path(self, rel):
        full = os.path.normpath(os.path.join(ROOT, rel))
        if not full.startswith(ROOT) or not os.path.isfile(full):
            return None
        return full

    def serve_graph(self, rel):
        full = self.graph_path(rel)
        if not full:
            return self.send_json({"error": "unknown graph"}, 404)
        nodes, edges = read_graph(full)
        drawable = nodes <= DRAW_MAX_NODES and len(edges) <= DRAW_MAX_EDGES
        self.send_json({"nodes": nodes, "edges": edges if drawable else None, "num_edges": len(edges)})

    # --- solver run, streamed as Server-Sent Events -------------------------
    def run_solver(self, query):
        get = lambda key, default="": query.get(key, [default])[0]
        full = self.graph_path(get("graph"))
        theory, engine_id = get("solver"), get("engine", "cvc5")
        try:
            k = int(get("k"))
            timeout = float(get("timeout") or 0)
        except ValueError:
            return self.send_json({"error": "K must be an integer"}, 400)
        engine = ENGINES.get(engine_id)
        if not full or not engine or not re.fullmatch(r"[A-Z0-9-]+", theory) or k < 1:
            return self.send_json({"error": "bad request"}, 400)
        # Solver options, NAME or NAME=VALUE: cvc5 uses names like bitblast, Z3 dotted ones
        # like sat.euf. dReal takes none.
        options = [o for o in query.get("opt", []) if o] if engine["options"] else []
        if not all(re.fullmatch(r"[a-z][a-z0-9_.-]*(=[A-Za-z0-9._+-]+)?", o) for o in options):
            return self.send_json({"error": "bad solver option"}, 400)
        # Strategies, NAME or NAME:PARAMS (the C++ engines only)
        strategy_specs = [s for s in query.get("strategy", []) if s] if engine["options"] else []
        if not all(re.fullmatch(r"[a-z][a-z0-9-]*(:[a-z0-9=,]+)?", s) for s in strategy_specs):
            return self.send_json({"error": "bad strategy"}, 400)

        binary = engine["command"]
        cmd = (binary + [theory, full, str(k), "--print-asserts", "--model"]
               + [a for o in options for a in ("--opt", o)] + [a for s in strategy_specs for a in ("--strategy", s)])

        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "close")
        self.end_headers()
        self.close_connection = True

        def send(event, data):
            self.wfile.write(f"event: {event}\ndata: {json.dumps(data)}\n\n".encode())
            self.wfile.flush()

        start = time.monotonic()
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                    bufsize=1, cwd=ROOT, env={**os.environ, "PYTHONUNBUFFERED": "1"})
        except OSError as e:
            send("failed", {"message": str(e)})
            return

        lines = queue.Queue()
        def pump(stream, tag):
            for line in stream:
                lines.put((tag, line.rstrip("\n")))
            lines.put((tag, None))
        threading.Thread(target=pump, args=(proc.stdout, "out"), daemon=True).start()
        threading.Thread(target=pump, args=(proc.stderr, "err"), daemon=True).start()

        command_shown = " ".join([os.path.relpath(binary[-1], ROOT)] + cmd[len(binary):len(binary) + 1]
                                 + [os.path.relpath(full, ROOT)] + cmd[len(binary) + 2:])
        send("start", {"command": command_shown})

        sent_asserts = total_asserts = 0
        strategy_tag = None
        in_query = False
        status, model, errors = None, None, []
        open_streams = 2
        try:
            while open_streams:
                elapsed = time.monotonic() - start
                if timeout and elapsed > timeout and proc.poll() is None:
                    proc.kill()
                    status = "TIMEOUT"
                try:
                    tag, line = lines.get(timeout=0.25)
                except queue.Empty:
                    send("tick", {"elapsed": elapsed})  # also detects a closed page (write fails)
                    continue
                if line is None:
                    open_streams -= 1
                    continue
                if tag == "err":
                    errors.append(line)
                    continue
                if line.startswith("STRATEGY-JSON "):
                    send("strategy", json.loads(line[len("STRATEGY-JSON "):]))
                    continue
                if line.startswith("STRATEGY "):
                    continue  # the human-readable twin of STRATEGY-JSON
                if line.startswith("; strategy: "):
                    strategy_tag = line[len("; strategy: "):]  # the following assertions come from it
                    continue
                if line.startswith("; ---"):
                    # opening marker -> formulas follow; closing marker -> solving starts
                    in_query = "ASSERTED" in line or "QUERY" in line
                    send("phase", {"phase": "building" if in_query else "solving"})
                    continue
                if line.startswith("(assert "):
                    total_asserts += 1
                    if sent_asserts < MAX_ASSERTS_SENT:
                        sent_asserts += 1
                        text = line[len("(assert "):-1]
                        send("assert", {"text": text, "from": strategy_tag} if strategy_tag else text)
                    elif total_asserts % 2000 == 0:
                        send("assert_count", total_asserts)
                    continue
                if in_query:
                    continue  # declarations etc. of the dReal query
                if line in ("SAT", "UNSAT", "UNKNOWN"):
                    status = line
                    send("phase", {"phase": "finishing"})
                elif line.startswith("MODEL:"):
                    model = line[len("MODEL:"):].strip()
                elif line.strip():
                    errors.append(line)
            proc.wait()
        except (BrokenPipeError, ConnectionResetError):
            proc.kill()  # the page went away or pressed Stop
            return

        elapsed = time.monotonic() - start
        result = {"status": status or ("ERROR" if proc.returncode else "UNKNOWN"), "elapsed": elapsed,
                  "asserts": total_asserts, "asserts_sent": sent_asserts, "errors": errors[-20:]}
        if model is not None:
            pairs = re.findall(r"(\S+): (.*?)(?=\s+\S+: |\s*$)", model)
            colors = {int(name[5:]): value for name, value in pairs if re.fullmatch(r"node_\d+", name)}
            result["colors"] = {str(n): v for n, v in sorted(colors.items())}
            result["extra"] = [[name, value] for name, value in pairs if not re.fullmatch(r"node_\d+", name)]
            _, edges = read_graph(full)
            bad = check_coloring(edges, colors)
            result["conflicts"] = bad[:20]
            result["num_conflicts"] = len(bad)
        try:
            send("result", result)
        except (BrokenPipeError, ConnectionResetError):
            pass


def main():
    parser = argparse.ArgumentParser(description="K-Coloring Explorer (local web UI)")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--no-browser", action="store_true", help="do not open a browser window")
    args = parser.parse_args()

    for port in range(args.port, args.port + 20):
        try:
            server = ThreadingHTTPServer(("127.0.0.1", port), Handler)
            break
        except OSError:
            continue
    else:
        sys.exit(f"No free port in {args.port}..{args.port + 19}")
    server.daemon_threads = True
    url = f"http://127.0.0.1:{port}/"
    print(f"K-Coloring Explorer running at {url}  (Ctrl+C to stop)")
    if not args.no_browser:
        threading.Timer(0.4, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


if __name__ == "__main__":
    main()
