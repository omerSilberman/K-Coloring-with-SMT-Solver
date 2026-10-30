"""Running the dReal binary and reading its answer."""
import ctypes
import os
import signal
import subprocess

# dReal 4.21.06.2 and its libraries unpacked from .deb files (see README, "dReal").
DREAL_ROOT = os.environ.get("DREAL_ROOT", os.path.expanduser("~/dreal/root"))
DREAL_BIN = os.path.join(DREAL_ROOT, "opt/dreal/4.21.06.2/bin/dreal")
DREAL_LIBS = [
    "opt/libibex/2.7.4/lib",
    "opt/dreal/4.21.06.2/lib",
    "usr/lib/x86_64-linux-gnu",
    "usr/lib/x86_64-linux-gnu/blas",
    "usr/lib/x86_64-linux-gnu/lapack",
]


def kill_with_parent():
    # Runs in the dReal child: if this script is killed (benchmark.py's timeout), so is dReal.
    PR_SET_PDEATHSIG = 1
    ctypes.CDLL("libc.so.6", use_errno=True).prctl(PR_SET_PDEATHSIG, signal.SIGKILL)


def run_dreal(query, precision, jobs):
    env = dict(os.environ)
    libs = [os.path.join(DREAL_ROOT, p) for p in DREAL_LIBS]
    env["LD_LIBRARY_PATH"] = ":".join(libs + [env.get("LD_LIBRARY_PATH", "")]).rstrip(":")
    cmd = [DREAL_BIN, "--in", "--model", "--precision", str(precision), "--jobs", str(jobs)]
    result = subprocess.run(cmd, input=query, capture_output=True, text=True, env=env,
                            preexec_fn=kill_with_parent)
    return result.stdout, result.stderr


def parse_boxes(output):
    """`node_3 : [3.1415926535897931, 3.1415926535897936]` -> {3: (lo, hi)}."""
    boxes = {}
    for line in output.splitlines():
        if line.startswith("node_") and ":" in line:
            name, interval = line.split(":", 1)
            a, b = interval.strip().strip("[]").split(",")
            boxes[int(name.strip()[len("node_"):])] = (float(a), float(b))
    return boxes
