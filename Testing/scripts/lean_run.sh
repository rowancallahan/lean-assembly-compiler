#!/usr/bin/env bash
# lean_run.sh FILE.lean ARGS... : `lean --run FILE ARGS` with the repo's modules on the path.
# With the project's dependencies present this is `lake env lean --run`. Without them (e.g. no ../deps/sail-riscv-lean)
# it compiles only FILE's import closure of repo modules with plain `lean -o` into $LEAN_RUN_CACHE (default
# ~/.cache/lean_run/<toolchain>) and runs it there; core modules come from the toolchain. Fails loudly either way.
set -euo pipefail
R=$(cd "$(dirname "$0")/../.." && pwd); cd "$R"
export PATH=$HOME/.elan/bin:$PATH
F=$1; shift
if lake env true > /dev/null 2>&1; then exec lake env lean --tstack=1000000 --run "$F" "$@"; fi
C=${LEAN_RUN_CACHE:-$HOME/.cache/lean_run/$(tr -c 'a-zA-Z0-9.' _ < lean-toolchain)}; mkdir -p "$C"
python3 - "$F" "$C" <<'PY' >&2
import os, re, subprocess, sys
f, c = sys.argv[1:3]; done = set()
def path(m): return m.replace('.', '/') + '.lean'
def build(m, src):
    if m in done: return
    done.add(m)
    for i in re.findall(r'^import\s+(\S+)', open(src).read(), re.M):
        if os.path.exists(path(i)): build(i, path(i))
    if m is None: return
    o = os.path.join(c, path(m)[:-5] + '.olean')
    if os.path.exists(o) and os.path.getmtime(o) >= os.path.getmtime(src): return
    os.makedirs(os.path.dirname(o), exist_ok=True)
    print('lean_run: building', m, flush=True)
    subprocess.run(['lean', '-o', o, src], check=True, env=dict(os.environ, LEAN_PATH=c), stdout=subprocess.DEVNULL)
build(None, f)
PY
LEAN_PATH=$C exec lean --tstack=1000000 --run "$F" "$@"
