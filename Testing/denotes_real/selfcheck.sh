#!/bin/bash
# con-leche checks the bridge itself (DENOTES_SPIKE.md §12.4): export the top bridge theorems with lean4export
# (v4.35.0-rc3, built in bridge/_tmp/lean4export) from bridge/'s build, then run con-leche --verified on the export.
set -e
cd "$(dirname "$0")/../../bridge"
L=~/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin
X=$PWD/_tmp/lean4export/.lake/build/bin/lean4export
mkdir -p _tmp/selfcheck
time env LEAN_PATH=$L/../lib/lean:$PWD/.lake/build/lib/lean:$PWD/.lake/packages/con-leche/.lake/build/lib/lean PATH=$L:$PATH \
  timeout 3000 $X Bridge.Main -- Bridge.nano_tiny Bridge.nano_input Bridge.nano_ite Bridge.nano_arith Bridge.nano_calls \
  Bridge.nano_len Bridge.nano_let Bridge.nano_loop Bridge.nano_pair Bridge.nano_sub Bridge.Real.LamDemo.lam_regime_g \
  > _tmp/selfcheck/all.ndjson
wc -lc < _tmp/selfcheck/all.ndjson
time timeout 6000 .lake/packages/con-leche/.lake/build/bin/con-leche _tmp/selfcheck/all.ndjson 2>&1 | grep -v "slowest\|pool"
