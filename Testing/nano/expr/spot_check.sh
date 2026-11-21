#!/usr/bin/env bash
# spot_check.sh [SEED] [N] : the Expr spot check (Testing/notes/EXPR.md §5) on C's own source, the examples
# (comment lines dropped, as run_examples.sh) and N fuzz programs of nanogen.py SEED (default 1, 300).
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$D/../v2self; W=$(mktemp -d)
echo "C source:"; "$D/run_check.py" "$V/self_S_input.txt" | tail -1
mkdir -p "$W/ex"; for f in "$V"/examples/*.lean; do grep -v '^--' "$f" > "$W/ex/$(basename "$f" .lean).src"; done
echo "examples:"; "$D/run_check.py" "$W"/ex/*.src | tail -1
mkdir -p "$W/fz"; python3 "$V/fuzz/nanogen.py" "${1:-1}" "${2:-300}" "$W/fz"
echo "fuzz (seed ${1:-1}, ${2:-300} programs):"; "$D/run_check.py" "$W"/fz/*.src > "$W/fz.out" || true
tail -1 "$W/fz.out"; ! grep -q '^other' "$W/fz.out"
