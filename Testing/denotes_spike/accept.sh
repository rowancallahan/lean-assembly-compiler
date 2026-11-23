#!/usr/bin/env bash
# usage: accept.sh File.lean   (core-Lean-only file; theorems/defs in it get exported)
# env: LEAN4EXPORT (path to lean4export binary), CONLECHE (path to con-leche binary)
set -euo pipefail
: "${LEAN4EXPORT:?}" "${CONLECHE:?}"
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$PATH"
f=$(realpath "$1"); d=$(mktemp -d); m=$(basename "$f" .lean)
cp "$f" "$d/$m.lean"
(cd "$d" && lean -o "$m.olean" "$m.lean")
t0=$(date +%s.%N)
(cd "$d" && LEAN_PATH="$d:$(lean --print-libdir)" "$LEAN4EXPORT" "$m" > "$m.ndjson")
t1=$(date +%s.%N)
out=$( { /usr/bin/time -f "maxrss_kb=%M" "$CONLECHE" --verified "$d/$m.ndjson"; } 2>&1 ) && st=ACCEPTED || st=REJECTED
t2=$(date +%s.%N)
echo "$out"
echo "$st file=$m export_s=$(echo "$t1-$t0"|bc) check_s=$(echo "$t2-$t1"|bc) ndjson_bytes=$(stat -c%s "$d/$m.ndjson")"
[ "$st" = ACCEPTED ]
