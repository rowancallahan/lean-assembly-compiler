#!/usr/bin/env bash
# Compile each example here AS IS (no comment stripping) with B2 (default ../B2.bin) under nanorun and compare the output
# with its "expect" line.  Each example may give `-- strip: <file>`: then the stripped variant is compiled by the OLD
# compiler OLDB2 too (if set) and both codes must be byte-identical.  usage: run_syntax.sh [prog.lean ...]
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); B2=${B2:-$D/../B2.bin}; T=$(mktemp -d)
cc -O2 "$D/../run/nanorun.c" -o "$T/nanorun"
hex() { od -An -v -tx1 "$1" | tr -d ' \n'; }
field() { sed -n "s/^-- $1 *(hex): *//p" "$2" | tr -d ' \n'; }
[ $# -gt 0 ] || set -- "$D"/*.lean
fail=0
for p in "$@"; do
  n=$(basename "$p" .lean)
  : > "$T/$n.in"; for b in $(sed -n 's/^-- input *(hex): *//p' "$p"); do printf "\\x$b" >> "$T/$n.in"; done
  "$T/nanorun" "$B2" "$p" "$T/$n.bin" ${WORK:-120} 2> "$T/$n.clog" || true   # match needs about 8 MiB more than 80
  [ -s "$T/$n.bin" ] || { echo "$n: REJECTED"; fail=1; continue; }
  : > "$T/$n.out"; "$T/nanorun" "$T/$n.bin" "$T/$n.in" "$T/$n.out" 2> "$T/$n.rlog" || true
  got=$(hex "$T/$n.out"); r=OK; [ "$got" = "$(field expect "$p")" ] || { r=FAIL; fail=1; }
  echo "$n: out=$got [$(sed 's/^nanorun: //' "$T/$n.rlog")] $r"
done
exit $fail
