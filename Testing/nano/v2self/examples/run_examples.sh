#!/usr/bin/env bash
# Compile every example with the self-compiled compiler B2 and run it (nanorun), then compare the output with the
# "expect" line of the program and with the reference semantics (semrun).  UNPROVEN glue, like nanorun.
# usage (from anywhere):  run_examples.sh [prog.lean ...]      default: all *.lean next to this script
#   B2=path/to/B2.bin   another compiler binary (default ../B2.bin, checked in; rebuild: ../boot/fixpoint.sh)
#   NOSEM=1             skip semrun (it needs Lean 4.29 and a built `lake build Nano.V2Self.Proof.Main.Main`)
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$D/../../../.." && pwd)
B2=${B2:-$D/../B2.bin}; T=$(mktemp -d)
cc -O2 "$D/../run/nanorun.c" -o "$T/nanorun"
hex() { od -An -v -tx1 "$1" | tr -d ' \n'; }
field() { sed -n "s/^-- $1 *(hex): *//p" "$2" | tr -d ' \n'; }
[ $# -gt 0 ] || set -- "$D"/*.lean
fail=0
for p in "$@"; do
  n=$(basename "$p" .lean)
  grep -v '^--' "$p" > "$T/$n.src"                     # the compiler has no comments: drop the `--` lines
  : > "$T/$n.in"; for b in $(sed -n 's/^-- input *(hex): *//p' "$p"); do printf "\\x$b" >> "$T/$n.in"; done
  "$T/nanorun" "$B2" "$T/$n.src" "$T/$n.bin" 2> "$T/$n.clog"       # (a) compile
  [ -s "$T/$n.bin" ] || { echo "$n: REJECTED by the compiler (empty code)"; fail=1; continue; }
  : > "$T/$n.out"; st=0
  "$T/nanorun" "$T/$n.bin" "$T/$n.in" "$T/$n.out" 2> "$T/$n.rlog" || st=$?   # (b) run
  got=$(hex "$T/$n.out"); r="exp:OK"
  [ "$got" = "$(field expect "$p")" ] || { r="exp:FAIL"; fail=1; }
  if [ -z "${NOSEM:-}" ]; then
    (cd "$ROOT" && SRC="$T/$n.src" INP="$T/$n.in" OUT="$T/$n.sem" lake env lean Testing/nano/v2self/semrun/semrun.lean)
    if cmp -s "$T/$n.out" "$T/$n.sem"; then r="$r sem:OK"; else r="$r sem:FAIL($(hex "$T/$n.sem"))"; fail=1; fi
  fi
  echo "$n: in=$(hex "$T/$n.in") out=$got exit=$st [$(sed 's/^nanorun: //' "$T/$n.rlog")] $r"
done
exit $fail
