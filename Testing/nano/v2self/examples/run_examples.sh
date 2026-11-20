#!/usr/bin/env bash
# Compile every example with the self-compiled compiler B2 and run it, both on QEMU's RISC-V model
# (qemu-riscv64 + run/shim/shim_rv.c), then compare the output with the "expect" line of the program and with the
# reference semantics (semrun).  UNPROVEN glue, like the shims.
# usage (from anywhere):  run_examples.sh [prog.lean ...]      default: all *.lean next to this script
#   B2=path/to/B2.bin   another compiler binary (default ../B2.bin, checked in; rebuild: ../boot/fixpoint.sh)
#   NOSEM=1             skip semrun (it needs Lean 4.29 and a built `lake build Nano.V2Self.Proof.Main.Main`)
#   NANORUN=1           use the interpreter run/nanorun.c instead of QEMU (no riscv64 toolchain or QEMU needed)
# Needs (default): riscv64-linux-gnu-gcc and qemu-riscv64 (Debian/Ubuntu: gcc-riscv64-linux-gnu qemu-user-static).
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$D/../../../.." && pwd)
B2=${B2:-$D/../B2.bin}; T=$(mktemp -d)
if [ -n "${NANORUN:-}" ]; then
  cc -O2 "$D/../run/nanorun.c" -o "$T/nanorun"
else
  QRV=${QRV:-$(command -v qemu-riscv64-static || command -v qemu-riscv64)}
  riscv64-linux-gnu-gcc -O2 -static "$D/../run/shim/shim_rv.c" -o "$T/shim_rv"
fi
# rv CODE IN OUT LOG: run RISC-V code (QEMU, or nanorun with NANORUN=1); the status line goes to LOG
rv() {
  if [ -n "${NANORUN:-}" ]; then "$T/nanorun" "$1" "$2" "$3" 2> "$4"
  else "$QRV" "$T/shim_rv" "$1" < "$2" > "$3" 2> "$4"; fi
}
hex() { od -An -v -tx1 "$1" | tr -d ' \n'; }
field() { sed -n "s/^-- $1 *(hex): *//p" "$2" | tr -d ' \n'; }
[ $# -gt 0 ] || set -- "$D"/*.lean
fail=0
for p in "$@"; do
  n=$(basename "$p" .lean)
  grep -v '^--' "$p" > "$T/$n.src"                     # the compiler has no comments: drop the `--` lines
  : > "$T/$n.in"; for b in $(sed -n 's/^-- input *(hex): *//p' "$p"); do printf "\\x$b" >> "$T/$n.in"; done
  rv "$B2" "$T/$n.src" "$T/$n.bin" "$T/$n.clog" || true                  # (a) compile
  [ -s "$T/$n.bin" ] || { echo "$n: REJECTED by the compiler (empty code)"; fail=1; continue; }
  : > "$T/$n.out"; st=0
  rv "$T/$n.bin" "$T/$n.in" "$T/$n.out" "$T/$n.rlog" || st=$?             # (b) run
  got=$(hex "$T/$n.out"); r="exp:OK"
  [ "$got" = "$(field expect "$p")" ] || { r="exp:FAIL"; fail=1; }
  if [ -z "${NOSEM:-}" ]; then
    (cd "$ROOT" && SRC="$T/$n.src" INP="$T/$n.in" OUT="$T/$n.sem" lake env lean Testing/nano/v2self/semrun/semrun.lean)
    if cmp -s "$T/$n.out" "$T/$n.sem"; then r="$r sem:OK"; else r="$r sem:FAIL($(hex "$T/$n.sem"))"; fail=1; fi
  fi
  echo "$n: in=$(hex "$T/$n.in") out=$got exit=$st [$(sed 's/^\(nanorun\|shim_rv\): //' "$T/$n.rlog")] $r"
done
exit $fail
