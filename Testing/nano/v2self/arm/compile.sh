#!/usr/bin/env bash
# compile.sh prog.lean > prog.arm : compile a nano Lean program to ARM machine code, ON ARM. UNPROVEN glue.
# Apple Silicon Mac: native. Linux x86-64: needs aarch64-linux-gnu-gcc + qemu-aarch64.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
[ $# -eq 1 ] || { echo "usage: compile.sh prog.lean > prog.arm" >&2; exit 2; }
if [ ! -x "$D/shim_arm" ]; then
  case $(uname -m) in
    arm64|aarch64) cc -O2 "$D/../run/shim/shim_arm.c" -o "$D/shim_arm" ;;
    *) aarch64-linux-gnu-gcc -O2 -static "$D/../run/shim/shim_arm.c" -o "$D/shim_arm" ;;
  esac
fi
case $(uname -m) in arm64|aarch64) Q="" ;; *) Q=$(command -v qemu-aarch64-static || command -v qemu-aarch64) ;; esac
grep -v '^--' "$1" > "$T/src"                                   # the compiler accepts no comments
$Q "$D/shim_arm" "$D/B2_arm.bin" < "$T/src" > "$T/rv" 2> "$T/log" # the compiler, running on ARM: Lean -> RISC-V code
[ -s "$T/rv" ] || { echo "compile.sh: rejected by the compiler: $1" >&2; exit 1; }
"$D/rv2arm.sh" "$T/rv"                                          # RISC-V code -> ARM code (nano translator, on ARM)
