#!/usr/bin/env bash
# compile.sh prog.lean > prog.a64 : compile a nano program to NATIVE AArch64 code with the native-ARM compiler GA_arm.bin
# (C with the GenArm back end, itself native A64), on ARM: Apple Silicon / ARM64 Linux natively, x86-64 Linux under
# qemu-aarch64 (needs aarch64-linux-gnu-gcc for the shim). PROTOTYPE, UNPROVEN: nothing here is proved.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
[ $# -eq 1 ] || { echo "usage: compile.sh prog.lean > prog.a64" >&2; exit 2; }
S=$D/shim_arm
if [ ! -x "$S" ]; then
  case $(uname -m) in
    arm64|aarch64) cc -O2 "$D/../run/shim/shim_arm.c" -o "$S" ;;
    *) aarch64-linux-gnu-gcc -O2 -static "$D/../run/shim/shim_arm.c" -o "$S" ;;
  esac
fi
case $(uname -m) in arm64|aarch64) Q="" ;; *) Q=$(command -v qemu-aarch64-static || command -v qemu-aarch64) ;; esac
grep -v '^--' "$1" > "$T/src"                                    # the compiler accepts no comments
$Q "$S" "$D/GA_arm.bin" < "$T/src" > "$T/out" 2> "$T/log"
[ -s "$T/out" ] || { echo "compile.sh: rejected by the compiler: $1" >&2; exit 1; }
cat "$T/out"
