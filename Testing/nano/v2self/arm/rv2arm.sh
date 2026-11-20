#!/bin/sh
# rv2arm.sh prog_rv.bin > prog_arm.bin : runs the nano translator once per chunk of CHUNK_WORDS RV words (UNPROVEN glue).
# RUN = a command that runs the translator from stdin to stdout. Default: the ARM translator rv2arm_arm.bin with
# shim_arm next to this script, natively on an ARM64 host, else under qemu-aarch64 (shim_arm then a static
# aarch64-linux-gnu-gcc build). Bootstrap with the RISC-V translator: RUN="qemu-riscv64 shim_rv rv2arm_rv.bin".
set -eu
D=$(dirname "$0")
if [ -z "${RUN:-}" ]; then
  case $(uname -m) in
    arm64|aarch64) RUN="$D/shim_arm $D/rv2arm_arm.bin" ;;
    *) Q=$(command -v qemu-aarch64-static || command -v qemu-aarch64) \
         || { echo "rv2arm: not an ARM64 host and no qemu-aarch64; set RUN" >&2; exit 1; }
       RUN="$Q $D/shim_arm $D/rv2arm_arm.bin" ;;
  esac
fi
Z=$(sed -n 's/^def z0 : UInt64 := \([0-9]*\)$/\1/p' "$D/rv2arm.lean")   # CHUNK_WORDS, from the translator source
[ -n "$Z" ] || { echo "rv2arm: CHUNK_WORDS (def z0) not found in $D/rv2arm.lean" >&2; exit 1; }
n=$(wc -c < "$1"); w=$((n / 4))
[ $((n % 4)) -eq 0 ] || { echo "rv2arm: size not a multiple of 4" >&2; exit 1; }
T=$(mktemp); L=$(mktemp); I=$(mktemp); c=0
while [ $((c * Z)) -lt $w ]; do
  { printf "$(printf '\\%03o\\%03o\\%03o\\%03o' $((c & 255)) $((c >> 8 & 255)) 0 0)"; cat "$1"; } > "$I"
  $RUN < "$I" > "$T" 2> "$L" || true
  k=$((w - c * Z)); [ $k -le $Z ] || k=$Z
  [ "$(wc -c < "$T")" -eq $((16 * k)) ] || { echo "rv2arm: chunk $c failed (invalid input?)" >&2; cat "$L" >&2; exit 1; }
  cat "$T"; c=$((c + 1))
done
rm -f "$T" "$L" "$I"
