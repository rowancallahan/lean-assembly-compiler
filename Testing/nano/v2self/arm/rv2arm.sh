#!/bin/sh
# rv2arm.sh prog_rv.bin > prog_arm.bin : runs the nano translator once per chunk of 32000 RV words (UNPROVEN glue).
# RUN = a command that runs the translator from stdin to stdout; default: shim_arm + rv2arm_arm.bin next to this script.
# Linux without ARM: RUN="nanorun rv2arm_rv.bin /dev/stdin /dev/stdout".
set -eu
D=$(dirname "$0"); RUN=${RUN:-"$D/shim_arm $D/rv2arm_arm.bin"}
n=$(wc -c < "$1"); w=$((n / 4))
[ $((n % 4)) -eq 0 ] || { echo "rv2arm: size not a multiple of 4" >&2; exit 1; }
T=$(mktemp); L=$(mktemp); I=$(mktemp); c=0
while [ $((c * 32000)) -lt $w ]; do
  { printf "$(printf '\\%03o\\%03o\\%03o\\%03o' $((c & 255)) $((c >> 8 & 255)) 0 0)"; cat "$1"; } > "$I"
  $RUN < "$I" > "$T" 2> "$L" || true
  k=$((w - c * 32000)); [ $k -le 32000 ] || k=32000
  [ "$(wc -c < "$T")" -eq $((16 * k)) ] || { echo "rv2arm: chunk $c failed (invalid input?)" >&2; cat "$L" >&2; exit 1; }
  cat "$T"; c=$((c + 1))
done
rm -f "$T" "$L" "$I"
