#!/usr/bin/env bash
# bench.sh [NA_DIR] [selfdyn] : RISC-V vs rv2arm vs native A64 (run test_native.sh first). Prints markdown tables:
# examples (static words, dynamic instructions of the generated code, qemu wall time on a 400 KB input) and
# self-compile (each host build of C compiling C's source: qemu wall time; with `selfdyn` also dynamic instructions,
# slow: ~1 µs per instruction under the exec log).  PROTOTYPE, UNPROVEN glue.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$D/..; T=${1:-/tmp/claude-0/na}; C=$D/dyn_count.sh
RV="qemu-riscv64 $T/shim_rv"; A="qemu-aarch64 $T/shim_arm"
wall() { local s e; s=$(date +%s.%N); "$@" > /dev/null 2>&1 || true; e=$(date +%s.%N); echo "$e - $s" | bc | xargs printf '%.2f'; }
head -c 2000000 /dev/urandom | tr -dc 'a-f ' | head -c 400000 > "$T/big.in"
echo "| example | static RV / rv2arm / native | dynamic RV / rv2arm / native | wall s (400 KB in) RV / rv2arm / native |"
echo "|---|---|---|---|"
for p in "$V"/examples/*.lean; do
  n=$(basename "$p" .lean); grep -v '^--' "$p" > "$T/$n.src"; head -c 300 "$T/big.in" > "$T/$n.small"
  $RV "$V/B2.bin" < "$T/$n.src" > "$T/$n.rv" 2>/dev/null; $A "$T/GA_arm.bin" < "$T/$n.src" > "$T/$n.na" 2>/dev/null
  RUN="$A $V/arm/rv2arm_arm.bin" "$V/arm/rv2arm.sh" "$T/$n.rv" > "$T/$n.tr"
  s="$(( $(stat -c%s "$T/$n.rv") / 4 )) / $(( $(stat -c%s "$T/$n.tr") / 4 )) / $(( $(stat -c%s "$T/$n.na") / 4 ))"
  d="$($C rv "$T/shim_rv" "$T/$n.rv" "$T/$n.small") / $($C a64 "$T/shim_arm" "$T/$n.tr" "$T/$n.small") / $($C a64 "$T/shim_arm" "$T/$n.na" "$T/$n.small")"
  w="$(wall sh -c "$RV $T/$n.rv < $T/big.in") / $(wall sh -c "$A $T/$n.tr < $T/big.in") / $(wall sh -c "$A $T/$n.na < $T/big.in")"
  echo "| $n | $s | $d | $w |"
done
echo
echo "| self-compile (C's source) | wall s | dynamic instructions |"
echo "|---|---|---|"
for h in "RISC-V B2|$RV $V/B2.bin|rv $T/shim_rv $V/B2.bin" "rv2arm B2_arm|$A $V/arm/B2_arm.bin|a64 $T/shim_arm $V/arm/B2_arm.bin" \
         "native B2_na|$A $T/B2_na.bin|a64 $T/shim_arm $T/B2_na.bin"; do
  IFS='|' read -r name cmd dyn <<< "$h"
  w=$(wall sh -c "$cmd < $V/self_S_input.txt"); dd="-"
  [ "${2:-}" = selfdyn ] && dd=$($C $dyn "$V/self_S_input.txt")
  echo "| $name | $w | $dd |"
done
