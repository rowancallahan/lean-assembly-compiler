#!/usr/bin/env bash
# cross_native.sh [NA_DIR] : cross-hosting matrix (run test_native.sh first; PROTOTYPE, UNPROVEN glue).
# Two compilers, each in three hosted builds that must give byte-identical output on every source:
#   C  (RISC-V back end, Gen):    B2.bin on RISC-V | arm/B2_arm.bin (rv2arm) on ARM | B2_na (native) on ARM
#   CA (native back end, GenArm): GA_rv on RISC-V   | GA_tr = rv2arm(GA_rv) on ARM   | GA_arm (native) on ARM
# Sources: examples, edge programs, C's source (self_S_input.txt), CA's source (self_A_input.txt).
# Fixpoints: B2_na(C's source) = B2.bin, GA_arm(CA's source) = GA_arm.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$D/..; T=${1:-/tmp/claude-0/na}
RV="qemu-riscv64 $T/shim_rv"; A="qemu-aarch64 $T/shim_arm"
[ -s "$T/GA_tr.bin" ] || RUN="$A $V/arm/rv2arm_arm.bin" "$V/arm/rv2arm.sh" "$T/GA_rv.bin" > "$T/GA_tr.bin"
srcs=("$V"/examples/*.lean "$D"/edge/*.lean "$V/self_S_input.txt" "$D/self_A_input.txt")
fail=0; n=0
for s in "${srcs[@]}"; do
  grep -v '^--' "$s" > "$T/x.src"
  c1=$($RV "$V/B2.bin" < "$T/x.src" 2>/dev/null | sha256sum); c2=$($A "$V/arm/B2_arm.bin" < "$T/x.src" 2>/dev/null | sha256sum)
  c3=$($A "$T/B2_na.bin" < "$T/x.src" 2>/dev/null | sha256sum)
  a1=$($RV "$T/GA_rv.bin" < "$T/x.src" 2>/dev/null | sha256sum); a2=$($A "$T/GA_tr.bin" < "$T/x.src" 2>/dev/null | sha256sum)
  a3=$($A "$T/GA_arm.bin" < "$T/x.src" 2>/dev/null | sha256sum)
  n=$((n + 1))
  if [ "$c1" = "$c2" ] && [ "$c2" = "$c3" ] && [ "$a1" = "$a2" ] && [ "$a2" = "$a3" ]; then :; else
    fail=1; echo "MISMATCH $(basename "$s"): C ${c1:0:8} ${c2:0:8} ${c3:0:8}  CA ${a1:0:8} ${a2:0:8} ${a3:0:8}"; fi
done
cmp -s <($A "$T/B2_na.bin" < "$V/self_S_input.txt" 2>/dev/null) "$V/B2.bin" || { fail=1; echo "FAIL: B2_na(C) != B2.bin"; }
cmp -s <($A "$T/GA_arm.bin" < "$D/self_A_input.txt" 2>/dev/null) "$T/GA_arm.bin" || { fail=1; echo "FAIL: GA_arm(CA) != GA_arm"; }
[ $fail = 0 ] && echo "cross matrix OK: $n sources x 3 hosts x 2 compilers identical; both fixpoints hold"
exit $fail
