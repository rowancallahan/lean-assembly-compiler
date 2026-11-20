#!/usr/bin/env bash
# test_native.sh [NA_DIR] : build and check the native AArch64 back end (C/GenArm.lean).  PROTOTYPE, UNPROVEN glue.
#  1. self_A.lean (Base+Lex2+Par1+Own+Gen+GenArm, driver a31) -> B2 (RISC-V) compiles it: GA_rv.bin
#  2. GA_rv compiles self_A: GA_arm.bin (the native-ARM compiler as A64 code); GA_arm compiles self_A: must = GA_arm.bin
#  3. GA_arm compiles the RISC-V compiler's source: B2_na.bin (B2 as native A64 code); B2_na compiles it: must = B2.bin
#  4. examples/*.lean and edge/*.lean on several inputs: RISC-V vs native A64 (status + output bytes)
# Needs riscv64-linux-gnu-gcc, aarch64-linux-gnu-gcc, qemu-riscv64, qemu-aarch64.  NA_DIR default /tmp/claude-0/na.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$D/..; T=${1:-/tmp/claude-0/na}; mkdir -p "$T"
riscv64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_rv.c" -o "$T/shim_rv"
aarch64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_arm.c" -o "$T/shim_arm"
RV="qemu-riscv64 $T/shim_rv"; A="qemu-aarch64 $T/shim_arm"
python3 "$D/build_self_A.py"
$RV "$V/B2.bin" < "$D/self_A_input.txt" > "$T/GA_rv.bin" 2>/dev/null
[ -s "$T/GA_rv.bin" ] || { echo "FAIL: B2 rejects self_A"; exit 1; }
$RV "$T/GA_rv.bin" < "$D/self_A_input.txt" > "$T/GA_arm.bin" 2>/dev/null
$A "$T/GA_arm.bin" < "$D/self_A_input.txt" > "$T/GA_arm2.bin" 2>/dev/null
cmp "$T/GA_arm.bin" "$T/GA_arm2.bin" && echo "fixpoint: GA_arm(self_A) = GA_rv(self_A) ($(stat -c%s "$T/GA_arm.bin") bytes)"
$A "$T/GA_arm.bin" < "$V/self_S_input.txt" > "$T/B2_na.bin" 2>/dev/null
$A "$T/B2_na.bin" < "$V/self_S_input.txt" > "$T/B2_from_na.bin" 2>/dev/null
cmp "$T/B2_from_na.bin" "$V/B2.bin" && echo "B2_na (native A64 B2, $(stat -c%s "$T/B2_na.bin") bytes) compiles C's source to B2.bin exactly"
fail=0
for p in "$V"/examples/*.lean "$D"/edge/*.lean; do
  for n in 0 1 7 300 70000; do
    head -c $n /dev/urandom > "$T/in"
    r=$(TMPD=$(mktemp -d) SHIMS=$T "$D/diff_run.sh" "$A $T/GA_arm.bin" "$p" "$T/in") || { fail=1; echo "FAIL $p ($n bytes): $r"; }
  done
  echo "$(basename "$p"): $r"
done
[ $fail = 0 ] && echo "all OK"
