#!/usr/bin/env bash
# cross_check.sh: RISC-V and ARM (both under QEMU) build each other's compiler; every result must equal the self-compile.
# Needs riscv64-linux-gnu-gcc, aarch64-linux-gnu-gcc, qemu-riscv64, qemu-aarch64. UNPROVEN glue check.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$D/..; T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
QR=$(command -v qemu-riscv64-static || command -v qemu-riscv64); QA=$(command -v qemu-aarch64-static || command -v qemu-aarch64)
riscv64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_rv.c" -o "$T/srv"
aarch64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_arm.c" -o "$T/sarm"
RV() { "$QR" "$T/srv" "$@" 2>/dev/null; }                      # run RISC-V code
AR() { "$QA" "$T/sarm" "$@" 2>/dev/null; }                     # run ARM code
S=$V/self_S_input.txt; grep -v '^--' "$D/rv2arm.lean" > "$T/tr.src"
fail=0; eq() { cmp -s "$1" "$2" && echo "OK   $3" || { echo "FAIL $3"; fail=1; }; }

# 1. compilers compile the compiler (output is RISC-V code = B2)
RV "$V/B2.bin"      < "$S" > "$T/b2_on_rv";   eq "$T/b2_on_rv"  "$V/B2.bin" "RISC-V compiler on RISC-V -> B2 (self)"
AR "$D/B2_arm.bin"  < "$S" > "$T/b2_on_arm";  eq "$T/b2_on_arm" "$V/B2.bin" "ARM compiler on ARM -> B2 (cross ARM->RISC-V)"
# 2. both compile the translator identically
RV "$V/B2.bin"     < "$T/tr.src" > "$T/tr_rv_a"; AR "$D/B2_arm.bin" < "$T/tr.src" > "$T/tr_rv_b"
eq "$T/tr_rv_a" "$D/rv2arm_rv.bin" "translator compiled on RISC-V = rv2arm_rv.bin"
eq "$T/tr_rv_b" "$D/rv2arm_rv.bin" "translator compiled on ARM    = rv2arm_rv.bin"
# 3. translate the compiler to ARM on each machine
RUN="$QR $T/srv $D/rv2arm_rv.bin"  "$D/rv2arm.sh" "$T/b2_on_rv"  > "$T/arm_from_rv" 2>/dev/null
RUN="$QA $T/sarm $D/rv2arm_arm.bin" "$D/rv2arm.sh" "$T/b2_on_arm" > "$T/arm_from_arm" 2>/dev/null
eq "$T/arm_from_rv"  "$D/B2_arm.bin" "ARM compiler built on RISC-V = B2_arm.bin (cross RISC-V->ARM)"
eq "$T/arm_from_arm" "$D/B2_arm.bin" "ARM compiler built on ARM    = B2_arm.bin (self)"
# 4. the cross-built compilers work: next generation is identical
AR "$T/arm_from_rv" < "$S" > "$T/g2"; eq "$T/g2" "$V/B2.bin" "ARM compiler built on RISC-V compiles itself -> B2"
RUN="$QA $T/sarm $D/rv2arm_arm.bin" "$D/rv2arm.sh" "$T/g2" > "$T/g2arm" 2>/dev/null
eq "$T/g2arm" "$D/B2_arm.bin" "second generation ARM compiler = B2_arm.bin (fixpoint)"
exit $fail
