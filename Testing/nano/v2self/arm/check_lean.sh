#!/usr/bin/env bash
# Lean check of the draft ArmBlock.lean (UNPROVEN glue around a draft statement): elaborates it against Spec.Top and
# Machine/Call (oleans built into a temp dir, no lake), then runs the generated #guards: blockJ = rv2arm.py's block on
# every distinct J instruction of B2, the translator, the examples and synth_rv.py's program.
# Needs: lean 4.29 (repo toolchain), riscv64-linux-gnu-gcc, qemu-riscv64(-static), python3.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); R=$(cd "$D/../../../.." && pwd); V=$D/..; T=$(mktemp -d)
export LEAN_PATH=$T
mkdir -p "$T/Spec" "$T/Nano/V2Self/Proof/Machine" "$T/Testing/nano/v2self/arm"
cd "$R"
lean -o "$T/Spec/Machines.olean" Spec/Machines.lean
lean -o "$T/Spec/Top.olean" Spec/Top.lean
lean -o "$T/Nano/V2Self/Proof/Machine/Call.olean" Nano/V2Self/Proof/Machine/Call.lean > /dev/null
lean -o "$T/Testing/nano/v2self/arm/ArmBlock.olean" "$D/ArmBlock.lean"
QRV=${QRV:-$(command -v qemu-riscv64-static || command -v qemu-riscv64)}
riscv64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_rv.c" -o "$T/shim_rv"
for e in "$V"/examples/*.lean; do                      # the examples' code, compiled by B2 on qemu-riscv64
  grep -v '^--' "$e" > "$T/e.src"; "$QRV" "$T/shim_rv" "$V/B2.bin" < "$T/e.src" > "$T/$(basename "$e" .lean).rv" 2> /dev/null
done
python3 "$D/synth_rv.py" > "$T/synth.rv"
python3 "$D/gen_check.py" "$V/B2.bin" "$D/rv2arm_rv.bin" "$T"/*.rv > "$T/ArmBlockCheck.lean"
lean "$T/ArmBlockCheck.lean"
echo "OK ArmBlock.lean elaborates; $(head -1 "$T/ArmBlockCheck.lean" | grep -o '[0-9]* distinct') J instructions: blockJ = oracle"
