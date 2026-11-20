#!/usr/bin/env bash
# Lean check of the draft ArmBlock.lean (UNPROVEN glue around a draft statement): elaborates it against Spec.Top and
# Machine/Call (oleans built into a temp dir, no lake), then runs the generated #guards: blockJ = rv2arm.py's block on
# every distinct J instruction of B2, the translator and the examples.  Needs: lean 4.29 (repo toolchain), cc, python3.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); R=$(cd "$D/../../../.." && pwd); V=$D/..; T=$(mktemp -d)
export LEAN_PATH=$T
mkdir -p "$T/Spec" "$T/Nano/V2Self/Proof/Machine" "$T/Testing/nano/v2self/arm"
cd "$R"
lean -o "$T/Spec/Machines.olean" Spec/Machines.lean
lean -o "$T/Spec/Top.olean" Spec/Top.lean
lean -o "$T/Nano/V2Self/Proof/Machine/Call.olean" Nano/V2Self/Proof/Machine/Call.lean > /dev/null
lean -o "$T/Testing/nano/v2self/arm/ArmBlock.olean" "$D/ArmBlock.lean"
cc -O2 "$V/run/nanorun.c" -o "$T/nanorun"
for e in "$V"/examples/*.lean; do
  grep -v '^--' "$e" > "$T/e.src"; "$T/nanorun" "$V/B2.bin" "$T/e.src" "$T/$(basename "$e" .lean).rv" 2> /dev/null
done
python3 "$D/synth_rv.py" > "$T/synth.rv"
python3 "$D/gen_check.py" "$V/B2.bin" "$D/rv2arm_rv.bin" "$T"/*.rv > "$T/ArmBlockCheck.lean"
lean "$T/ArmBlockCheck.lean"
echo "OK ArmBlock.lean elaborates; $(head -1 "$T/ArmBlockCheck.lean" | grep -o '[0-9]* distinct') J instructions: blockJ = oracle"
