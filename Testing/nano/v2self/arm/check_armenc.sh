#!/usr/bin/env bash
# ArmEnc (Nano/V2Self/Proof/Machine/ArmEnc.lean, lake-built) = rv2arm's oracle, word for word: the same #guards as
# check_lean.sh (every distinct J instruction of B2, the examples and synth_rv.py, plus the extra forms of gen_check.py),
# with ArmBlock.blockJ replaced by ArmEnc.blockJ.  Needs: lake build Nano.V2Self.Proof.Machine.ArmEnc, cc, python3.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); R=$(cd "$D/../../../.." && pwd); V=$D/..; T=$(mktemp -d)
cd "$R"
cc -O2 "$V/run/nanorun.c" -o "$T/nanorun"
for e in "$V"/examples/*.lean; do
  grep -v '^--' "$e" > "$T/e.src"; "$T/nanorun" "$V/B2.bin" "$T/e.src" "$T/$(basename "$e" .lean).rv" 2> /dev/null
done
python3 "$D/synth_rv.py" > "$T/synth.rv"
python3 "$D/gen_check.py" "$V/B2.bin" "$D/rv2arm_rv.bin" "$T"/*.rv \
  | sed 's/^import Testing.nano.v2self.arm.ArmBlock$/import Nano.V2Self.Proof.Machine.ArmEnc/; s/^open ArmBlock CallProbe$/open ArmEnc CallProbe/' \
  > "$T/ArmEncCheck.lean"
lake env lean "$T/ArmEncCheck.lean"
echo "OK $(head -1 "$T/ArmEncCheck.lean" | grep -o '[0-9]* distinct') J instructions: ArmEnc.blockJ = rv2arm oracle"
