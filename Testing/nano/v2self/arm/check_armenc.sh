#!/usr/bin/env bash
# ArmEnc (Nano/Run/ArmEnc.lean, lake-built) = rv2arm's oracle, word for word: the same #guards as
# check_lean.sh (every distinct J instruction of B2, the examples and synth_rv.py, plus the extra forms of gen_check.py),
# with ArmBlock.blockJ replaced by ArmEnc.blockJ.  Needs: lake build Nano.Run.ArmEnc,
# riscv64-linux-gnu-gcc, qemu-riscv64(-static), python3 (the examples are compiled as in check_lean.sh).
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); R=$(cd "$D/../../../.." && pwd); V=$D/..; T=$(mktemp -d)
cd "$R"
# RUNNER=qemu (default, as check_lean.sh) or RUNNER=nanorun (C emulator, when there is no qemu user mode)
if [ "${RUNNER:-qemu}" = nanorun ]; then
  cc -O2 "$V/run/nanorun.c" -o "$T/nanorun"
  run() { "$T/nanorun" "$V/B2.bin" "$1" "$2" 2> /dev/null; }
else
  QRV=${QRV:-$(command -v qemu-riscv64-static || command -v qemu-riscv64 || true)}
  [ -n "$QRV" ] || { echo "check_armenc: no qemu-riscv64(-static); install it or set RUNNER=nanorun" >&2; exit 1; }
  riscv64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_rv.c" -o "$T/shim_rv"
  run() { "$QRV" "$T/shim_rv" "$V/B2.bin" < "$1" > "$2" 2> /dev/null; }
fi
for e in "$V"/examples/*.lean; do                      # the examples' code, compiled by B2
  grep -v '^--' "$e" > "$T/e.src"; run "$T/e.src" "$T/$(basename "$e" .lean).rv"
done
python3 "$D/synth_rv.py" > "$T/synth.rv"
python3 "$D/gen_check.py" "$V/B2.bin" "$D/rv2arm_rv.bin" "$T"/*.rv \
  | sed 's/^import Testing.nano.v2self.arm.ArmBlock$/import Nano.Run.ArmEnc/; s/^open ArmBlock CallProbe$/open ArmEnc CallProbe/' \
  > "$T/ArmEncCheck.lean"
lake env lean "$T/ArmEncCheck.lean"
echo "OK $(head -1 "$T/ArmEncCheck.lean" | grep -o '[0-9]* distinct') J instructions: ArmEnc.blockJ = rv2arm oracle"
