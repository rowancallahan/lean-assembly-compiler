#!/bin/bash
# Patch opencompl/sail-riscv-lean @51c635c (built for Lean 4.29.0) to build on Lean 4.34.1.
# Usage: Riscv/gen/patch_434.sh <path to sail-riscv-lean checkout>. Notes: Riscv/gen/DIFFS.md
set -euo pipefail
D=$1
G=$(cd "$(dirname "$0")" && pwd)
test "$(git -C "$D" rev-parse HEAD)" = 51c635c460125ac87955d061fcd902ce03b8011f
test -z "$(git -C "$D" status --porcelain -- LeanRV64D lakefile.toml lean-toolchain)"
cd "$D"
# 1. toolchain
echo 'leanprover/lean4:v4.34.1' > lean-toolchain
# 2. 4.29 default for the do elaborator (4.34 flipped it to false)
sed -i 's/^leanOptions.weak.linter.style.nameCheck = false$/&\nleanOptions.backward.do.legacy = true/' lakefile.toml
grep -qx 'leanOptions.backward.do.legacy = true' lakefile.toml
# 3. `assert` is a do-element keyword in 4.34: spell the call as the constant it resolved to on 4.29
n0=$(grep -rcP '(?<![\w.])assert(?![\w!])' LeanRV64D | awk -F: '{s+=$2} END{print s}')
test "$n0" = 1257  # lines: 1255 do-statements, 1 `then assert`, the definition
sed -i -E 's/^(\s*)assert /\1LeanRV64D.assert /' LeanRV64D/*.lean
sed -i 's/^      then assert (hart_is_active/      then LeanRV64D.assert (hart_is_active/' LeanRV64D/Step.lean
# only the definition itself is left
test "$(grep -rP '(?<![\w.])assert(?![\w!])' LeanRV64D | grep -v '"loop dummy assert"$')" = 'LeanRV64D/SpecializationV1.lean:abbrev assert (p : Bool) (s : String) : SailM Unit := PreSail.assert p s'
test "$(grep -rc 'LeanRV64D\.assert ' LeanRV64D | awk -F: '{s+=$2} END{print s}')" = 1256
# 4. `(← do S)` -> `(← (do S))`: 4.34 parses `do S` after `←` as a do-element, which the legacy elaborator rejects
test "$(grep -roP '\(← do\b' LeanRV64D | wc -l)" = 2005
test "$(python3 "$G"/wrap_nested_do.py LeanRV64D/*.lean | awk -F'\t' '{s+=$2} END{print s}')" = 2005
test "$(grep -roP '\(← \(do\b' LeanRV64D | wc -l)" = 2005
echo patched
