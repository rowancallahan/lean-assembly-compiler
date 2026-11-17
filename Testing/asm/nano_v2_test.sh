#!/bin/bash
# nano v2 increment 1 (`if` + comparisons, Nano/V2Gen.lean) on QEMU + Sail in the StartCorrect convention: emit with
# Testing/asm/emit_nano_v2.lean, then each program's 8 cases with ir_test.py (work = memoryNeeded = 8 * depth, and one
# byte less: a0 = -1), aligned and with misaligned input / output blocks (MIS).  Removes Testing/asm/ctest.
set -eo pipefail
cd "$(dirname "$0")/../.."; export PATH=$HOME/.elan/bin:$PATH
mkdir -p Testing/asm/ir-words
(ulimit -s unlimited; lake env lean --tstack=4000000 Testing/asm/emit_nano_v2.lean)
n=0
for f in Testing/asm/ir-words/nanov2_*.words; do
  name=$(basename "$f" .words)
  for mis in 0,0 1,3 5,7; do MIS=$mis python3 Testing/asm/ir_test.py check 8 "$name" > /dev/null; n=$((n + 8)); done
done
rm -rf Testing/asm/ctest
echo "nano v2 stack generator: $n program x input pairs ok (QEMU == Sail == Lean, each also at memoryNeeded - 1)"
