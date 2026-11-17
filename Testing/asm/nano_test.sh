#!/bin/bash
# nano code generator on QEMU + Sail: emit (Testing/asm/emit_nano.lean), then every program's 8 cases with
# Testing/asm/ir_test.py (memoryNeeded and memoryNeeded - 1); removes Testing/asm/ctest afterwards.
set -eo pipefail
cd "$(dirname "$0")/../.."; export PATH=$HOME/.elan/bin:$PATH
lake env lean Testing/asm/emit_nano.lean
n=0
for f in Testing/asm/ir-words/nano_*.words; do
  name=$(basename "$f" .words); python3 Testing/asm/ir_test.py check 8 "$name"; n=$((n + 8))
done
rm -rf Testing/asm/ctest
echo "nano: $n program x input pairs ok"
