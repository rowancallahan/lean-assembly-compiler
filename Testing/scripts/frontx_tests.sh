#!/bin/bash
# QEMU + Sail tests of every frontx entry point against executed Lean (`Testing/asm/frontx_test.py`).
# Re-emit the words and cases first when Riscv/Frontx changed:
#   lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean
set -eo pipefail
H=$(cd "$(dirname "$0")" && pwd); R=$(cd "$H/../.." && pwd); cd "$R"
N=${1:-50}
for f in $(ls Testing/asm/frontx-words/*.cases | xargs -n1 basename | sed 's/\.cases$//'); do
  python3 Testing/asm/frontx_test.py check "$N" "$f"
done
