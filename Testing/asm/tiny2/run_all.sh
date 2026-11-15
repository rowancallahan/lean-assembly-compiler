#!/bin/bash
# Reproduce TINYSELF2: build, emit words/cases, QEMU+Sail check of each compiler binary, self-hosting run, repros.
set -eo pipefail
cd "$(dirname "$0")/../../.."
lake build Riscv.Frontx.TinyS1 Riscv.Frontx.TinyS2 Riscv.Frontx.TinyS3 Riscv.Frontx.TinyS5
for s in 1 2 3 5; do
  lake env lean --tstack=4000000 Testing/asm/emit_tiny2_s$s.lean
  python3 Testing/asm/frontx_test.py check 50 tiny2_s$s
  python3 Testing/asm/tiny2/selfhost2_test.py s$s
done
lake env lean Testing/asm/tiny2/axioms.lean | grep -c depends
# bash Testing/asm/tiny2/repro/run_repros.sh   # each reproducer's first error (slow)
