#!/bin/bash
# runs every reproducer (each is a standalone file importing Riscv.Frontx.IndCmd) and prints its first error line
cd "$(dirname "$0")/../../../.."
for f in Testing/asm/tiny2/repro/r*.lean; do
  echo "== $(basename $f)"
  timeout 900 lake env lean --tstack=4000000 "$f" 2>&1 | grep -E "error|frontx_ind:" | head -2 | cut -c1-170
done
