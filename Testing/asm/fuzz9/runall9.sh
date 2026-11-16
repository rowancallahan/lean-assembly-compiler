#!/bin/bash
# usage: runall9.sh LOG   (QEMU: seeds 21, 22 x 150 cases + big cases for every entry; 3 jobs in parallel)
cd "$(dirname "$0")/../../.."; export PATH=$HOME/.elan/bin:$PATH
E="expr_hasfvar expr_closed0 expr_inst1 expr_sizef expr_scopedd expr_isforalle expr_getappfn expr_piresult expr_fvartyped expr_numargs expr_islit tinyr1 tinyr2 tinyr3 tinyr5 $(ls Testing/asm/frontx-words | grep '^hof_.*words' | sed 's/.words//' | tr '\n' ' ')"
for e in $E; do
  for s in 21 22; do echo "$e $s 150"; done
  echo "$e 23 8 big"
done | xargs -P3 -L1 bash -c 'WSUF=_$$ python3 Testing/asm/fuzz9/fuzz9.py $0 $1 $2 qemu $3 2>&1 | grep -E "^FAIL|ok on|Error|assert" | cut -c1-400' > "$1"
