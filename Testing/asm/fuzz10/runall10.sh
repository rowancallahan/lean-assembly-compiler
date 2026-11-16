#!/bin/bash
# usage: runall10.sh MODE   MODE: seed21 | seed22 | big | sail   (Lean 4.29 on PATH; qemu-system-riscv64; riscv64-linux-gnu-gcc; Sail at the path in fuzz10.py)
# P entries in parallel (default 3). One result line (or the failure) per entry, appended to results/<MODE>.txt
cd "$(dirname "$0")/../../.."; export PATH=$(ls -d /tmp/leandl/x/*/bin):$PATH; export MODE=$1
mkdir -p Testing/asm/fuzz10/results
one() {
  f=$1; export WSUF=$MODE-$f
  case $MODE in
    seed21) python3 Testing/asm/fuzz10/fuzz10.py $f 21 200 qemu 2>&1 | tail -3 | cut -c1-600;;
    seed22) python3 Testing/asm/fuzz10/fuzz10.py $f 22 200 qemu 2>&1 | tail -3 | cut -c1-600;;
    big) BIG=1 python3 Testing/asm/fuzz10/fuzz10.py $f 23 60 qemu big 2>&1 | tail -3 | cut -c1-600;;
    sail) SAILMAX=${SAILMAX:-1500} python3 Testing/asm/fuzz10/fuzz10.py $f 24 40 sail 2>&1 | tail -3 | cut -c1-600;;
  esac
  rm -rf Testing/asm/fuzz10/work$WSUF
}
export -f one
tr ' ' '\n' < Testing/asm/fuzz10/ALL.txt | xargs -P ${P:-3} -I{} bash -c 'one {}'
