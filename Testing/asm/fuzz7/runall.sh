#!/bin/bash
# usage: runall.sh seed1|seed2|big|sail   (needs Lean 4.29 in /tmp/leandl/x/*/bin, qemu-system-riscv64, riscv64-linux-gnu-gcc,
# Sail 0.9 at the path in fuzz7.py)
cd "$(dirname "$0")"; export WSUF=$1
FNS="wa_kraft wa_nextcodes wa_gcd fx_gcd wa_ops64 wa_ops32 wa_opsn fx_ops64 fx_ops32 fx_opsn"
for f in $FNS; do
  case $1 in
    seed1) python3 fuzz7.py $f 1 1500 qemu 2>&1 | tail -1 | cut -c1-500;;
    seed2) python3 fuzz7.py $f 2 1500 qemu 2>&1 | tail -1 | cut -c1-500;;
    big) BIGN=1 python3 fuzz7.py $f 3 40 qemu 2>&1 | tail -1 | cut -c1-500;;
    sail) python3 fuzz7.py $f 4 120 sail 2>&1 | tail -1 | cut -c1-500;;
  esac
done
