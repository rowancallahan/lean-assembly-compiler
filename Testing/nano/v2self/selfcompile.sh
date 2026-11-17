#!/bin/bash
# Interim self-compile check. Usage: bash Testing/nano/v2self/selfcompile.sh [KAPPA=65536] [WORK_MB=64]   (repo root, lake env on PATH)
# 1. frontElabK KAPPA + gen on the stripped, concatenated Nano/V2Self/C/*.lean (selfcompile.lean) -> P.words
# 2. P on QEMU with the same text as input (selfrun.py) -> O.bin
# 3. native reference C.m on the text (native_ref.lean) -> Oref.bin; cmp O Oref; P size.  Needs gcc-riscv64, qemu-system-riscv64.
set -e
K=${1:-65536}; W=${2:-64}; D=${D:-/tmp/selfcompile}; mkdir -p $D
C=Nano/V2Self/C
lake env lean --run Testing/nano/v2self/selfcompile.lean $K $D $C/Base.lean $C/Asm.lean $C/Expand.lean $C/Lex.lean $C/Inl.lean $C/Parse.lean $C/Main.lean
rm -f $D/O.bin; TMO=300 python3 Testing/nano/v2self/selfrun.py $D $W 4096
lake env lean --run Testing/nano/v2self/native_ref.lean $D/src.txt $D/Oref.bin
ls -l $D/O.bin $D/Oref.bin; cmp $D/O.bin $D/Oref.bin && echo "QEMU output == native C.m output"
