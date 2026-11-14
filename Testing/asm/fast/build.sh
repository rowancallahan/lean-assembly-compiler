#!/bin/bash
# compile the unproved fast backends to .olean files in Testing/asm/work/lib (put it on LEAN_PATH when running fuzz_exp.lean)
set -e
R=$(cd "$(dirname "$0")/../../.." && pwd); cd "$R"; export PATH=$HOME/.elan/bin:$PATH
L=Testing/asm/work/lib; mkdir -p $L
lake env lean -o $L/CodeFast.olean Testing/asm/fast/CodeFast.lean
LEAN_PATH=$(lake env printenv LEAN_PATH):$R/$L lake env lean -o $L/CompilerArmFast.olean Testing/asm/fast/CompilerArmFast.lean
