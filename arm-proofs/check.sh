#!/bin/bash
# Builds the ARM proofs in dependency order against the built model in /home/user/armv9-lean.
set -e
D=$(cd "$(dirname "$0")" && pwd)
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/armv9-lean
BASE=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$D/build:$BASE"
mkdir -p "$D/build/Proven" "$D/build/Arm"
for f in ${@:-Proven/Code Proven/CompilerArm}; do
  echo "== $f"; S=$(date +%s.%N); lean --root="$D" --tstack=400000 -o "$D/build/$f.olean" "$D/$f.lean"; echo "  $(echo "$(date +%s.%N) - $S" | bc) s"
done
