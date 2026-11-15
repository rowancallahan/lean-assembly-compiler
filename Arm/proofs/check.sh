#!/bin/bash
# Builds the ARM proofs in dependency order against the built model in /home/user/armv9-lean.
# Run from anywhere: Arm/proofs/check.sh [Module/Path ...]
# The shared sources are read from their single location in the repo (Spec/Code.lean, Arm/CompilerArm.lean) and
# staged unchanged into build/src/ as modules Spec.Code / Proven.CompilerArm (Spec.Code under its repo name, so that
# the bridge in Arm/apc can import both these files and the Apc lake package, which also has Spec.Code).
set -e
D=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$D/../.." && pwd)
export PATH=$HOME/.elan/bin:$PATH
mkdir -p "$D/build/Proven" "$D/build/Spec" "$D/build/Arm" "$D/build/src/Proven" "$D/build/src/Spec"
rm -f "$D/build/src/Proven/Code.lean" "$D/build/Proven/Code.olean"
cp "$R/Spec/Code.lean" "$D/build/src/Spec/Code.lean"
cp "$R/Arm/CompilerArm.lean" "$D/build/src/Proven/CompilerArm.lean"
cd /home/user/armv9-lean
BASE=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$D/build:$BASE"
for f in ${@:-Spec/Code Proven/CompilerArm Arm/Base Arm/Exec Arm/Flags Arm/Small Arm/Words Arm/Compiler Arm/Ret Arm/Hooks Arm/Fetch Arm/Step Arm/Full Arm/Machine Arm/Witness Arm/Branch Arm/SymDec Arm/BrFull Arm/Axioms}; do
  case $f in Proven/*|Spec/*) root="$D/build/src";; *) root="$D";; esac
  echo "== $f"; S=$(date +%s.%N); lean --root="$root" --tstack=400000 -o "$D/build/$f.olean" "$root/$f.lean"; echo "  $(echo "$(date +%s.%N) - $S" | bc) s"
done
