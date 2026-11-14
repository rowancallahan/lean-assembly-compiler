#!/bin/bash
# Builds the ARM proofs in dependency order against the built model in /home/user/armv9-lean.
# Run from anywhere: Arm/proofs/check.sh [Module/Path ...]
# The shared 4.29 sources are read from their single location in the repo (Spec/Code.lean, Arm/CompilerArm.lean)
# and staged into build/src/Proven/ under their old module names Proven.Code / Proven.CompilerArm
# (only the import line `import Spec.Code` is rewritten to `import Proven.Code`), so files here keep `import Proven.*`.
set -e
D=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$D/../.." && pwd)
export PATH=$HOME/.elan/bin:$PATH
mkdir -p "$D/build/Proven" "$D/build/Arm" "$D/build/src/Proven"
cp "$R/Spec/Code.lean" "$D/build/src/Proven/Code.lean"
sed 's/^import Spec\.Code$/import Proven.Code/' "$R/Arm/CompilerArm.lean" > "$D/build/src/Proven/CompilerArm.lean"
cd /home/user/armv9-lean
BASE=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$D/build:$BASE"
for f in ${@:-Proven/Code Proven/CompilerArm Arm/Base Arm/Exec Arm/Flags Arm/Small Arm/Words Arm/Compiler Arm/Ret Arm/Hooks Arm/Fetch Arm/Step Arm/Full Arm/Machine Arm/Witness Arm/Branch Arm/Axioms}; do
  case $f in Proven/*) root="$D/build/src";; *) root="$D";; esac
  echo "== $f"; S=$(date +%s.%N); lean --root="$root" --tstack=400000 -o "$D/build/$f.olean" "$root/$f.lean"; echo "  $(echo "$(date +%s.%N) - $S" | bc) s"
done
