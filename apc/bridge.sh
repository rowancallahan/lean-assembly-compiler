#!/bin/bash
# Item D: both semantics in ONE Lean 4.34.1 environment.
# Needs: (1) Arm/proofs/check.sh run (oleans in Arm/proofs/build, against the built ARM Sail model at /home/user/armv9-lean),
#        (2) their `arm64` package built under 4.34.1 at $A (copy of Arm64.lean + Arm64/Trusted + Arm64/Legacy, toolchain file changed).
# Stages Apc/Flags, Apc/Agree, Apc/AgreeAll with `armStep` / `emitted` taken from OUR Sail-side files (Arm.Small, Arm.Words)
# instead of the verbatim copy Apc/Small.lean, then checks Bridge.lean.
set -e
H=$(cd "$(dirname "$0")" && pwd); R=$(cd "$H/.." && pwd); A=${A:-$HOME/apc/t341/Arm64}; B=${B:-$HOME/apc/bridge}
export PATH=$HOME/.elan/bin:$PATH; mkdir -p $B/Br
cd /home/user/armv9-lean; export LEAN_PATH="$B:$R/Arm/proofs/build:$A/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
cp $H/Apc/Flags.lean $B/Br/Flags.lean
sed 's/^import Apc.Small$/import Arm.Words/; s/^import Apc.Flags$/import Br.Flags/; s/^open Proven.Arm$/open ArmProof/' $H/Apc/Agree.lean > $B/Br/Agree.lean
sed 's/^import Apc.Agree$/import Br.Agree/; s/^open Proven.Arm$/open ArmProof/' $H/Apc/AgreeAll.lean > $B/Br/AgreeAll.lean
cp $H/Bridge.lean.txt $B/Br/Bridge.lean
for f in Br/Flags Br/Agree Br/AgreeAll Br/Bridge; do
  echo "== $f"; S=$(date +%s); lean --root=$B --tstack=400000 -o $B/$f.olean $B/$f.lean; echo "  $(( $(date +%s) - S )) s"
done
