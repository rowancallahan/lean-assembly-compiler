#!/bin/bash
# Builds everything of Arm/apc and prints the axioms of the main theorems (Lean 4.34.1).
#  1. DeepMind's trusted `arm64` package (google-deepmind/code-verification at b0f729a, NOT in this repo) at $CV
#     (default /home/user/deps/code-verification; blobless clone, see README.md), built with Lean 4.34.1.
#  2. `stage.sh` (model-free source facts from Riscv/, into Apc/Src, not committed), then `lake build` of this package:
#     the instance `apc L : Machine`, `compile_apc`, `gcd_apc`, `sort_apc`, `agree_emitted` (against a verbatim copy
#     `Apc/Small.lean` of our small machine); `apcF : MachineF`, `msort_apc`; `apcC : MachineC`,
#     `callsCode_implements_apc`, `sumTo_apc`/`fib_apc`/`isEven_apc`/`treeEval_apc`; `apcw`/`apcwF : Wide`/`WideF`,
#     `compBFOA_ok`, `msortO_apc`, `crc_apc_of`/`crc_apc`/`crcO_apc` (all printed by `Apc/Axioms.lean`).
#     stage.sh also applies `mid.patch` (writable hypotheses on the store laws) to copies of eight Compiler files.
#  3. The bridge, in ONE environment with the Sail ARM model (/home/user/armv9-lean, read only, never rebuilt):
#     `Arm/proofs/check.sh` (skip with SKIP_ARM=1 if Arm/proofs/build is current), then Br/Flags, Br/Agree,
#     Br/AgreeAll (= Apc/* with `armStep`/`emitted` imported from OUR Arm/proofs/Arm/{Small,Words}.lean) and Bridge.lean.
set -e
H=$(cd "$(dirname "$0")" && pwd); R=$(cd "$H/../.." && pwd)
CV=${CV:-/home/user/deps/code-verification}; A=$CV/arm64-semantics/Arm64
export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin:$HOME/.elan/bin:$PATH
t() { S=$(date +%s); "$@"; echo "  [$(( $(date +%s) - S )) s] $*"; }
[ "$(git -C "$CV" rev-parse --short=7 HEAD)" = b0f729a ] || { echo "need $CV at b0f729a"; exit 1; }
echo "== arm64 (their trusted package)"; (cd "$A" && t lake build -q)
echo "== Apc (lake)"; "$H/stage.sh"; (cd "$H" && t lake build -q Apc.Axioms)
(cd "$H" && lake env lean Apc/Axioms.lean)
[ -n "$SKIP_ARM" ] || { echo "== Arm/proofs (Sail side)"; t "$R/Arm/proofs/check.sh"; }
echo "== bridge"
B=$H/build; mkdir -p "$B/Br"
cp "$H/Apc/Flags.lean" "$B/Br/Flags.lean"
sed 's/^import Apc.Small$/import Arm.Words/; s/^import Apc.Flags$/import Br.Flags/; s/^open Proven.Arm$/open ArmProof/' "$H/Apc/Agree.lean" > "$B/Br/Agree.lean"
sed 's/^import Apc.Agree$/import Br.Agree/; s/^open Proven.Arm$/open ArmProof/' "$H/Apc/AgreeAll.lean" > "$B/Br/AgreeAll.lean"
cp "$H/Bridge.lean" "$B/Br/Bridge.lean"
cd /home/user/armv9-lean
export LEAN_PATH="$B:$R/Arm/proofs/build:$A/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
for f in Br/Flags Br/Agree Br/AgreeAll Br/Bridge; do
  echo "-- $f"; t lean --root="$B" --tstack=400000 -o "$B/$f.olean" "$B/$f.lean"
done
