#!/bin/sh -e
# Regenerate the ARM v9.4-A Lean model from pinned, unmodified upstream sources.
# Needs: opam switch with Sail's deps, z3.  Output: $OUT (default ./armv9).
SAIL_REV=ef5dca5ac2048a19ab971f128bb13477561c021c      # rems-project/sail
ARM_REV=5416ef6b43e9527c38dc71fb752259c1d01a47e1       # rems-project/sail-arm
G=$(cd "$(dirname "$0")" && pwd)
W=${W:-$PWD/regen-work}; OUT=${OUT:-$PWD/armv9}
mkdir -p "$W"; cd "$W"
[ -d sail ] || git clone https://github.com/rems-project/sail.git
[ -d sail-arm ] || git clone https://github.com/rems-project/sail-arm.git
git -C sail checkout -q $SAIL_REV; git -C sail-arm checkout -q $ARM_REV
for p in "$G"/patches/sail/*.patch; do [ -e "$p" ] && git -C sail apply "$p"; done
eval $(opam env); (cd sail && opam install . --deps-only --yes && make install)
(cd sail-arm/arm-v9.4-a && make clean && make gen_lean VERBOSE_FLAG= SAIL_FLAGS='--lean-partial-function Reduce__1')
rm -rf "$OUT"; cp -r sail-arm/arm-v9.4-a/lean/armv9 "$OUT"
bash "$G/../../Testing/scripts/model_hash.sh" "$OUT"   # compare with MODEL_PROVENANCE.md (Arm/model: 8f79d6b2…)
# Partition (ARM_FAST.md A1 + option 4): core layer Armv9Core.* + rest, V8Base rest cut into parts. Verbatim text.
python3 "$G/partition.py" "$OUT" "$OUT-part" "$G/../proofs/Arm"
