#!/bin/sh -e
# Regenerate the ARM v9.4-A Lean model from pinned, unmodified upstream sources.
# Needs: opam switch with Sail's deps, z3.  Output: $OUT (default ./armv9).
SAIL_REV=ef5dca5ac2048a19ab971f128bb13477561c021c      # rems-project/sail
ARM_REV=5416ef6b43e9527c38dc71fb752259c1d01a47e1       # rems-project/sail-arm
W=${W:-$PWD/regen-work}; OUT=${OUT:-$PWD/armv9}
mkdir -p "$W"; cd "$W"
[ -d sail ] || git clone https://github.com/rems-project/sail.git
[ -d sail-arm ] || git clone https://github.com/rems-project/sail-arm.git
git -C sail checkout -q $SAIL_REV; git -C sail-arm checkout -q $ARM_REV
for p in "$(dirname "$0")"/patches/sail/*.patch; do [ -e "$p" ] && git -C sail apply "$p"; done
eval $(opam env); (cd sail && opam install . --deps-only --yes && make install)
(cd sail-arm/arm-v9.4-a && make clean && make gen_lean VERBOSE_FLAG=)
rm -rf "$OUT"; cp -r sail-arm/arm-v9.4-a/lean/armv9 "$OUT"
find "$OUT" -name '*.lean' | sort | xargs sha256sum | sha256sum
