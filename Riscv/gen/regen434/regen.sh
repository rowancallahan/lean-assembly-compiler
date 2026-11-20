#!/bin/bash
# RISC-V model REGENERATED with Sail 97aa617dc (not the trusted model) -- reproduction script (branch rv-regen-434).
# Generates LeanRV64D from riscv/sail-riscv b7d1357 with rems-project/sail sail2 @ 97aa617dc (Lean 4.34.1, lean-sail v10),
# on top of opencompl/sail-riscv-lean @ 51c635c, then adds the banner line. No other edits.
# usage: regen.sh <workdir>
set -euxo pipefail
W=$1; mkdir -p "$W"; cd "$W"
SAIL_REV=97aa617dc; RISCV_REV=b7d1357; BASE=51c635c
git clone https://github.com/rems-project/sail.git && git -C sail checkout $SAIL_REV
opam switch create sail 5.2.1 -y; eval $(opam env --switch=sail)
(cd sail && opam pin add -y -n . && opam install -y $(ls *.opam | sed 's/.opam//'))
git clone https://github.com/riscv/sail-riscv.git && git -C sail-riscv checkout $RISCV_REV
# the C-emulator dependencies are not needed for Lean generation (upstream switches)
cmake -S sail-riscv -B sail-riscv/build -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DDOWNLOAD_CLI11=OFF -DDOWNLOAD_ASIO=OFF -DDOWNLOAD_JSONCONS=OFF
cmake --build sail-riscv/build --target generated_lean_rv64d
git clone https://github.com/opencompl/sail-riscv-lean.git regen && git -C regen checkout -b rv-regen-434 $BASE
G=sail-riscv/build/model/Lean_RV64D
rm -rf regen/LeanRV64D regen/LeanRV64D.lean
cp -r $G/LeanRV64D $G/LeanRV64D.lean $G/lakefile.toml $G/lean-toolchain $G/lake-manifest.json regen/
B="RISC-V model REGENERATED with Sail $SAIL_REV (rems-project/sail sail2, untagged) from riscv/sail-riscv $RISCV_REV (not the trusted model); provenance: Riscv/gen/PROVENANCE.md in lean-assembly-compiler"
for f in regen/LeanRV64D.lean regen/LeanRV64D/*.lean; do sed -i "1i -- $B" "$f"; done
sed -i "1i # $B" regen/lakefile.toml
(cd regen && lake update)
