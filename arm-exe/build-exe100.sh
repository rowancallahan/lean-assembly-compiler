#!/bin/sh -e
# Rebuild the experimental executable from the repo. ~2 h on 4 cores, needs ~14 GB RAM (V8Base).
export PATH=$HOME/.elan/bin:$PATH
H=$(cd "$(dirname "$0")"; pwd); T=${T:-$HOME/exe100}; R=${R:-$HOME/run100}
cp -a $H/../arm-exe-gen/armv9 $T
cp $H/gen100/SysregsAutogen.lean $T/Armv9/
(cd $T && patch -p0 lakefile.toml < $H/gen100/lakefile.patch)
for m in V8Base SysregsAutogen Instrs32 Instrs64 Instrs64Sme Instrs64Sve DecodeEnd Elfmain; do D=$T $H/build.sh Armv9.$m; done
for m in DecodeEnd SysregsAutogen V8Base; do D=$T $H/build.sh Armv9.$m:o; done   # one big clang at a time
$H/mkmodel.sh
mkdir -p $R; cp -r $H/Run.lean $H/ArmRun $H/lean-toolchain $R/; sed "s|path = .*|path = \"$T\"|" $H/lakefile.toml > $R/lakefile.toml
cd $R && lake build armrun
printf "15 0 0 0 aa0003e9 aa0003ea 8b0a0129 aa0903e0 d65f03c0\n" > t.txt && [ "$(./.lake/build/bin/armrun t.txt)" = 2a ]
