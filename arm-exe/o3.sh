#!/bin/sh -e
# Faster runner: recompile every C file of the linked executable at -O3, except DecodeEnd.c and SysregsAutogen.c
# (clang does not finish / was not tried at -O3; their -O0 objects are reused). Same C sources, same link line.
# usage: o3.sh [RUN_DIR] [OUT_DIR]   (RUN_DIR has been built with `lake build armrun`)
R=${1:-$HOME/run100}; O=${2:-$HOME/o3}; L=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1; mkdir -p $O
tr ' ' '\n' < $R/.lake/build/bin/armrun.rsp | tr -d '"' > $O/rsp.txt
grep 'c.o.export$' $O/rsp.txt | grep -v 'DecodeEnd\|SysregsAutogen' | while read f; do
  c=${f%.o.export}; o=$O/$(echo $c | tr / _).o
  [ $o -nt $c ] || echo "$L/bin/clang -c -o $o $c -I $L/include -fstack-clash-protection -ffp-contract=off -fdata-sections -ffunction-sections -fPIC -fvisibility=hidden -Wno-unused-command-line-argument --sysroot $L -nostdinc -isystem $L/include/clang -O3 -DNDEBUG -fbracket-depth=100000 -DLEAN_EXPORTING"
done | xargs -P ${J:-2} -I{} sh -c {}
sed "s|^\(.*\)\.c\.o\.export$|\1.c|" $O/rsp.txt | while read a; do
  case $a in *DecodeEnd.c|*SysregsAutogen.c) echo $a.o.export;; *.c) echo $O/$(echo $a | tr / _).o;; *) echo $a;; esac
done > $O/link.txt
$L/bin/clang -o $O/armrun $(cat $O/link.txt)
