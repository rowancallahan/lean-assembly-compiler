#!/usr/bin/env bash
# check_E.sh [SEED] [N] : the self-hosted Expr emitter. Builds E's text (build_E.py), compiles it with the committed
# self-compiled C (B2.bin on qemu-riscv64 + shim_rv), runs E.bin on C's source, E's own text, the examples and N fuzz
# programs (nanogen.py SEED), and checks expand.py(E.bin's output) = the reference emitSpec (emit_ref.lean), byte for
# byte (rejections included). Then (unless SPOT=0) the spot check (run_check.py) on E's own text. Exit 1 on any difference.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); R=$(cd "$D/../../.." && pwd); V=$R/Testing/nano/v2self; W=$(mktemp -d); cd "$R"
QRV=$(command -v qemu-riscv64-static || command -v qemu-riscv64)
riscv64-linux-gnu-gcc -O2 -static $V/run/shim/shim_rv.c -o $W/shim_rv
python3 $D/build_E.py $W/E.src
$QRV $W/shim_rv $V/B2.bin < $W/E.src > $W/E.bin 2> $W/E.log; test -s $W/E.bin
echo "E: $(grep -c '^def ' $W/E.src) defs, $(wc -c < $W/E.src) bytes -> E.bin $(wc -c < $W/E.bin) bytes, sha256 $(sha256sum $W/E.bin | cut -c1-16)"
mkdir -p $W/set/ex $W/set/fz
for f in $V/examples/*.lean; do grep -v '^--' $f > $W/set/ex/$(basename $f .lean).src; done
python3 $V/fuzz/nanogen.py ${1:-1} ${2:-300} $W/set/fz
run() {  # run SRC... : E.bin on each (prefix P<i>. when several, as emit_ref.lean)
  local i=0
  for f in "$@"; do
    $QRV $W/shim_rv $W/E.bin < $f 2>> $W/run.log | python3 $D/expand.py > $W/one
    if [ "$(cat $W/one)" = "R" ]; then echo "R $i"
    elif [ $# -gt 1 ]; then sed "s/^D /D P$i./" $W/one; else cat $W/one; fi
    i=$((i+1))
  done
}
cmpset() {  # cmpset NAME SRC...
  local n=$1; shift
  run "$@" > $W/$n.E
  Testing/scripts/lean_run.sh $D/emit_ref.lean "$@" 2>/dev/null | sed 's/^\(R [0-9]*\) .*/\1/' > $W/$n.R
  cmp $W/$n.E $W/$n.R || { echo "FAIL $n: E.bin differs from emitSpec"; exit 1; }
  echo "$n: E.bin = emitSpec ($(grep -c '^D' $W/$n.E) defs, $(grep -c '^R' $W/$n.E || true) rejected programs)"
}
cmpset C $V/self_S_input.txt
cmpset E $W/E.src
cmpset examples $W/set/ex/*.src
cmpset fuzz $W/set/fz/*.src
[ "${SPOT:-1}" = 0 ] && exit 0  # SPOT=0: byte equality only
echo "spot check of E's own text:"; $D/run_check.py $W/E.src | tail -3
