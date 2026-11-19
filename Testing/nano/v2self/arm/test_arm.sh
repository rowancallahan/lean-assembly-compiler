#!/usr/bin/env bash
# Linux test of rv2arm (UNPROVEN glue): every example is compiled to RISC-V by B2 (nanorun), translated with rv2arm.py,
# run with shim_arm under qemu-aarch64 on several inputs, and compared with nanorun's output and status.
# Needs: cc, aarch64-linux-gnu-gcc, qemu-aarch64(-static), python3.   usage: test_arm.sh [prog.lean ...]
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$D/..; T=$(mktemp -d)
QEMU=${QEMU:-$(command -v qemu-aarch64-static || command -v qemu-aarch64)}
cc -O2 "$V/run/nanorun.c" -o "$T/nanorun"
aarch64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_arm.c" -o "$T/shim_arm"
[ $# -gt 0 ] || set -- "$V"/examples/*.lean
printf '' > "$T/i0"; printf 'a' > "$T/i1"; printf 'hello, world\n' > "$T/i2"
printf '\x00\xff\x10\x10\x10\x7f\x80zzzA' > "$T/i3"; head -c 3000 /dev/urandom > "$T/i4"; printf '\x14' > "$T/i5"
fail=0
for p in "$@"; do
  n=$(basename "$p" .lean)
  grep -v '^--' "$p" > "$T/$n.src"
  "$T/nanorun" "$V/B2.bin" "$T/$n.src" "$T/$n.rv" 2> /dev/null
  [ -s "$T/$n.rv" ] || { echo "$n: REJECTED"; fail=1; continue; }
  python3 "$D/rv2arm.py" "$T/$n.rv" > "$T/$n.arm"
  for i in "$T"/i?; do
    rs=0; "$T/nanorun" "$T/$n.rv" "$i" "$T/o.rv" 2> "$T/l.rv" || rs=$?
    [ $rs -eq 0 ] || : > "$T/o.rv"
    as=0; "$QEMU" "$T/shim_arm" "$T/$n.arm" < "$i" > "$T/o.arm" 2> "$T/l.arm" || as=$?
    a=$(sed -n 's/.*status \(-\?[0-9]*\).*/\1/p' "$T/l.arm"); r=$(sed -n 's/.*a0 = \(-\?[0-9]*\).*/\1/p' "$T/l.rv")
    if cmp -s "$T/o.rv" "$T/o.arm" && [ "$a" = "$r" ]; then res=OK; else res=FAIL; fail=1; fi
    echo "$n $(basename "$i"): rv(a0=$r,$(wc -c < "$T/o.rv")B) arm(status=$a,$(wc -c < "$T/o.arm")B) $res"
  done
done
exit $fail
