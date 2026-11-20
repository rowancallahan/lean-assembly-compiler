#!/usr/bin/env bash
# Linux test of the nano translator rv2arm.lean (UNPROVEN glue). Needs: cc, aarch64-linux-gnu-gcc, qemu-aarch64(-static),
# python3 (oracle rv2arm.py only).  usage: test_arm.sh [prog.lean ...]   (default: all examples)
#  1. B2 compiles rv2arm.lean -> rv2arm_rv.bin; nanorun runs it on itself -> rv2arm_arm.bin; under qemu the ARM
#     translator translates itself to itself (fixpoint) and both equal the Python oracle; the checked-in binaries match.
#  2. every example: compiled by B2, translated by the ARM translator (= oracle), run with shim_arm under qemu on
#     6 inputs: output and status equal nanorun's.
#  3. B2 translated by the ARM translator = B2_arm.bin; ARM-B2 on the compiler's source = B2.bin byte for byte.
#  4. invalid input (an ecall word, an odd size) is refused.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$D/..; T=$(mktemp -d)
QEMU=${QEMU:-$(command -v qemu-aarch64-static || command -v qemu-aarch64)}
cc -O2 "$V/run/nanorun.c" -o "$T/nanorun"
aarch64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_arm.c" -o "$T/shim_arm"
ok() { echo "OK   $1"; }
bad() { echo "FAIL $1"; fail=1; }
fail=0

grep -v '^--' "$D/rv2arm.lean" > "$T/rv2arm.src"
"$T/nanorun" "$V/B2.bin" "$T/rv2arm.src" "$T/rv2arm_rv.bin" 2> /dev/null
RUN="$T/nanorun $T/rv2arm_rv.bin /dev/stdin /dev/stdout" "$D/rv2arm.sh" "$T/rv2arm_rv.bin" > "$T/rv2arm_arm.bin"
ARM="$QEMU $T/shim_arm $T/rv2arm_arm.bin"
RUN="$ARM" "$D/rv2arm.sh" "$T/rv2arm_rv.bin" | cmp -s - "$T/rv2arm_arm.bin" && ok "ARM translator fixpoint" || bad "fixpoint"
python3 "$D/rv2arm.py" "$T/rv2arm_rv.bin" | cmp -s - "$T/rv2arm_arm.bin" && ok "= oracle on itself" || bad "oracle on itself"
cmp -s "$T/rv2arm_rv.bin" "$D/rv2arm_rv.bin" && cmp -s "$T/rv2arm_arm.bin" "$D/rv2arm_arm.bin" \
  && ok "checked-in rv2arm_rv.bin / rv2arm_arm.bin" || bad "checked-in translator binaries differ"

[ $# -gt 0 ] || set -- "$V"/examples/*.lean
printf '' > "$T/i0"; printf 'a' > "$T/i1"; printf 'hello, world\n' > "$T/i2"
printf '\x00\xff\x10\x10\x10\x7f\x80zzzA' > "$T/i3"; head -c 3000 /dev/urandom > "$T/i4"; printf '\x14' > "$T/i5"
for p in "$@"; do
  n=$(basename "$p" .lean)
  grep -v '^--' "$p" > "$T/$n.src"
  "$T/nanorun" "$V/B2.bin" "$T/$n.src" "$T/$n.rv" 2> /dev/null
  [ -s "$T/$n.rv" ] || { bad "$n: REJECTED by B2"; continue; }
  RUN="$ARM" "$D/rv2arm.sh" "$T/$n.rv" > "$T/$n.arm"
  python3 "$D/rv2arm.py" "$T/$n.rv" | cmp -s - "$T/$n.arm" || bad "$n: translator != oracle"
  for i in "$T"/i?; do
    rs=0; "$T/nanorun" "$T/$n.rv" "$i" "$T/o.rv" 2> "$T/l.rv" || rs=$?
    [ $rs -eq 0 ] || : > "$T/o.rv"
    "$QEMU" "$T/shim_arm" "$T/$n.arm" < "$i" > "$T/o.arm" 2> "$T/l.arm" || true
    a=$(sed -n 's/.*status \(-\?[0-9]*\).*/\1/p' "$T/l.arm"); r=$(sed -n 's/.*a0 = \(-\?[0-9]*\).*/\1/p' "$T/l.rv")
    if cmp -s "$T/o.rv" "$T/o.arm" && [ "$a" = "$r" ]; then ok "$n $(basename "$i") (status $a, $(wc -c < "$T/o.arm") B)"
    else bad "$n $(basename "$i"): rv a0=$r, arm status=$a"; fi
  done
done

RUN="$ARM" "$D/rv2arm.sh" "$V/B2.bin" > "$T/B2_arm.bin"
cmp -s "$T/B2_arm.bin" "$D/B2_arm.bin" && ok "B2 translated by the ARM translator = B2_arm.bin" || bad "B2_arm.bin"
"$QEMU" "$T/shim_arm" "$T/B2_arm.bin" < "$V/self_S_input.txt" > "$T/self.bin" 2> /dev/null
cmp -s "$T/self.bin" "$V/B2.bin" && ok "ARM-B2 self-compile = B2.bin" || bad "ARM-B2 self-compile"

# instruction set (§0-min): only these mnemonics (objdump aliases), no sp, no stored xzr, never x18..x29
if command -v aarch64-linux-gnu-objdump > /dev/null; then
  for f in "$T/B2_arm.bin" "$T/rv2arm_arm.bin"; do
    aarch64-linux-gnu-objdump -D -b binary -m aarch64 "$f" | awk -F'\t' 'NF >= 3 {print $3 "\t" $4}' > "$T/dis"
    other=$(cut -f1 "$T/dis" | sort -u | grep -vxE 'mov|movk|add|sub|neg|and|orr|eor|lsl|lsr|mul|cmp|b\.(eq|ne|cs|cc)|cbz|b|bl|br|ldr|str|ldrb|strb' || true)
    bad=$(grep -cE '\bsp\b|^(str|strb)\s+[wx]zr|\b[xw](1[89]|2[0-9])\b' "$T/dis" || true)
    movs=$(grep -cP '^mov\t' "$T/dis"); movz=$(aarch64-linux-gnu-objdump -D -b binary -m aarch64 "$f" | grep -cP '\td2[89a-f][0-9a-f]{5}\s+\tmov\t' || true)
    if [ -z "$other" ] && [ "$bad" = 0 ] && [ "$movs" = "$movz" ]; then ok "instruction set of $(basename "$f")"
    else bad "instruction set of $(basename "$f"): other=[$other] sp/xzr-store/x18-29=$bad mov=$movs movz=$movz"; fi
  done
fi

printf '\x73\x00\x00\x00' > "$T/bad1"; printf '\x13\x05\xf0' > "$T/bad2"
for b in bad1 bad2; do
  if RUN="$ARM" "$D/rv2arm.sh" "$T/$b" > /dev/null 2>&1; then bad "$b accepted"; else ok "$b refused"; fi
done
exit $fail
