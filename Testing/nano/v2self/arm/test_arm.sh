#!/usr/bin/env bash
# Linux test of the nano translator rv2arm.lean (UNPROVEN glue). All code runs on QEMU's machine models: RISC-V code
# with qemu-riscv64 shim_rv, ARM code with qemu-aarch64 shim_arm. NANORUN=1 adds the interpreter nanorun as a
# cross-check of every RISC-V run. Needs: riscv64-linux-gnu-gcc, aarch64-linux-gnu-gcc, qemu-user-static, python3
# (oracle rv2arm.py only); cc only with NANORUN=1.  usage: test_arm.sh [prog.lean ...]   (default: all examples)
#  1. B2 compiles rv2arm.lean -> rv2arm_rv.bin; it runs on itself (RISC-V) -> rv2arm_arm.bin; the ARM translator
#     translates itself to itself (fixpoint) and both equal the Python oracle; the checked-in binaries match.
#  2. every example: compiled by B2, translated by the ARM translator (= oracle), run on 6 inputs as RISC-V and as
#     ARM: output and status agree.
#  3. B2 translated by the ARM translator = B2_arm.bin; ARM-B2 on the compiler's source = B2.bin byte for byte.
#  4. invalid input (an ecall word, an odd size) is refused.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); V=$D/..; T=$(mktemp -d)
QEMU=${QEMU:-$(command -v qemu-aarch64-static || command -v qemu-aarch64)}
QRV=${QRV:-$(command -v qemu-riscv64-static || command -v qemu-riscv64)}
aarch64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_arm.c" -o "$T/shim_arm"
riscv64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_rv.c" -o "$T/shim_rv"
[ -z "${NANORUN:-}" ] || cc -O2 "$V/run/nanorun.c" -o "$T/nanorun"
# rvrun CODE IN OUT LOG: the RISC-V code on qemu-riscv64 (status line in LOG); with NANORUN=1 also nanorun, which
# must agree (status and output)
rvrun() {
  local rc=0; "$QRV" "$T/shim_rv" "$1" < "$2" > "$3" 2> "$4" || rc=$?
  if [ -n "${NANORUN:-}" ]; then
    local nr=0; "$T/nanorun" "$1" "$2" "$T/nr.out" 2> "$T/nr.log" || nr=$?
    [ $nr -eq 0 ] || : > "$T/nr.out"
    [ "$(st "$4")" = "$(sed -n 's/.*a0 = \(-\?[0-9]*\).*/\1/p' "$T/nr.log")" ] && cmp -s "$3" "$T/nr.out" \
      || bad "nanorun disagrees with qemu-riscv64 on $(basename "$1") < $(basename "$2")"
  fi
  return $rc
}
st() { sed -n 's/.*status \(-\?[0-9]*\).*/\1/p' "$1"; }
ok() { echo "OK   $1"; }
bad() { echo "FAIL $1"; fail=1; }
fail=0

grep -v '^--' "$D/rv2arm.lean" > "$T/rv2arm.src"
rvrun "$V/B2.bin" "$T/rv2arm.src" "$T/rv2arm_rv.bin" "$T/l"
RUN="$QRV $T/shim_rv $T/rv2arm_rv.bin" "$D/rv2arm.sh" "$T/rv2arm_rv.bin" > "$T/rv2arm_arm.bin"
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
  rvrun "$V/B2.bin" "$T/$n.src" "$T/$n.rv" "$T/l" || true
  [ -s "$T/$n.rv" ] || { bad "$n: REJECTED by B2"; continue; }
  RUN="$ARM" "$D/rv2arm.sh" "$T/$n.rv" > "$T/$n.arm"
  python3 "$D/rv2arm.py" "$T/$n.rv" | cmp -s - "$T/$n.arm" || bad "$n: translator != oracle"
  for i in "$T"/i?; do
    rvrun "$T/$n.rv" "$i" "$T/o.rv" "$T/l.rv" || true
    "$QEMU" "$T/shim_arm" "$T/$n.arm" < "$i" > "$T/o.arm" 2> "$T/l.arm" || true
    a=$(st "$T/l.arm"); r=$(st "$T/l.rv")
    if cmp -s "$T/o.rv" "$T/o.arm" && [ "$a" = "$r" ]; then ok "$n $(basename "$i") (status $a, $(wc -c < "$T/o.arm") B)"
    else bad "$n $(basename "$i"): rv a0=$r, arm status=$a"; fi
  done
done

RUN="$ARM" "$D/rv2arm.sh" "$V/B2.bin" > "$T/B2_arm.bin"
cmp -s "$T/B2_arm.bin" "$D/B2_arm.bin" && ok "B2 translated by the ARM translator = B2_arm.bin" || bad "B2_arm.bin"
"$QEMU" "$T/shim_arm" "$T/B2_arm.bin" < "$V/self_S_input.txt" > "$T/self.bin" 2> /dev/null
cmp -s "$T/self.bin" "$V/B2.bin" && ok "ARM-B2 self-compile = B2.bin" || bad "ARM-B2 self-compile"
rvrun "$V/B2.bin" "$V/self_S_input.txt" "$T/self_rv.bin" "$T/l" || true
cmp -s "$T/self_rv.bin" "$V/B2.bin" && ok "RISC-V B2 self-compile (qemu-riscv64) = B2.bin" || bad "RISC-V B2 self-compile"

# instruction set (§0-min): only these mnemonics (objdump aliases), no register field 31 (xzr/wzr/sp), never x18..x29
if command -v aarch64-linux-gnu-objdump > /dev/null; then
  for f in "$T/B2_arm.bin" "$T/rv2arm_arm.bin"; do
    aarch64-linux-gnu-objdump -D -b binary -m aarch64 "$f" | awk -F'\t' 'NF >= 3 {print $3 "\t" $4}' > "$T/dis"
    other=$(cut -f1 "$T/dis" | sort -u | grep -vxE 'mov|movk|add|sub|subs|and|orr|eor|lsl|lsr|madd|b\.(eq|ne|cs|cc)|cbz|b|bl|br|ldr|str|ldrb|strb' || true)
    bad=$(grep -cE '\bsp\b|[wx]zr|\b[xw](1[89]|2[0-9])\b' "$T/dis" || true)
    movs=$(grep -cP '^mov\t' "$T/dis"); movz=$(aarch64-linux-gnu-objdump -D -b binary -m aarch64 "$f" | grep -cP '\td2[89a-f][0-9a-f]{5}\s+\tmov\t' || true)
    if [ -z "$other" ] && [ "$bad" = 0 ] && [ "$movs" = "$movz" ]; then ok "instruction set of $(basename "$f")"
    else bad "instruction set of $(basename "$f"): other=[$other] sp/xzr/x18-29=$bad mov=$movs movz=$movz"; fi
  done
fi

# G's semantic certificate (Nano/V2Self/Proof/CertArm, CertArm.sem_rv2arm: the nano meaning of rv2arm's text = the Lean
# function RA.m) is generated from rv2arm.lean; it must be about the CURRENT text. All of CertArm comes from the same
# comment-stripped text as Src.lean, so compare that. Regenerate: the 4 commands in ../cert/gen_cert.py (target arm).
CA="$V/../../../Nano/V2Self/Proof/CertArm/Src.lean"
if [ -f "$CA" ]; then
  sed -n '/^namespace RA$/,/^end RA$/p' "$CA" | sed '1d;$d' > "$T/ca.src"
  { grep -v '^--' "$D/rv2arm.lean"; echo; } > "$T/now.src"   # gen_cert keeps the empty last line of split("\n")
  cmp -s "$T/ca.src" "$T/now.src" && ok "CertArm certificate is about the current rv2arm.lean" \
    || bad "CertArm is STALE (about an older rv2arm.lean): regenerate with ../cert/gen_cert.py (target arm), commit"
else bad "CertArm/Src.lean missing"; fi

# rare forms (x0 operands, mul, x2, far offsets, x0 stores): nano translator = oracle
python3 "$D/synth_rv.py" > "$T/synth.rv"
RUN="$ARM" "$D/rv2arm.sh" "$T/synth.rv" > "$T/synth.arm" || true
python3 "$D/rv2arm.py" "$T/synth.rv" | cmp -s - "$T/synth.arm" && ok "synthetic forms: translator = oracle" || bad "synthetic forms"

# refused: an ecall word, an odd size, and (FZ-T) unmapped sources with rd = x0 and jalr through x0
printf '\x73\x00\x00\x00' > "$T/bad1"; printf '\x13\x05\xf0' > "$T/bad2"
printf '\x13\x80\x01\x00' > "$T/bad3"; printf '\x03\xb0\x01\x00' > "$T/bad4"
printf '\x33\x80\x41\x00' > "$T/bad5"; printf '\x67\x00\x00\x00' > "$T/bad6"
# limits an RV word can exceed (immediates beyond imm12 cannot be encoded in RV words; their checks are defensive):
# branch/jal target past the end or before 0, misaligned branch/jal offsets, slli shift field with bit 26, jal rd = x5,
# branch and jal reaching only the end of a 2-word program
python3 - "$T" <<'EOF'
import struct, sys
T = sys.argv[1]
def I(op, f3, rd, rs, imm): return (imm & 4095) << 20 | rs << 15 | f3 << 12 | rd << 7 | op
def B(f3, a, b, o):
    return ((o >> 12) & 1) << 31 | ((o >> 5) & 63) << 25 | b << 20 | a << 15 | f3 << 12 | ((o >> 1) & 15) << 8 | ((o >> 11) & 1) << 7 | 0x63
def J(rd, o): return ((o >> 20) & 1) << 31 | ((o >> 1) & 1023) << 21 | ((o >> 11) & 1) << 20 | ((o >> 12) & 255) << 12 | rd << 7 | 0x6f
nop = I(0x13, 0, 0, 0, 0)
cases = {'lim1': [B(0, 5, 6, 8), nop], 'lim2': [nop, B(1, 5, 6, -8)], 'lim3': [J(0, 8), nop], 'lim4': [nop, J(1, -8)],
         'lim5': [B(7, 5, 6, 2), nop], 'lim6': [J(0, 2), nop], 'lim7': [I(0x13, 1, 5, 6, 64 | 3), nop],
         'lim8': [J(5, 4), nop], 'lim9': [I(0x13, 5, 5, 6, 1024 | 3), nop]}
for k, ws in cases.items(): open('%s/%s' % (T, k), 'wb').write(struct.pack('<%dI' % len(ws), *ws))
open('%s/okl' % T, 'wb').write(struct.pack('<4I', B(0, 5, 6, 12), J(0, 8), J(1, -8), nop))   # in range: accepted
EOF
RUN="$ARM" "$D/rv2arm.sh" "$T/okl" > "$T/okl.arm" && python3 "$D/rv2arm.py" "$T/okl" | cmp -s - "$T/okl.arm" \
  && ok "in-range branch/jal at the program edges accepted (= oracle)" || bad "in-range edge branches"
for b in bad1 bad2 bad3 bad4 bad5 bad6 lim1 lim2 lim3 lim4 lim5 lim6 lim7 lim8 lim9; do
  if python3 "$D/rv2arm.py" "$T/$b" > /dev/null 2>&1; then bad "$b accepted by the oracle"; fi
  if RUN="$ARM" "$D/rv2arm.sh" "$T/$b" > /dev/null 2>&1; then bad "$b accepted"; else ok "$b refused"; fi
done
exit $fail
