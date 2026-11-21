#!/bin/sh
# test_jarm.sh [WORKDIR]: build the J -> ARM translator (Nano/Codegen/JArm.lean) with B2 and check it (UNPROVEN glue):
#  1. examples + edge: translated code runs like B2's RISC-V code and GenArm's (GA_arm.bin), 5 inputs each
#  2. translator fixpoint: jarm_arm = jarm_rv(jarm_rv) reproduces itself
#  3. C with the translator back end (self_N): N_rv (B2-built) -> N_arm -> N_arm (fixpoint), = jarm(B2(self_N))
#  4. B2 translated compiles C's source to B2.bin exactly
set -eu
D=$(cd "$(dirname "$0")" && pwd); V=$D/..; W=${1:-$(mktemp -d)}; mkdir -p "$W"
cc_rv=riscv64-linux-gnu-gcc; cc_arm=aarch64-linux-gnu-gcc
$cc_rv -O2 -static "$V/run/shim/shim_rv.c" -o "$W/shim_rv"; $cc_arm -O2 -static "$V/run/shim/shim_arm.c" -o "$W/shim_arm"
Q() { qemu-riscv64 "$W/shim_rv" "$@" 2>/dev/null; }; A() { qemu-aarch64 "$W/shim_arm" "$@" 2>/dev/null; }
fail() { echo "FAIL: $*"; exit 1; }
python3 "$D/build_jarm.py"
Q "$V/B2.bin" < "$D/jarm_input.txt" > "$W/jarm_rv.bin"; [ -s "$W/jarm_rv.bin" ] || fail "B2 rejects the translator"
Q "$V/B2.bin" < "$D/self_N_input.txt" > "$W/N_rv.bin"; [ -s "$W/N_rv.bin" ] || fail "B2 rejects self_N"
n=0
for f in "$V"/examples/*.lean "$D"/edge/*.lean; do
  grep -v '^--' "$f" > "$W/p.src"; Q "$V/B2.bin" < "$W/p.src" > "$W/p.rv"; Q "$W/jarm_rv.bin" < "$W/p.rv" > "$W/p.ja"
  A "$D/GA_arm.bin" < "$W/p.src" > "$W/p.ga"; [ -s "$W/p.ja" ] || fail "translator rejects $f"
  for x in "" "a" "hello world" "$(seq 1 300)" "$(printf '\377\000\001')"; do
    r1=$(printf '%s' "$x" | qemu-riscv64 "$W/shim_rv" "$W/p.rv" 2>&1 | od -An -tx1 | tr -d ' \n')
    r2=$(printf '%s' "$x" | qemu-aarch64 "$W/shim_arm" "$W/p.ja" 2>&1 | od -An -tx1 | tr -d ' \n')
    r3=$(printf '%s' "$x" | qemu-aarch64 "$W/shim_arm" "$W/p.ga" 2>&1 | od -An -tx1 | tr -d ' \n')
    r2=$(echo "$r2" | sed 's/7368696d5f61726d/7368696d5f7276/'); r3=$(echo "$r3" | sed 's/7368696d5f61726d/7368696d5f7276/')
    [ "$r1" = "$r2" ] || fail "run $f (translated)"; [ "$r1" = "$r3" ] || fail "run $f (GenArm)"
  done; n=$((n + 1))
done
echo "PASS examples + edge: $n programs x 5 inputs (RISC-V = translated = GenArm)"
Q "$W/jarm_rv.bin" < "$W/jarm_rv.bin" > "$W/jarm_arm.bin"; A "$W/jarm_arm.bin" < "$W/jarm_rv.bin" | cmp -s - "$W/jarm_arm.bin" || fail "translator fixpoint"
echo "PASS translator fixpoint ($(wc -c < "$W/jarm_arm.bin") bytes)"
Q "$W/N_rv.bin" < "$D/self_N_input.txt" > "$W/N_arm.bin"; A "$W/N_arm.bin" < "$D/self_N_input.txt" | cmp -s - "$W/N_arm.bin" || fail "self_N fixpoint"
Q "$W/jarm_rv.bin" < "$W/N_rv.bin" | cmp -s - "$W/N_arm.bin" || fail "jarm(B2(self_N)) != N_arm"
echo "PASS self_N fixpoint ($(wc -c < "$W/N_arm.bin") bytes) = jarm(B2(self_N))"
A "$W/N_arm.bin" < "$V/self_S_input.txt" > "$W/B2_t.bin"; Q "$W/jarm_rv.bin" < "$V/B2.bin" | cmp -s - "$W/B2_t.bin" || fail "N_arm(C) != jarm(B2)"
A "$W/B2_t.bin" < "$V/self_S_input.txt" | cmp -s - "$V/B2.bin" || fail "translated B2 does not give B2.bin"
echo "PASS translated B2 compiles C's source to B2.bin"
