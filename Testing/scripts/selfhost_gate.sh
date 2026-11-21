#!/usr/bin/env bash
# selfhost_gate.sh [WORKDIR] : the self-hosting gate (owner rule: every merge). One PASS/FAIL line per step, exit 1 on
# any FAIL. Checks CONSISTENCY of this checkout, not equality with an old release: binaries legitimately change when
# the compiler changes, so nothing here pins a hash across PRs (the sha256s are printed for the record only).
#   gen   regenerate the self-host proofs from C's current source (boot/fixpoint.sh's self_S*, cert/dump_pc + gen_cert.py
#         -> Nano/SelfHost/Cert, srclink/gen.lean -> Nano/SelfHost/SrcLink): no tracked file may change, none may appear
#   fix   RISC-V fixpoint: B1 (Lean-compiled) -> B2 = committed B2.bin, B2 -> B3 = B2 (boot/fixpoint.sh)
#   arm   native ARM: rebuilt GA_arm (C + GenArm) = committed native_arm/GA_arm.bin, GA_arm compiles its source to itself,
#         B2_na compiles C's source to B2.bin (native_arm/test_native.sh, also examples + edge programs)
#   cross 3-host matrix: RISC-V / rv2arm / native builds of both compilers agree on 14 sources (native_arm/cross_native.sh)
#   subset  Testing/scripts/subset_check.sh, when present (else SKIP)
# Needs: Lean (elan, toolchain of this checkout), leanc, python3, riscv64-linux-gnu-gcc, aarch64-linux-gnu-gcc,
# qemu-riscv64, qemu-aarch64. Generators run through Testing/scripts/lean_run.sh (lake env, or the import closure).
set -uo pipefail
R=$(cd "$(dirname "$0")/../.." && pwd); cd "$R"
W=${1:-$(mktemp -d)}; mkdir -p "$W"; V=Testing/nano/v2self; N=$V/native_arm
export PATH=$HOME/.elan/bin:$PATH
GEN="Nano/SelfHost $V"
fail=0
step() {  # step NAME FUNC : strict subshell, log in W/NAME.log
  local rc=0; ( set -euo pipefail; "$2" ) > "$W/$1.log" 2>&1 || rc=$?
  if [ $rc = 0 ]; then echo "PASS  $1  $(tail -1 "$W/$1.log")"
  elif [ $rc = 77 ]; then echo "SKIP  $1  $(tail -1 "$W/$1.log")"
  else echo "FAIL  $1  (exit $rc, log $W/$1.log): $(tail -1 "$W/$1.log")"; fail=1; fi
}
snap() { git status --porcelain --untracked-files=all -- $GEN; git diff -- $GEN; }
snap > "$W/start.snap"
[ ! -s "$W/start.snap" ] || echo "WARNING: $GEN has uncommitted changes; checked against the working tree as it was at start"
clean() { snap > "$W/now.snap"; cmp -s "$W/start.snap" "$W/now.snap" || { diff "$W/start.snap" "$W/now.snap" | head -20; echo "regenerated files differ from the checkout"; exit 1; }; }
s_fix() {
  clean
  $V/boot/fixpoint.sh "$W/fp"
  cmp "$W/fp/B2.bin" $V/B2.bin
  clean
  echo "B1 -> B2 = committed B2.bin, B3 = B2"
}
s_gen() {
  Testing/scripts/lean_run.sh $V/cert/dump_pc.lean $V/self_S_input.txt > "$W/pcdump"
  python3 $V/cert/gen_cert.py "$W/pcdump"
  Testing/scripts/lean_run.sh $V/srclink/gen.lean $V/self_S_input.txt Nano/SelfHost/SrcLink 800
  clean
  echo "Cert ($(ls Nano/SelfHost/Cert | wc -l) files) and SrcLink ($(ls Nano/SelfHost/SrcLink | wc -l) files) regenerate identically"
}
s_arm() {
  $N/test_native.sh "$W/na" | tee "$W/na.out"
  grep -q "^fixpoint:" "$W/na.out"; grep -q "compiles C's source to B2.bin exactly" "$W/na.out"; grep -q "^all OK" "$W/na.out"
  cmp "$W/na/GA_arm.bin" $N/GA_arm.bin
  clean
  echo "GA_arm rebuilt = committed, GA_arm(own source) = GA_arm, B2_na(C) = B2.bin, examples + edge OK"
}
s_cross() { $N/cross_native.sh "$W/na"; }
s_subset() {
  [ -x Testing/scripts/subset_check.sh ] || { echo "Testing/scripts/subset_check.sh not present"; exit 77; }
  Testing/scripts/subset_check.sh
}
step fix s_fix
step gen s_gen
step arm s_arm
step cross s_cross
step subset s_subset
echo "sha256  B2.bin $(sha256sum $V/B2.bin | cut -c1-16)  GA_arm.bin $(sha256sum $N/GA_arm.bin | cut -c1-16)  B2_na $( [ -f "$W/na/B2_na.bin" ] && sha256sum "$W/na/B2_na.bin" | cut -c1-16)"
[ $fail = 0 ] && echo "SELFHOST GATE PASSED" || echo "SELFHOST GATE FAILED"
exit $fail
