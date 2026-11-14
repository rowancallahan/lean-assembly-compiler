#!/bin/bash
# Build the RISC-V side, check the axioms of the main theorems against expected-axioms.txt, and grep the
# non-model Lean sources for sorry / native_decide / bv_decide / axiom.  Run from anywhere; fails loudly.
set -eo pipefail
H=$(cd "$(dirname "$0")" && pwd); R=$(cd "$H/../.." && pwd); cd "$R"
export PATH=$HOME/.elan/bin:$PATH
fail() { echo "CHECK FAILED: $*" >&2; exit 1; }
echo "== lake build"; lake build Spec Compiler Riscv Arm || fail "lake build"
echo "== #print axioms"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
for g in a b c d e; do lake env lean "$H/axioms_$g.lean" > "$T/$g.txt" 2>&1 || { cat "$T/$g.txt"; fail "axioms_$g.lean"; }; done
cat "$T"/{a,b,c,d,e}.txt | tr -d '\n' | sed "s/'Proven/\n'Proven/g; s/ //g" | grep -v '^$' > "$T/got.txt"
if diff "$H/expected-axioms.txt" "$T/got.txt" > "$T/diff.txt"; then
  awk -F'dependsonaxioms:' '{n=split($2,a,","); print "  ok", $1, n, "axioms"}' "$T/got.txt"
else cat "$T/diff.txt"; fail "axioms differ from Testing/scripts/expected-axioms.txt"; fi
echo "== forbidden words (comments/strings ignored; Riscv/Legacy excluded: Sort.lean is stated with sorry)"
BAD=$(git ls-files 'Spec/*.lean' 'Compiler/*.lean' 'Riscv/*.lean' 'Arm/CompilerArm.lean' 'Arm/proofs/*.lean' 'Arm/shrink/*.lean' \
  | grep -v '^Riscv/Legacy/' | xargs python3 "$H/nocomment.py")
[ -z "$BAD" ] || { echo "$BAD"; fail "forbidden words"; }
echo "  none"
echo "== held-out spec (WARNING only while the owner tidies Spec/; re-freeze: Testing/scripts/spec_check.sh --freeze)"
"$H/spec_check.sh" || echo "WARNING: Spec/ changed since Spec/FROZEN.sha256"
echo "== statement fingerprints (WARNING only; re-freeze: Testing/scripts/statement_check.sh --freeze)"
"$H/statement_check.sh" || echo "WARNING: a headline statement or a definition it depends on changed"
echo "ALL CHECKS PASSED"
