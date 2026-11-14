#!/bin/bash
# Statement fingerprints of the headline theorems (cheap comparator substitute; Testing/scripts/stmt_hash.lean):
# the pretty-printed statement and the dependency closure of the statement (definitions' bodies, theorems' types)
# are hashed and compared with Testing/scripts/expected-statements.txt.
#   Testing/scripts/statement_check.sh            check (exit 1 + diff on any change)
#   Testing/scripts/statement_check.sh --freeze   re-freeze (after an intended change to a statement/definition)
#   Testing/scripts/statement_check.sh --list     also print each statement and its project-local definitions
set -eo pipefail
H=$(cd "$(dirname "$0")" && pwd); R=$(cd "$H/../.." && pwd); cd "$R"
export PATH=$HOME/.elan/bin:$PATH
L=""; [ "${1:-}" = "--list" ] && L="--list"
run() {
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.LoopExamples,Riscv.Direct.MemCompiler,Compiler.Front.PipeMachine \
    Proven.compile_ok Proven.compileS_ok Proven.gcd_ok Proven.compileStore_ok Proven.compileP_ok
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Direct.SortMergeMachine \
    Proven.compileAF_ok Proven.sortCode_implements Proven.msortCode_implements
}
if [ -n "$L" ]; then run; exit 0; fi
T=$(mktemp); trap 'rm -f "$T"' EXIT
run > "$T"
if [ "${1:-}" = "--freeze" ]; then cp "$T" "$H/expected-statements.txt"; echo "re-frozen: $(wc -l < "$T") statements"; exit 0; fi
if D=$(diff "$H/expected-statements.txt" "$T"); then echo "  $(wc -l < "$T") statements and their definition closures unchanged"
else echo "$D"; echo "STATEMENT CHECK: a headline statement or a definition it depends on changed (re-freeze: Testing/scripts/statement_check.sh --freeze)"; exit 1; fi
