#!/bin/bash
# (three runs: LoopExamples / ArrExamples and Pipe / Arr2Code cannot be imported together)
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
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.LoopExamples,Riscv.Direct.MemCompiler \
    Proven.compile_ok Proven.compileS_ok Proven.gcd_ok Proven.compileStore_ok
  lake env lean --run "$H/stmt_hash.lean" $L Compiler.Front.PipeMachine Proven.compileP_ok
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Direct.SortMergeMachine \
    Proven.compileAF_ok Proven.sortCode_implements Proven.msortCode_implements
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.Crc,Riscv.Examples.Implements1Ex \
    Proven.Crc.crc32_implements1 Proven.sortCode_implements1 Proven.msortCode_implements1 \
    Proven.Mach.Riscv.take_implements1 Proven.Mach.Riscv.inc_implements1 Proven.Mach.Riscv.sum_implements1 \
    Proven.Mach.MachineF.compBF_ok
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.Implements1Pipe Proven.compileP_implements1
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Back.Opt Proven.compileO_ok Proven.compileFO_ok
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Back.OptArr,Riscv.Back.OptB \
    Proven.compileAFO_ok Proven.compileBFO_ok Proven.Mach.WideF.optB_ok
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.Implements1Opt \
    Proven.Crc.crc32_implements1O Proven.sortCode_implements1O Proven.msortCode_implements1O \
    Proven.Mach.Riscv.take_implements1O Proven.Mach.Riscv.inc_implements1O Proven.Mach.Riscv.sum_implements1O
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.MsortBOpt Proven.msortCodeO2_implements1
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.InsB Proven.Mach.Riscv.insCodeO_implements1
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.GcdOpt Proven.gcdO_ok Proven.gcdO_ok_nat
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.PipeExamples Proven.compileX1_ok \
    Proven.PipeEx.revinc5_implements1 Proven.PipeEx.filtsort_implements1 Proven.PipeEx.any3_implements1 \
    Proven.PipeEx.min_implements1 Proven.PipeEx.sum64_implements1
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.CallExamples Proven.Mach.MachineC.compP_ok \
    Proven.Mach.Riscv.callsCode_implements Proven.Mach.Riscv.sumTo_implements Proven.Mach.Riscv.fib_implements \
    Proven.Mach.Riscv.isEven_implements
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Examples.TreeEval Proven.Mach.MachineC.execC_ok \
    Proven.Mach.Riscv.treeEval_implements
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Frontx.Machine Proven.Frontx.implements1_res \
    Proven.Frontx.Ex.crcRaw.implements1 Proven.Frontx.Ex.b64All.implements1 Proven.Frontx.Ex.findNL.implements1 Proven.Frontx.Ex.be32At0.implements1 \
    Proven.Frontx.Ex.tailSum.implements1 Proven.Frontx.Ex.nonTailSum.implements1 Proven.Frontx.Ex.tailLength.implements1 Proven.Frontx.Ex.bookLength.implements1
  lake env lean --run "$H/stmt_hash.lean" $L Riscv.Frontx.IndExamples Proven.Mach.Ind.ind_ok \
    Proven.Frontx.IndEx.BinTree.count.implements1 Proven.Frontx.IndEx.BinTree.mirror.implements1 \
    Proven.Frontx.IndEx.BinTree.graftLeft.implements1 Proven.Frontx.IndEx.Pos.toNat.implements1 \
    Proven.Frontx.IndEx.Pos.plus.implements1 Proven.Frontx.IndEx.NonTail.sum.implements1 Proven.Frontx.IndEx.Tail.sum.implements1 \
    Proven.Frontx.IndEx.Tail.reverse.implements1 List.append.implements1 ConLeche.levelHasParam.implements1 \
    ConLeche.Level.isNeverZero.implements1
}
if [ -n "$L" ]; then run; exit 0; fi
T=$(mktemp); trap 'rm -f "$T"' EXIT
run > "$T"
if [ "${1:-}" = "--freeze" ]; then cp "$T" "$H/expected-statements.txt"; echo "re-frozen: $(wc -l < "$T") statements"; exit 0; fi
if D=$(diff "$H/expected-statements.txt" "$T"); then echo "  $(wc -l < "$T") statements and their definition closures unchanged"
else echo "$D"; echo "STATEMENT CHECK: a headline statement or a definition it depends on changed (re-freeze: Testing/scripts/statement_check.sh --freeze)"; exit 1; fi
