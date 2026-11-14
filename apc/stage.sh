#!/bin/sh -e
# Stage the SOURCE-LEVEL parts (programs and their big-step facts; no machine model in them) of files that also
# import the RISC-V Sail model, so they can be checked next to the AlphaProof-Code semantics.  Text is taken
# unchanged from the repo; only the import line / enclosing namespace differ.  Output: Apc/Src/ (not committed).
cd "$(dirname "$0")"; R=..; O=Apc/Src; mkdir -p $O
cut_before() { awk -v pat="$2" 'index($0, pat) == 1 { exit } { print }' "$1"; }
{ echo "import Compiler.Stmt"; echo "namespace Proven.Mach"
  sed -n '/^theorem Exec.loop_of/,$p' $R/Riscv/Direct/Loop.lean | cut_before /dev/stdin "/-! ## Code"  | cut_before /dev/stdin "def iMv"
  sed -n '/^theorem Exec.det/,$p' $R/Riscv/Examples/LoopExamples.lean | cut_before /dev/stdin "theorem sumProg_wf" |
    sed 's/have hb : τ 1 = 0 := by simp \[Exp.denote\] at hc; exact hc ha/have hb : τ 1 = 0 := by have ha0 : ¬ τ 0 = 0#64 := ha; simpa [Exp.denote, ha0] using hc/'   # Lean 4.34 simp normal form (the only textual change)
  echo "end Proven.Mach"; } > $O/Loop.lean
{ echo "import Spec.ArrCode"; echo "namespace Proven"
  sed -n '/^theorem AExec.loop_inv/,$p' $R/Riscv/Direct/Arr.lean | cut_before /dev/stdin "end Proven"
  sed -n '/^namespace Proven/,$p' $R/Riscv/Examples/ArrExamples.lean | sed 1d | cut_before /dev/stdin "/-! ## Machine theorems" |
    sed 's/(by simpa using hc)/(by simpa [AExp.denote] using hc)/; s/(by simpa using hx)/(by simpa [AExp.denote] using hx)/'   # Lean 4.34
  echo "end Proven"; } > $O/ArrEx.lean
sed 's/^import Riscv.Examples.ArrExamples$/import Apc.Src.ArrEx/; s/(by simpa using hi)/(by simpa [AExp.denote] using hi)/' $R/Riscv/Direct/SortIns.lean > $O/SortIns.lean   # second edit: Lean 4.34
