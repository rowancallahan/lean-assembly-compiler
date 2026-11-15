#!/bin/sh -e
# Stage the SOURCE-LEVEL parts (programs and their big-step facts; no machine model in them) of files that also
# import the RISC-V Sail model, so they can be checked next to the AlphaProof-Code semantics.  Text is taken
# unchanged from the repo; only the import line / enclosing namespace differ.  Output: Apc/Src/ (not committed).
cd "$(dirname "$0")"; R=../..; O=Apc/Src; mkdir -p $O
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
# the spill-slot language and the merge sorts (source level only)
{ echo "import Spec.ArrCode"; echo "namespace Proven"
  sed -n '/^\/-! ## Expressions over variables/,$p' $R/Riscv/Direct/Arr2Code.lean | cut_before /dev/stdin "/-! ## Words"
  echo "end Proven"; } > $O/Arr2Code.lean
sed 's/^import Riscv.Direct.Arr2Code$/import Apc.Src.Arr2Code/' $R/Riscv/Direct/Arr2Src.lean > $O/Arr2Src.lean
cp $R/Riscv/Direct/SortMergeList.lean $O/SortMergeList.lean
sed 's/^import Riscv.Direct.Arr2Src$/import Apc.Src.Arr2Src/; s/^import Riscv.Direct.SortMergeList$/import Apc.Src.SortMergeList/; s/^import Riscv.Direct.SortIns$/import Apc.Src.SortIns/; s/dsimp only; rw/(try dsimp only); rw/' \
  $R/Riscv/Direct/SortMergeSrc.lean > $O/SortMergeSrc.lean
sed 's/^import Riscv.Direct.SortMergeSrc$/import Apc.Src.SortMergeSrc/; s/dsimp only; rw/(try dsimp only); rw/' $R/Riscv/Examples/MsortB.lean > $O/MsortB.lean
{ echo "import Apc.Src.Arr2Code"; echo "import Compiler.BLang"; echo "namespace Proven.Mach.Riscv"
  sed -n '/^def toMB/,$p' $R/Riscv/Back/BStmt.lean | cut_before /dev/stdin "/-! ## Same words"
  echo "end Proven.Mach.Riscv"; } > $O/ToM.lean
# middle files with `writable` hypotheses on the frame / 8-byte store laws (DeepMind's memory faults on stores to
# non-writable, e.g. executable, bytes; "in RAM" alone cannot be proved there): repo-root copies + mid.patch
M=Mid/Compiler; mkdir -p $M
for f in Frame BExp BStmt; do cp $R/Compiler/$f.lean $M/$f.lean; done
patch -s -d Mid -p1 < mid.patch
