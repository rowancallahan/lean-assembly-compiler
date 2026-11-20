#!/bin/sh -e
# Stage the SOURCE-LEVEL parts (programs and their big-step facts; no machine model in them) of files that also
# import the RISC-V Sail model, so they can be checked next to the AlphaProof-Code semantics.  Text is taken
# unchanged from the repo; only the import line / enclosing namespace differ.  Output: Apc/Src/ (not committed).
cd "$(dirname "$0")"; R=../..; O=Apc/Src; mkdir -p $O
cut_before() { awk -v pat="$2" 'index($0, pat) == 1 { exit } { print }' "$1"; }
{ echo "import Nano.Base.Compiler.Stmt"; echo "namespace Proven.Mach"
  sed -n '/^theorem Exec.loop_of/,$p' $R/Nano/Base/Riscv/Direct/Loop.lean | cut_before /dev/stdin "/-! ## Code"  | cut_before /dev/stdin "def iMv"
  sed -n '/^theorem Exec.det/,$p' $R/Nano/Base/Riscv/Examples/LoopExamples.lean | cut_before /dev/stdin "theorem sumProg_wf" |
    sed 's/have hb : τ 1 = 0 := by simp \[Exp.denote\] at hc; exact hc ha/have hb : τ 1 = 0 := by have ha0 : ¬ τ 0 = 0#64 := ha; simpa [Exp.denote, ha0] using hc/'   # Lean 4.34 simp normal form (the only textual change)
  echo "end Proven.Mach"; } > $O/Loop.lean
{ echo "import Spec.ArrCode"; echo "namespace Proven"
  sed -n '/^theorem AExec.loop_inv/,$p' $R/Nano/Base/Riscv/Direct/Arr.lean | cut_before /dev/stdin "end Proven"
  sed -n '/^namespace Proven/,$p' $R/Nano/Base/Riscv/Examples/ArrExamples.lean | sed 1d | cut_before /dev/stdin "/-! ## Machine theorems" |
    sed 's/(by simpa using hc)/(by simpa [AExp.denote] using hc)/; s/(by simpa using hx)/(by simpa [AExp.denote] using hx)/'   # Lean 4.34
  echo "end Proven"; } > $O/ArrEx.lean
sed 's/^import Nano.Base.Riscv.Examples.ArrExamples$/import Apc.Src.ArrEx/; s/(by simpa using hi)/(by simpa [AExp.denote] using hi)/' $R/Nano/Base/Riscv/Direct/SortIns.lean > $O/SortIns.lean   # second edit: Lean 4.34
# the spill-slot language and the merge sorts (source level only)
{ echo "import Spec.ArrCode"; echo "import Nano.Base.Compiler.MOp"; echo "namespace Proven"
  sed -n '/^\/-! ## Expressions over variables/,$p' $R/Nano/Base/Riscv/Direct/Arr2Code.lean | cut_before /dev/stdin "/-! ## Words"
  echo "end Proven"; } > $O/Arr2Code.lean
sed 's/^import Nano.Base.Riscv.Direct.Arr2Code$/import Apc.Src.Arr2Code/' $R/Nano/Base/Riscv/Direct/Arr2Src.lean > $O/Arr2Src.lean
cp $R/Nano/Base/Riscv/Direct/SortMergeList.lean $O/SortMergeList.lean
sed 's/^import Nano.Base.Riscv.Direct.Arr2Src$/import Apc.Src.Arr2Src/; s/^import Nano.Base.Riscv.Direct.SortMergeList$/import Apc.Src.SortMergeList/; s/^import Nano.Base.Riscv.Direct.SortIns$/import Apc.Src.SortIns/; s/dsimp only; rw/(try dsimp only); rw/' \
  $R/Nano/Base/Riscv/Direct/SortMergeSrc.lean > $O/SortMergeSrc.lean
sed 's/^import Nano.Base.Riscv.Direct.SortMergeSrc$/import Apc.Src.SortMergeSrc/; s/dsimp only; rw/(try dsimp only); rw/' $R/Nano/Base/Riscv/Examples/MsortB.lean > $O/MsortB.lean
{ echo "import Apc.Src.Arr2Code"; echo "import Nano.Base.Compiler.BLang"; echo "namespace Proven.Mach.Riscv"
  sed -n '/^def toMB/,$p' $R/Nano/Base/Riscv/Back/BStmt.lean | cut_before /dev/stdin "/-! ## Same words"
  echo "end Proven.Mach.Riscv"; } > $O/ToM.lean
# calls: `Computes` and the le8 facts of Nano/Base/Riscv/Back/Calls.lean, the source parts of the call examples
{ echo "import Nano.Base.Compiler.CLang"; echo "import Nano.Base.Compiler.Frame"; echo "import Spec.Encode"; echo "namespace Proven.Mach.Riscv"
  sed -n '/^theorem le8_byte/,$p' $R/Nano/Base/Riscv/Back/Calls.lean | cut_before /dev/stdin "/-! ## Checking well-formedness"
  sed -n '/^\/-- the source-level specification of a program/,$p' $R/Nano/Base/Riscv/Back/Calls.lean | cut_before /dev/stdin "/-- the machine code"
  echo "end Proven.Mach.Riscv"; } > $O/CallsSrc.lean
python3 cut.py $R/Nano/Base/Riscv/Examples/CallExamples.lean $O/CallExamples.lean 'Nano.Base.Riscv.Back.Calls=>Apc.Src.CallsSrc'
python3 cut.py $R/Nano/Base/Riscv/Examples/TreeEval.lean $O/TreeEval.lean 'Nano.Base.Riscv.Examples.CallExamples=>Apc.Src.CallExamples'
sed -i 's/(by simpa \[encB\] using hlt)/(by simp only [encB, List.length_map]; exact hlt)/' $O/TreeEval.lean   # Lean 4.34
# CRC-32 (source level): the model-free head of Implements1Ex.lean and of Crc.lean
cut_before $R/Nano/Base/Riscv/Examples/Implements1Ex.lean "/-! ## Machine theorems" > $O/i1.tmp
python3 cut.py $O/i1.tmp $O/Implements1Ex.lean 'Nano.Base.Riscv.Back.Implements1=>Apc.Src.ArrEx' 'Nano.Base.Riscv.Back.SortMerge=>Nano.Base.Compiler.BLang' \
  'Nano.Base.Riscv.Back.Arr=>Spec.Encode' 'Nano.Base.Riscv.Back.Keep=>'; echo "end Proven.Mach.Riscv" >> $O/Implements1Ex.lean
sed -i 's/(.load (by simp) (by simpa using \(h[a-z]*\)))/(.load (by simp) (by simpa [Mach.BExp.denote] using \1))/' $O/Implements1Ex.lean  # Lean 4.34
cut_before $R/Nano/Base/Riscv/Examples/Crc.lean "/-! ## The machine theorem" > $O/crc.tmp
python3 cut.py $O/crc.tmp $O/Crc.lean 'Nano.Base.Riscv.Examples.Implements1Ex=>Apc.Src.Implements1Ex'; echo "end Proven.Crc" >> $O/Crc.lean
sed -i 's/      · show xs.length - (e4 4).toNat < xs.length - (env 4).toNat/      · show xs.length - (e4 4).toNat < _/' $O/Crc.lean  # Lean 4.34
rm -f $O/i1.tmp $O/crc.tmp
# the (untrusted) register-assignment search of Nano/Base/Riscv/Back/OptB.lean, over `apcwF L0`
{ echo "import Apc.Wide"; echo "import Apc.Stack"; echo "import Nano.Base.Compiler.Opt.Color"; echo "namespace Proven.Mach.ApcS"
  echo "open Proven.Apc"
  sed -n '/^\/-! ## The (untrusted) choice of registers/,/^end Proven.Mach.Riscv/p' $R/Nano/Base/Riscv/Back/OptB.lean | sed '$d' |
    sed 's/rvwF/(apcwF L0)/g'
  echo "end Proven.Mach.ApcS"; } > $O/Search.lean
