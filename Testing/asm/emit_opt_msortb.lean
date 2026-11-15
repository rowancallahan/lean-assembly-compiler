-- words of the branchy merge sort `msortCodeO2` (`Riscv/Examples/MsortBOpt.lean`), to
-- `Testing/asm/opt-words/msortb.words` (bench.py, msort_test.py with MSORT=msortb) and
-- `Testing/asm/impl1-opt-words/msortb.words` (impl1_test.py msortb)
import Riscv.Examples.MsortBOpt
open Proven
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
#eval show IO Unit from do
  let ws := msortCodeO2
  let ok := match compileOptB 7 [0, 2, 3] msortProgB with | .ok v => v == ws | .error _ => false
  for d in ["opt-words", "impl1-opt-words"] do
    IO.FS.writeFile s!"Testing/asm/{d}/msortb.words" (String.intercalate "\n" (ws.map hex8) ++ "\n")
  IO.println s!"msortb: {ws.length} words, optimised path: {ok}"
