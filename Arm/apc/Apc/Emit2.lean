/- Emit the words of the frame / call / optimised examples (for `test/ext_test.py`): `lake env lean Apc/Emit2.lean`. -/
import Apc.Opt
import Apc.Calls
open Proven Proven.Mach Proven.Apc
def hexs (ws : List (BitVec 32)) : String := " ".intercalate (ws.map fun w => String.ofList (Nat.toDigits 16 w.toNat))
#eval IO.println s!"msort {hexs msortCode}"
#eval IO.println s!"msortO {hexs msortCodeO}"
#eval IO.println s!"crc {hexs crcCode}"
#eval IO.println s!"crcO {hexs crcCodeO}"
#eval IO.println s!"sumTo {hexs (callsCode L0 Riscv.sumToProg 0)}"
#eval IO.println s!"fib {hexs (callsCode L0 Riscv.fibProg 0)}"
#eval IO.println s!"isEven {hexs (callsCode L0 Riscv.evenProg 0)}"
#eval IO.println s!"tree {hexs (callsCode L0 Riscv.treeProg 0)}"
