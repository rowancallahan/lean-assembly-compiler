/- Emit the words of the compiled examples (for the QEMU tests in `apc/test`). -/
import Apc.Stack
open Proven Proven.Mach Proven.Apc
def hexs (ws : List (BitVec 32)) : String := " ".intercalate (ws.map fun w => String.ofList (Nat.toDigits 16 w.toNat))
#eval IO.println s!"gcd {hexs ((apc L0).code ((apc L0).compF gcdProg))}"
#eval IO.println s!"sum {hexs ((apc L0).code ((apc L0).compF sumProg))}"
#eval IO.println s!"sort {hexs sortCode}"
