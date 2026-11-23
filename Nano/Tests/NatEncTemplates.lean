/- Checks (`#guard`, evaluated at build time) that the native encoder's specification (Nano/Run/NatEnc.lean) accepts
Gen's J templates: every template parses into atoms (`atomize`) whose side conditions `NTm.ok` hold, and a small whole
program (stubs, start code, a definition with array get / set, byte read, mul, epilogue) is encoded (`natEncJ`, so
the jump targets are atom boundaries).  A failing line names the template the spec does not cover. -/
import Nano.Run.NatEnc
import Nano.Run.Heap
import Nano.Run.EVXL
import Nano.Run.CallA
import Nano.Run.StartCode
namespace JT.NatEncTest
open CallProbe Templates

/-- the template parses and every atom is `ok` -/
def tOk (l : List J) : Bool :=
  match atomize l.length l with
  | some ts => ts.all NTm.ok
  | none => false

#guard tOk (pushA 1 20 5)
#guard tOk (liT 5 7)
#guard tOk (liT 5 0x123456789ABCDEF0)
#guard tOk (constT 1 20 4096)
#guard tOk (localT 1 2 0 20 3)
#guard tOk (localT 1 2 40 20 2)
#guard tOk (popN 2 0 3)
#guard tOk (popN 2 40 2)
#guard tOk (binT 1)
#guard tOk (binT 3)
#guard tOk (binT 8)
#guard tOk (lenT 1 20)
#guard tOk rdT
#guard tOk (bnewT 1 20 2097152)
#guard tOk bsizeT
#guard tOk bgetT
#guard tOk bsetT
#guard tOk (bpushT 6 20)
#guard tOk (ifHeadG 1 9)
#guard tOk (ifHeadG 2 9)
#guard tOk (loopHead 2 7)
#guard tOk (loopHead 0 7)
#guard tOk (loopDec 2)
#guard tOk (proA 1 43 2)
#guard tOk (proA 1 43 0)
#guard tOk (epi 1 1)
#guard tOk (epi 2 5)
#guard tOk (stubJ 11)
#guard tOk (startJ 11 43)

/-- stubs, start code, one definition -/
def prog : List J :=
  stubJ 11 ++ startJ 11 43 ++ proA 1 43 2 ++ bgetT ++ bsetT ++ rdT ++ binT 3 ++ epi 1 1

#guard (natEncJ prog).isSome
#guard ((natEncJ prog).map List.length).getD 0 % 4 == 0

end JT.NatEncTest
