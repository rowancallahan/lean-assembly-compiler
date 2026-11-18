/- Sail simulations for the J instructions of the expression templates: R-type ALU (`alu`), `slli`, `lbu`
(Bridge part 2 continued; same style as SimW.sim_addi/sim_ld).  The `lbu` byte is read out of an aligned 8-byte cell of the
work block (the input lives in the work block: `wok` of the containing cell). -/
import Nano.V2Self.Proof.SimW
namespace SimW
open Proven Nano.V2B

/-- J's ALU numbering (Gen's BIN: add 1 sub 2 mul 3 and 4 or 5 sll 6 srl 7 xor 8) as nano-v2's `ROp` -/
def ropOf (op : Nat) : ROp :=
  if op = 1 then .add else if op = 2 then .sub else if op = 3 then .mul else if op = 4 then .and
  else if op = 5 then .or else if op = 6 then .sll else if op = 7 then .srl else .xor

/- TODO (in progress): sim_aluW / sim_slliW / sim_lbuW; the lemmas follow once the Sail build finishes. -/

end SimW
