import Nano.Parser.NumSpec
/-! `NumSpec.slotNatP` on C's own source (self_S_input.txt): the slots bound to `(if .. then 1 else 0)` and used only
in `== literal` are Nat (s22 `v`, o32 `k`/`r`, o38 `k`); parameter and `bget` slots are UInt64.
usage: lake env lean Testing/nano/v2self/fuzz/slotnat_test.lean -/
open ParSpec
def src : String := include_str "../self_S_input.txt"
def P : List DefA := ((lexAll (src.length + 1) src.toUTF8.toList).bind refParse).getD []
/-- the Nat slots of def `i` -/
def natSlots (i : Nat) : List Nat := match P[i]? with
  | some df => (List.range (df.nslots + 1)).filter (NumSpec.slotNatP P i)
  | none => []
#eval (P.length, natSlots 19, natSlots 190, natSlots 199)
