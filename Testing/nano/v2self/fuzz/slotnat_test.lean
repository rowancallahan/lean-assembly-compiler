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
-- defs 19, 190, 199 are s22, o32, o38 (0-based order of the `def`s in self_S_input.txt)
#guard natSlots 19 == [5]     -- s22: v := if .. then (if .. then 1 else 0) else 1; used in `v == 0`
#guard natSlots 190 == [39]   -- o32: k (or r) := (if .. then 0 else .. 1 else 0); used in `== 1`
#guard natSlots 199 == [13]   -- o38: k := (if 1048575 < p then 1 else ..); used in `k == 1`
#guard !NumSpec.slotNatP P 19 0   -- s22's parameter q (UInt64, read by `rd x q`)
#guard !NumSpec.slotNatP P 199 8  -- o38's i := bget a 0 (UInt64)
