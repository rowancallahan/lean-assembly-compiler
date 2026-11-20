import LeanRV64D
open Lean
partial def strip (e : Expr) : Expr := e.replace fun
  | .mdata _ b => some (strip b)
  | .lam _ t b bi => some (.lam `_ (strip t) (strip b) bi)
  | .forallE _ t b bi => some (.forallE `_ (strip t) (strip b) bi)
  | .letE _ t v b _ => some (.letE `_ (strip t) (strip v) (strip b) false)
  | _ => none
#eval show MetaM Unit from do
  for n in [``LeanRV64D.Functions.check_stateen_bit, ``LeanRV64D.Functions.get_xLPE] do
    let ci ← getConstInfo n
    IO.println s!"== {n}\n{(strip ci.value!)}"
