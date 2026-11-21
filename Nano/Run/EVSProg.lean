/- The def and program level, shared facts: `At.len`, `defT_ne`, and the per-def side conditions `DefOKS`.  The run
theorems for all outcomes (`defRunO`, `progRunO`, `gen_defs_runO`) are in CapProg.lean. -/
import Nano.Run.EVSRun
import Nano.Run.NdTop
namespace Templates
open CallProbe SimW SafeRun ParSpec

theorem At.len {C : List J} {pos : Nat} {l : List J} (h : At C pos l) (hl : l ≠ []) : pos + l.length ≤ C.length := by
  have hp : 0 < l.length := List.length_pos_iff.mpr hl
  have := h (l.length - 1) (by omega)
  rcases Nat.lt_or_ge (pos + (l.length - 1)) C.length with q | q
  · omega
  · rw [List.getElem?_eq_none q, List.getElem?_eq_getElem (by omega)] at this; simp at this

theorem defT_ne (S : SC) (e : Nd) (f q : Nat) : defT S e f q ≠ [] := by simp [defT, proA, pushA, push]

/-- the per-def facts of the safe program theorem -/
structure DefOKS (P : PC) (ds : List DefA) (C : List J) (k : Nat) : Prop where
  base : DefOK P ds C k
  op : OpV (dA ds k).body
  nl : (dA ds k).nslots < 251
  q : (dA ds k).nres < 251

end Templates
