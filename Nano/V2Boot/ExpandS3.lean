/- B₁: the v2 expander `mexpV` (Nano/V2/Expand.lean) in S3 form (Nano/V2Boot/Prelude.lean) and the bridge
`mexpVS_eq : mexpVS xs = mexpV xs` (inputs of length < 2^64). `mexpOpS` is `mexpOp` with `put ↦ putR`. -/
import Nano.V2S.Expand
import Nano.V2Boot.Prelude

namespace Nano.V2B
open Nano.V2S

/-- `mexpOp` on the reversed output -/
def mexpOpS (m x : UInt64) (o : List UInt8) : List UInt8 :=
  if m == 0 then putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR o 5) 31) 2) 3) 1) 31) 31) 3) 0) 28) 10) 0
  else if m == 1 then putR (putR (putR (putR o 4) 5) 28) 7
  else if m == 2 then putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR o 1) 5) 5) 8) 4) 6) 28) x) 14) 5) 5) 6
  else if m == 3 then putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR o 0) 31) 31) 248) 7) 0) 31) 12) 0) 10) 0) 255) 48) 0) 1) 0) 11) 5) 31) 0
  else if m == 4 then putR (putR (putR (putR o 8) 28) 28) 1
  else if m == 5 then putR (putR (putR (putR o 0) 5) 0) 0
  else if m == 6 then putR (putR (putR (putR (putR (putR (putR (putR o 1) 5) 5) 8) 6) 5) 5) x
  else if m == 7 then putR (putR (putR (putR o 3) 5) 31) x
  else if m == 8 then putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR o 3) 6) 31) 0) 3) 5) 31) 1) 8) 31) 31) 1) x) 5) 5) 6) 11) 5) 31) 0
  else if m == 9 then putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR (putR o 3) 5) 31) 0) 8) 31) 31) x) 11) 5) 31) 0
  else if m == 10 then putR (putR (putR (putR o 5) 6) 5) x
  else if m == 11 then putR (putR (putR (putR o 16) 6) 13) x
  else putR (putR (putR (putR o 48) 0) 1) 0

def mexpLS (f : UInt64) (xs : List UInt8) (i : UInt64) (o : List UInt8) : List UInt8 :=
  if h : f = 0 then o
  else if lenS xs < i + 2 then o
  else
    let m := rdS xs i
    let x := rdS xs (i + 1)
    mexpLS (f - 1) xs (i + 2) (mexpOpS m x o)
termination_by f.toNat
decreasing_by exact dec_lt h

def mexpVS (xs : List UInt8) : List UInt8 := (mexpLS (lenS xs) xs 0 []).reverse

theorem mexpOpS_rev (m x : UInt64) (o : List UInt8) : mexpOpS m x o.reverse = (mexpOp m x o).reverse := by
  unfold mexpOpS mexpOp; simp only [putR_rev, apply_ite List.reverse]

theorem mexpLS_eq (xs : List UInt8) : ∀ (n : Nat) (i : UInt64) (o : List UInt8), n < 2 ^ 64 →
    mexpLS n.toUInt64 xs i o.reverse = (mexpL n xs i o).reverse
  | 0, i, o, _ => by rw [mexpLS, dif_pos fuel_zero, mexpL]
  | n + 1, i, o, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    rw [mexpLS, dif_neg h1, mexpL, ite_lt_swap, lenS_eq]
    simp only [rdS_eq, h2, mexpOpS_rev]
    split
    · exact mexpLS_eq xs n _ _ (by omega)
    · rfl

theorem mexpVS_eq (xs : List UInt8) (h : xs.length < 2 ^ 64) : mexpVS xs = mexpV xs := by
  have := mexpLS_eq xs xs.length 0 [] h
  simp only [List.reverse_nil] at this
  rw [mexpVS, lenS_eq, show len xs = xs.length.toUInt64 from rfl, this, List.reverse_reverse]; rfl

end Nano.V2B
