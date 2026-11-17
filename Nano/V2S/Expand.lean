/- nano v2 source: the micro-op expander `mexp` (Nano/Expand.lean) as a byte machine (Testing/notes/NANO_V2_SRC.md).
Constructs: UInt64 `==`, `≤`, `+`, `if`, `let`, calls, fuel recursion, `rd`, `len`, `put`.
Bridge: `mexpV_eq : mexpV xs = mexp xs` for every input of length < 2^32. -/
import Nano.ExpandM
import Nano.V2.Asm

namespace Nano.V2

/-- the records of micro-op `[m, x]` appended to `o` -/
def mexpOp (m x : UInt64) (o : List UInt8) : List UInt8 :=
  if m == 0 then put (put (put (put (put (put (put (put (put (put (put (put o 5) 31) 2) 3) 1) 31) 31) 3) 0) 28) 10) 0
  else if m == 1 then put (put (put (put o 4) 5) 28) 7
  else if m == 2 then put (put (put (put (put (put (put (put (put (put (put (put o 1) 5) 5) 8) 4) 6) 28) x) 14) 5) 5) 6
  else if m == 3 then put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put o 0) 31) 31) 248) 7) 0) 31) 12) 0) 10) 0) 255) 48) 0) 1) 0) 11) 5) 31) 0
  else if m == 4 then put (put (put (put o 8) 28) 28) 1
  else if m == 5 then put (put (put (put o 0) 5) 0) 0
  else if m == 6 then put (put (put (put (put (put (put (put o 1) 5) 5) 8) 6) 5) 5) x
  else if m == 7 then put (put (put (put o 3) 5) 31) x
  else if m == 8 then put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put o 3) 6) 31) 0) 3) 5) 31) 1) 8) 31) 31) 1) x) 5) 5) 6) 11) 5) 31) 0
  else if m == 9 then put (put (put (put (put (put (put (put (put (put (put (put o 3) 5) 31) 0) 8) 31) 31) x) 11) 5) 31) 0
  else if m == 10 then put (put (put (put o 5) 6) 5) x
  else if m == 11 then put (put (put (put o 16) 6) 13) x
  else put (put (put (put o 48) 0) 1) 0

/-- one micro-op `[m, x]` at input position `i` per step -/
def mexpL : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, _, _, o => o
  | n + 1, xs, i, o =>
    if i + 2 ≤ len xs then
      let m := rd xs i
      let x := rd xs (i + 1)
      mexpL n xs (i + 2) (mexpOp m x o)
    else o

/-- **the expander, nano v2 source** -/
def mexpV (xs : List UInt8) : List UInt8 := mexpL xs.length xs 0 []

/-! ## bridge -/

set_option maxRecDepth 4000 in
theorem mexpOp_eq (m x : UInt8) (o : List UInt8) : mexpOp m.toUInt64 x.toUInt64 o = o ++ mexp [m, x] := by
  simp only [mexpOp, mexp, beq8 m (nat_lit 0) (by decide), beq8 m (nat_lit 1) (by decide), beq8 m (nat_lit 2) (by decide), beq8 m (nat_lit 3) (by decide), beq8 m (nat_lit 4) (by decide), beq8 m (nat_lit 5) (by decide), beq8 m (nat_lit 6) (by decide), beq8 m (nat_lit 7) (by decide), beq8 m (nat_lit 8) (by decide), beq8 m (nat_lit 9) (by decide), beq8 m (nat_lit 10) (by decide), beq8 m (nat_lit 11) (by decide)]
  simp only [put, List.append_assoc, List.cons_append, List.nil_append, apply_ite (fun l => o ++ l),
    UInt8.toUInt8_toUInt64, UInt64.toUInt8_ofNat]

theorem mexp_short : ∀ l : List UInt8, l.length < 2 → mexp l = []
  | [], _ => by simp [mexp]
  | [_], _ => by simp [mexp]
  | _ :: _ :: _, h => by simp at h; omega

theorem mexpL_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n : Nat) (i : UInt64) (o : List UInt8),
    i.toNat ≤ xs.length → xs.length < i.toNat + 2 * n + 2 → mexpL n xs i o = o ++ mexp (xs.drop i.toNat)
  | 0, i, o, _, h2 => by
    rw [mexpL, mexp_short _ (by simp; omega)]; simp
  | n + 1, i, o, h1, h2 => by
    rw [mexpL]
    by_cases hc : i + 2 ≤ len xs
    · have h4 : i.toNat + 2 ≤ xs.length := by
        unfold len at hc; rw [UInt64.le_iff_toNat_le] at hc; simp at hc; omega
      rw [if_pos hc]
      have r0 : rd xs i = (xs[i.toNat]'(by omega)).toUInt64 := by
        unfold rd; simp [List.getElem?_eq_getElem (show i.toNat < xs.length by omega)]
      have r1 := rd_at xs i 1 hx (by omega)
      have e1 : (1 : Nat).toUInt64 = 1 := rfl
      rw [e1] at r1
      have hd : xs.drop i.toNat = xs[i.toNat] :: xs[i.toNat + 1] :: xs.drop (i.toNat + 2) := by
        rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]; rfl
      have hi2 : (i + 2).toNat = i.toNat + 2 := by simp; omega
      simp only []
      rw [r0, r1, mexpOp_eq, mexpL_eq xs hx n (i + 2) _ (by rw [hi2]; omega) (by rw [hi2]; omega), hi2]
      conv => rhs; rw [hd, Nano.MX.mexp_cons]
      simp; rfl
    · have h4 : ¬ i.toNat + 2 ≤ xs.length := by
        intro q; apply hc; unfold len; rw [UInt64.le_iff_toNat_le]; simp; omega
      rw [if_neg hc, mexp_short _ (by simp; omega)]; simp

/-- **the bridge**: the nano v2 source is the expander, on every input of length < 2^32 -/
theorem mexpV_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : mexpV xs = mexp xs := by
  unfold mexpV; rw [mexpL_eq xs hx _ 0 [] (by simp) (by simp; omega)]; simp

end Nano.V2
