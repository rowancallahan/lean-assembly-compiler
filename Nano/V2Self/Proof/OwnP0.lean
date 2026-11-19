/- Nano/V2Self/Proof/OwnP0: arithmetic and list facts for the soundness proof of the ownership stage `C.o41`
(Nano/V2Self/C/Own.lean) against `OwnSpec` (Testing/notes/NANO_V2_OWN.md).  Machine words that hold naturals are
written `u n` (= `UInt64.ofNat n`); the `uw` simp set turns their arithmetic / comparisons into Nat facts with bound
side conditions (`simp (disch := omega)`). -/
import Nano.V2Self.C.Own
namespace OwnP
open C

def u (n : Nat) : UInt64 := UInt64.ofNat n

theorem u_toNat {n : Nat} (h : n < 2 ^ 64) : (u n).toNat = n := by simp [u]; omega
theorem u_add (a b : Nat) : u a + u b = u (a + b) := (UInt64.ofNat_add a b).symm
theorem u_mul (a b : Nat) : u a * u b = u (a * b) := (UInt64.ofNat_mul a b).symm
theorem u_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) : u a - u b = u (a - b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ ((UInt64.le_iff_toNat_le).mpr (by rw [u_toNat ha, u_toNat (by omega)]; exact h)),
    u_toNat ha, u_toNat (by omega), u_toNat (by omega)]
theorem u_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (u a < u b) ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, u_toNat ha, u_toNat hb]
theorem u_sub' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) : u a - u b = u (a - b) := u_sub h ha
theorem u_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : u a = u b ↔ a = b := by
  constructor
  · intro h; have := congrArg UInt64.toNat h; rwa [u_toNat ha, u_toNat hb] at this
  · rintro rfl; rfl
theorem u_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (u a == u b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : u a ≠ u b := fun e => h ((u_inj ha hb).mp e)
    simp [h, this]
/-- every UInt64 literal as `u n` -/
theorem lit (n : Nat) : (no_index (OfNat.ofNat n : UInt64)) = u n := rfl
theorem u_lt' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (u a < u b) = (a < b) := propext (u_lt ha hb)
theorem u_zero : (0 : UInt64) = u 0 := rfl
theorem u_one : (1 : UInt64) = u 1 := rfl
theorem u_and3 {a : Nat} (ha : a < 2 ^ 64) : u a &&& 3 = u (a % 4) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, u_toNat ha, u_toNat (by omega)]
  show a &&& (3 : UInt64).toNat = a % 4
  exact Nat.and_two_pow_sub_one_eq_mod a 2
theorem u_shr2 {a : Nat} (ha : a < 2 ^ 64) : u a >>> 2 = u (a / 4) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, u_toNat ha, u_toNat (by omega)]
  simp [Nat.shiftRight_eq_div_pow]
theorem u_or01 (a b : Bool) : u (if a then 1 else 0) ||| u (if b then 1 else 0) = u (if a || b then 1 else 0) := by
  cases a <;> cases b <;> decide

/-! ## buffers as lists -/
theorem bget_u (b : Buf) {k : Nat} (h : k < 2 ^ 64) : bget b (u k) = b.getD k 0 := by
  simp only [bget, u_toNat h]
theorem bset_u (b : Buf) {k : Nat} (h : k < 2 ^ 64) (v : UInt64) : bset b (u k) v = b.set k v := by
  simp only [bset, u_toNat h]
theorem bsize_u (b : Buf) : bsize b = u b.length := rfl

theorem getD_set (b : Buf) (j k : Nat) (v : UInt64) :
    (b.set j v).getD k 0 = if j = k ∧ j < b.length then v else b.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : j = k
  · subst h1
    by_cases h2 : j < b.length
    · simp [h2]
    · simp [h2, List.getElem?_eq_none (show b.length ≤ j by omega)]
  · simp [h1]

theorem getD_append_single (b : Buf) (k : Nat) (v : UInt64) :
    (b ++ [v]).getD k 0 = if k = b.length then v else b.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  by_cases h : k < b.length
  · simp [h, show k ≠ b.length by omega]
  · by_cases h2 : k = b.length
    · subst h2; simp
    · have e1 : [v][k - b.length]? = none := List.getElem?_eq_none (by simp; omega)
      have e2 : b[k]? = none := List.getElem?_eq_none (by omega)
      simp [h, h2, e1, e2]

/-- `o0` = write at an index not beyond the end -/
def wr (b : Buf) (j : Nat) (v : UInt64) : Buf := if j < b.length then b.set j v else b ++ [v]

theorem o0_u (b : Buf) {j : Nat} (hj : j < 2 ^ 64) (hb : b.length < 2 ^ 64) (v : UInt64) : o0 b (u j) v = wr b j v := by
  unfold o0 wr
  by_cases h : j < b.length
  · simp only [bsize_u, u_lt hj hb, h, if_true, bset_u b hj]
  · simp only [bsize_u, u_lt hj hb, h, if_false, bpush]

theorem wr_getD {b : Buf} {j : Nat} (h : j ≤ b.length) (v : UInt64) (k : Nat) :
    (wr b j v).getD k 0 = if k = j then v else b.getD k 0 := by
  unfold wr; split
  · rename_i hj
    rw [getD_set]
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [hk, Ne.symm hk]
  · rw [getD_append_single]; have : j = b.length := by omega
    subst this; rfl

theorem wr_length {b : Buf} {j : Nat} (h : j ≤ b.length) (v : UInt64) : (wr b j v).length = max b.length (j + 1) := by
  unfold wr; split <;> simp <;> omega

theorem set_length' (b : Buf) (j : Nat) (v : UInt64) : (b.set j v).length = b.length := List.length_set

end OwnP
