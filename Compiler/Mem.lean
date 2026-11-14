/- Model-free memory reasoning for the middle layer: contiguous regions, reading `n` bytes, single-byte
writes and the separation facts the array compiler needs.  (`Proven/MemModel.lean` cannot be imported:
it imports `Proven/Spec.lean`, hence the Sail model; this is the minimal function-based copy.) -/
import Compiler.Iface

namespace Proven.Mach

structure Region where
  base : Nat
  len : Nat

def disjoint (r₁ r₂ : Region) : Prop := r₁.base + r₁.len ≤ r₂.base ∨ r₂.base + r₂.len ≤ r₁.base

/-- the `n` bytes at `a` -/
def bytes (m : Mem) (a : Nat) : Nat → List (Option (BitVec 8))
  | 0 => []
  | n + 1 => m a :: bytes m (a + 1) n

/-- memory outside the regions `R` unchanged -/
def Out (R : List Region) (m m' : Mem) : Prop := ∀ a, (∀ r ∈ R, a < r.base ∨ r.base + r.len ≤ a) → m' a = m a

theorem Out.refl (R : List Region) (m : Mem) : Out R m m := fun _ _ => rfl

theorem Out.trans {R : List Region} {m₁ m₂ m₃ : Mem} (h₁ : Out R m₁ m₂) (h₂ : Out R m₂ m₃) : Out R m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem Out.of_eq {R : List Region} {m m' : Mem} (h : m' = m) : Out R m m' := fun _ _ => by rw [h]

theorem bytes_congr {m m' : Mem} : ∀ {a n : Nat}, (∀ j, j < n → m' (a + j) = m (a + j)) → bytes m' a n = bytes m a n
  | _, 0, _ => rfl
  | a, n + 1, h => by
    show m' a :: bytes m' (a + 1) n = m a :: bytes m (a + 1) n
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    have ih : bytes m' (a + 1) n = bytes m (a + 1) n := bytes_congr fun j hj => by
      rw [show a + 1 + j = a + (j + 1) by omega]; exact h (j + 1) (by omega)
    rw [h0, ih]

theorem bytes_upd_out {m : Mem} {x a n : Nat} {v : BitVec 8} (h : ∀ j, j < n → a + j ≠ x) :
    bytes (m.upd x v) a n = bytes m a n :=
  bytes_congr fun j hj => by unfold Mem.upd; rw [ite_neg (h j hj)]

theorem bytes_upd_in {m : Mem} {v : BitVec 8} : ∀ {a n i : Nat}, i < n →
    bytes (m.upd (a + i) v) a n = (bytes m a n).set i (some v)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | a, n + 1, 0, _ => by
    show m.upd (a + 0) v a :: bytes (m.upd (a + 0) v) (a + 1) n = some v :: bytes m (a + 1) n
    rw [bytes_upd_out fun j _ => by omega]
    unfold Mem.upd; rw [ite_pos (by omega)]
  | a, n + 1, i + 1, h => by
    show m.upd (a + (i + 1)) v a :: bytes (m.upd (a + (i + 1)) v) (a + 1) n =
      m a :: (bytes m (a + 1) n).set i (some v)
    rw [show a + (i + 1) = a + 1 + i by omega, bytes_upd_in (by omega)]
    unfold Mem.upd; rw [ite_neg (by omega)]

theorem get_of_bytes {m : Mem} : ∀ {a n : Nat} {l : List (BitVec 8)}, bytes m a n = l.map some →
    ∀ {i : Nat} (hi : i < l.length), m (a + i) = some l[i]
  | _, 0, [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _, 0, _ :: _, h, _, _ => nomatch h
  | _, _ + 1, [], h, _, _ => nomatch h
  | a, n + 1, x :: l, h, i, hi => by
    have h' : m a = some x ∧ bytes m (a + 1) n = l.map some := List.cons.inj h
    cases i with
    | zero => exact h'.1
    | succ i =>
      have := get_of_bytes h'.2 (i := i) (by simp only [List.length_cons] at hi; omega)
      rw [show a + (i + 1) = a + 1 + i by omega]; exact this

theorem length_bytes (m : Mem) : ∀ (a n : Nat), (bytes m a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by show (bytes m (a + 1) n).length + 1 = n + 1; rw [length_bytes m (a + 1) n]

/-! ## Lists of blocks -/

theorem getD_get {α : Type} : ∀ (H : List (List α)) {b : Nat} (hb : b < H.length), H[b]?.getD [] = H[b]
  | _ :: _, 0, _ => rfl
  | _ :: t, b + 1, hb => getD_get t (b := b) (by simp only [List.length_cons] at hb; omega)

theorem getD_set_self {α : Type} : ∀ (H : List (List α)) {b : Nat} (x : List α), b < H.length →
    (H.set b x)[b]?.getD [] = x
  | _ :: _, 0, _, _ => rfl
  | _ :: t, b + 1, x, hb => getD_set_self t (b := b) x (by simp only [List.length_cons] at hb; omega)

theorem getD_set_ne {α : Type} : ∀ (H : List (List α)) {b b' : Nat} (x : List α), b' ≠ b →
    (H.set b x)[b']? = H[b']?
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: t, b + 1, b' + 1, x, h => getD_set_ne t (b := b) (b' := b') x (fun e => h (by rw [e]))

theorem map_set {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat) (x : α), (l.set i x).map f = (l.map f).set i (f x)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: t, i + 1, x => by
    show f a :: (t.set i x).map f = f a :: (t.map f).set i (f x)
    rw [map_set f t i x]

theorem getD_mem {α : Type} {d : α} : ∀ (l : List α) {b : Nat}, b < l.length → l.getD b d ∈ l
  | a :: t, 0, _ => by rw [List.getD_cons_zero]; exact List.mem_cons_self
  | a :: t, b + 1, hb => by
    rw [List.getD_cons_succ]
    exact List.mem_cons_of_mem a (getD_mem t (b := b) (by simp only [List.length_cons] at hb; omega))

theorem pairwise_get {R : List Region} (h : R.Pairwise disjoint) {i j : Nat} (hi : i < R.length) (hj : j < R.length)
    (hij : i ≠ j) : disjoint R[i] R[j] := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact List.pairwise_iff_getElem.mp h i j hi hj hlt
  · have := List.pairwise_iff_getElem.mp h j i hj hi hlt
    unfold disjoint at this ⊢; omega

end Proven.Mach
