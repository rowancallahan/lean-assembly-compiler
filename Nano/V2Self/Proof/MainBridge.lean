/- Nano/V2Self/Proof/MainBridge: the Sem ⇐ sv bridge, layer 1 — the heap representation of `Sem`'s buffers in E's heap
image (`Templates.Hp`, Proof/HeapEV.lean) and the per-prim agreement of E's machine-level prims with `Sem`'s.
`BufAt hb κ H a l`: at address `a` a buffer [len][cap = κ][κ words] whose first |l| words are `l`. -/
import Nano.V2Self.Proof.MainTy
import Nano.V2Self.Proof.NdSem

namespace NanoMain
open Templates

def BufAt (hb κ : Nat) (H : Hp) (a : UInt64) (l : List UInt64) : Prop :=
  hb ≤ a.toNat ∧ a.toNat % 8 = 0 ∧ a.toNat + 16 + 8 * κ ≤ H.top ∧ a.toNat + 16 + 8 * κ < 2 ^ 62 ∧ l.length ≤ κ ∧
  κ < 2 ^ 40 ∧ H.m a.toNat = some (UInt64.ofNat l.length) ∧ H.m (a.toNat + 8) = some (UInt64.ofNat κ) ∧
  ∀ i (h : i < l.length), H.m (a.toNat + 16 + 8 * i) = some l[i]

theorem hread_of {hb : Nat} {H : Hp} {a : Nat} {v : UInt64} (h1 : hb ≤ a) (h2 : a < H.top) (h : H.m a = some v) :
    hread hb H a = some v := by simp [hread, h1, h2, h]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem bufInfo_at {hb κ : Nat} {H : Hp} {a : UInt64} {l : List UInt64} (h : BufAt hb κ H a l) :
    bufInfo hb H a = some (UInt64.ofNat l.length, UInt64.ofNat κ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h
  have e1 : hread hb H a.toNat = some (UInt64.ofNat l.length) := hread_of h1 (by omega) h7
  have e2 : hread hb H (a.toNat + 8) = some (UInt64.ofNat κ) := hread_of (by omega) (by omega) h8
  have k1 : (UInt64.ofNat κ).toNat = κ := toNat_ofNat_lt (by omega)
  have k2 : (UInt64.ofNat l.length).toNat = l.length := toNat_ofNat_lt (by omega)
  simp only [bufInfo, h1, h2, and_self, if_true, e1, e2, Option.bind_some, k1, k2]
  rw [if_pos ⟨h5, h3⟩]

/-- BSIZE -/
theorem bsize_at {hb κ : Nat} {H : Hp} {a : UInt64} {l : List UInt64} (h : BufAt hb κ H a l) (sp : Nat) :
    bsizeF hb a sp H = some (UInt64.ofNat l.length, H) := by
  obtain ⟨h1, -, h3, -, h5, -, h7, -⟩ := h
  simp [bsizeF, hread_of h1 (by omega) h7]

/-- BGET (out of range ⇒ 0, like `List.getD`) -/
theorem bget_at {hb κ : Nat} {H : Hp} {a : UInt64} {l : List UInt64} (h : BufAt hb κ H a l) (i : UInt64) (sp : Nat) :
    bgetF hb a i sp H = some (l.getD i.toNat 0, H) := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7, -, h9⟩ := h
  have k2 : (UInt64.ofNat l.length).toNat = l.length := toNat_ofNat_lt (by omega)
  simp only [bgetF, hread_of h1 (by omega) h7, Option.bind_some, k2]
  by_cases hi : i.toNat < l.length
  · rw [if_pos hi, if_pos (by omega), hread_of (by omega) (by omega) (h9 _ hi)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · rw [if_neg hi]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ i.toNat)]

/-- the cells of a buffer region -/
def InBuf (κ : Nat) (a : UInt64) (x : Nat) : Prop := a.toNat ≤ x ∧ x < a.toNat + 16 + 8 * κ

/-- BPUSH / PUT below capacity: the same address now holds `l ++ [v]`; only the buffer's own cells change -/
theorem bpush_at {hb κ : Nat} {H : Hp} {a : UInt64} {l : List UInt64} (h : BufAt hb κ H a l) (hl : l.length < κ)
    (v : UInt64) (sp : Nat) : ∃ H', bpushF hb a v sp H = some (a, H') ∧ BufAt hb κ H' a (l ++ [v]) ∧ H'.top = H.top ∧
      ∀ x, ¬ InBuf κ a x → H'.m x = H.m x := by
  have hi := bufInfo_at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have k1 : (UInt64.ofNat κ).toNat = κ := toNat_ofNat_lt (by omega)
  have k2 : (UInt64.ofNat l.length).toNat = l.length := toNat_ofNat_lt (by omega)
  simp only [bpushF, hi, Option.bind_some, k1, k2]
  rw [if_pos ⟨hl, by omega⟩]
  refine ⟨_, rfl, ⟨h1, h2, h3, h4, by simp; omega, h6, ?_, ?_, ?_⟩, rfl, ?_⟩
  · simp only [if_true, List.length_append, List.length_singleton]
    congr 1; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, k2, toNat_ofNat_lt (by omega)]
    simp; omega
  · simp only [show a.toNat + 8 ≠ a.toNat by omega, if_false, show a.toNat + 8 ≠ a.toNat + 16 + 8 * l.length by omega, h8]
  · intro i hi
    simp only [show a.toNat + 16 + 8 * i ≠ a.toNat by omega, if_false]
    by_cases e : i = l.length
    · subst e; simp
    · have hi' : i < l.length := by simp at hi; omega
      rw [if_neg (by omega), h9 i hi', List.getElem_append_left hi']
  · intro x hx; simp only [InBuf] at hx
    dsimp only; rw [if_neg (by omega), if_neg (by omega)]

/-- BSET: in range ⇒ `l.set i v` at the same address, else unchanged (like `List.set`) -/
theorem bset_at {hb κ : Nat} {H : Hp} {a : UInt64} {l : List UInt64} (h : BufAt hb κ H a l) (i v : UInt64) (sp : Nat) :
    ∃ H', bsetF hb a i v sp H = some (a, H') ∧ BufAt hb κ H' a (l.set i.toNat v) ∧ H'.top = H.top ∧
      ∀ x, ¬ InBuf κ a x → H'.m x = H.m x := by
  have hi := bufInfo_at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have k2 : (UInt64.ofNat l.length).toNat = l.length := toNat_ofNat_lt (by omega)
  simp only [bsetF, hi, Option.bind_some, k2]
  by_cases hil : i.toNat < l.length
  · rw [if_pos hil, if_pos (by omega)]
    refine ⟨_, rfl, ⟨h1, h2, h3, h4, by simp; omega, h6, ?_, ?_, ?_⟩, rfl, ?_⟩
    · dsimp only; rw [if_neg (by omega)]; simpa using h7
    · dsimp only; rw [if_neg (by omega)]; exact h8
    · intro j hj
      simp only [List.length_set] at hj
      by_cases e : j = i.toNat
      · subst e; simp
      · dsimp only; rw [if_neg (by omega), h9 j hj, List.getElem_set_ne (by omega)]
    · intro x hx; simp only [InBuf] at hx; dsimp only; rw [if_neg (by omega)]
  · rw [if_neg hil]
    refine ⟨H, rfl, ?_, rfl, fun _ _ => rfl⟩
    rw [List.set_eq_of_length_le (by omega)]; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- BNEW: a fresh empty buffer at the old heap top; older cells unchanged -/
theorem bnew_at {hb κ : Nat} {H H' : Hp} {a : UInt64} {env : Env} {sp : Nat} (hh : hb ≤ H.top) (h8 : H.top % 8 = 0)
    (h : bnewS κ env sp H = some (a, H')) :
    BufAt hb κ H' a [] ∧ H.top + 16 + 8 * κ = H'.top ∧ a.toNat = H.top ∧ ∀ x, x < H.top → H'.m x = H.m x := by
  unfold bnewS at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have ht : (UInt64.ofNat H.top).toNat = H.top := toNat_ofNat_lt (by omega)
    refine ⟨⟨by omega, by omega, by dsimp only; omega, by omega, by simp, hc.2.2, ?_, ?_, by simp⟩, by dsimp only; omega, ht, ?_⟩
    · simp [ht]
    · simp [ht]
    · intro x hx; dsimp only; rw [if_neg (by omega), if_neg (by omega), if_pos hx]
  · simp at h

/-- the input as E sees it: length word and bytes as words -/
def inpW (inp : List UInt8) : Nat → UInt64 := fun k => (inp.getD k 0).toUInt64

/-- RD agrees with `Sem`'s `rd` (index past the end ⇒ 0) -/
theorem rd_agree (inp : List UInt8) (hl : inp.length < 2 ^ 64) (i : UInt64) (sp : Nat) (H : Hp) :
    rdF1 (UInt64.ofNat inp.length) (inpW inp) i sp H = some ((inp.getD i.toNat 0).toUInt64, H) := by
  simp only [rdF1, toNat_ofNat_lt hl, inpW]
  split
  · rfl
  · rename_i h; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : inp.length ≤ i.toNat)]

end NanoMain
