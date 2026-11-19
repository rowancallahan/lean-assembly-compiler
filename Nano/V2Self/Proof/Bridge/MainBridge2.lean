/- Nano/V2Self/Proof/Bridge/MainBridge2: the Sem ⇐ sv bridge, layer 2 — a ghost ABSTRACT HEAP σ (block address ↦ the
buffer's list) represented in E's heap image, the value relation, and how BNEW / BPUSH / BSET change σ. -/
import Nano.V2Self.Proof.Bridge.MainBridge

namespace NanoMain
open Templates

abbrev AH := Nat → Option (List UInt64)

/-- σ's blocks are buffers in `H`, pairwise disjoint -/
def AHeap (hb κ : Nat) (H : Hp) (σ : AH) : Prop :=
  (∀ a l, σ a = some l → a < 2 ^ 64 ∧ BufAt hb κ H (UInt64.ofNat a) l) ∧
  (∀ a b, a ≠ b → (σ a).isSome → (σ b).isSome → a + 16 + 8 * κ ≤ b ∨ b + 16 + 8 * κ ≤ a)

/-- a `Sem` value word and E's machine word -/
def VR (σ : AH) : W → UInt64 → Prop
  | .w x, u => u = x
  | .b l, u => σ u.toNat = some l

def VRs (σ : AH) (v : List W) (u : List UInt64) : Prop :=
  v.length = u.length ∧ ∀ i (h1 : i < v.length) (h2 : i < u.length), VR σ v[i] u[i]

def upd (σ : AH) (a : Nat) (l : List UInt64) : AH := fun x => if x = a then some l else σ x

theorem bufAt_frame {hb κ : Nat} {H H' : Hp} {a : UInt64} {l : List UInt64} (h : BufAt hb κ H a l)
    (ht : H.top ≤ H'.top) (hm : ∀ x, InBuf κ a x → H'.m x = H.m x) : BufAt hb κ H' a l := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, Nat.le_trans h3 ht, h4, h5, h6, ?_, ?_, fun i hi => ?_⟩
  · rw [hm _ ⟨Nat.le_refl _, by omega⟩]; exact h7
  · rw [hm _ ⟨by omega, by omega⟩]; exact h8
  · have : i < κ := by omega
    rw [hm _ ⟨by omega, by omega⟩]; exact h9 i hi

/-- BPUSH / BSET on a σ-block: σ updated at that block only -/
theorem aheap_update {hb κ : Nat} {H H' : Hp} {σ : AH} {a : Nat} {l l' : List UInt64} (hA : AHeap hb κ H σ)
    (ha : σ a = some l) (hB : BufAt hb κ H' (UInt64.ofNat a) l') (ht : H'.top = H.top)
    (hm : ∀ x, ¬ InBuf κ (UInt64.ofNat a) x → H'.m x = H.m x) : AHeap hb κ H' (upd σ a l') := by
  obtain ⟨hA1, hA2⟩ := hA
  have hal := (hA1 a l ha).1
  have hta : (UInt64.ofNat a).toNat = a := toNat_ofNat_lt hal
  refine ⟨fun b lb hb' => ?_, fun b c hbc hb1 hc1 => ?_⟩
  · unfold upd at hb'
    split at hb'
    · subst_vars; cases hb'; exact ⟨hal, hB⟩
    · rename_i hne
      obtain ⟨hbl, hbB⟩ := hA1 b lb hb'
      refine ⟨hbl, bufAt_frame hbB (by omega) fun x hx => hm x ?_⟩
      have hd := hA2 b a hne (by simp [hb']) (by simp [ha])
      have htb : (UInt64.ofNat b).toNat = b := toNat_ofNat_lt hbl
      simp only [InBuf, hta, htb] at hx ⊢; omega
  · have e1 : (σ b).isSome ∨ b = a := by unfold upd at hb1; split at hb1 <;> simp_all
    have e2 : (σ c).isSome ∨ c = a := by unfold upd at hc1; split at hc1 <;> simp_all
    have ha' : (σ a).isSome := by simp [ha]
    rcases e1 with e1 | rfl <;> rcases e2 with e2 | rfl
    · exact hA2 b c hbc e1 e2
    · exact hA2 b c hbc e1 ha'
    · exact hA2 b c hbc ha' e2
    · exact absurd rfl hbc

/-- BNEW: a fresh block beyond every σ-block -/
theorem aheap_new {hb κ : Nat} {H H' : Hp} {σ : AH} {a : UInt64} (hA : AHeap hb κ H σ) (hB : BufAt hb κ H' a [])
    (htop : H.top + 16 + 8 * κ = H'.top) (hat : a.toNat = H.top) (hm : ∀ x, x < H.top → H'.m x = H.m x) :
    AHeap hb κ H' (upd σ a.toNat []) ∧ σ a.toNat = none := by
  obtain ⟨hA1, hA2⟩ := hA
  have hfresh : σ a.toNat = none := by
    cases e : σ a.toNat with
    | none => rfl
    | some l =>
      obtain ⟨-, hb⟩ := hA1 _ l e; have := hb.2.2.1; rw [toNat_ofNat_lt a.toNat_lt] at this; omega
  refine ⟨⟨fun b lb hb' => ?_, fun b c hbc hb1 hc1 => ?_⟩, hfresh⟩
  · unfold upd at hb'
    split at hb'
    · rename_i e; subst e; cases hb'; refine ⟨a.toNat_lt, ?_⟩; rw [show UInt64.ofNat a.toNat = a by simp]; exact hB
    · obtain ⟨hbl, hbB⟩ := hA1 b lb hb'
      refine ⟨hbl, bufAt_frame hbB (by omega) fun x hx => hm x ?_⟩
      have := hbB.2.2.1; simp only [InBuf] at hx; omega
  · have bnd : ∀ d, (σ d).isSome → d + 16 + 8 * κ ≤ H.top := by
      intro d hd
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hd
      obtain ⟨hdl, hdB⟩ := hA1 d l hl; have := hdB.2.2.1; rw [toNat_ofNat_lt hdl] at this; exact this
    have e1 : (σ b).isSome ∨ b = a.toNat := by unfold upd at hb1; split at hb1 <;> simp_all
    have e2 : (σ c).isSome ∨ c = a.toNat := by unfold upd at hc1; split at hc1 <;> simp_all
    rcases e1 with e1 | rfl <;> rcases e2 with e2 | rfl
    · exact hA2 b c hbc e1 e2
    · have := bnd b e1; omega
    · have := bnd c e2; omega
    · exact absurd rfl hbc

end NanoMain
