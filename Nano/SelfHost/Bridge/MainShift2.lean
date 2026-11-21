/- Nano/SelfHost/Bridge/MainShift2: shift invariance, layer 2 — the prim closings.  Handles are shifted by `δ`
(8-aligned, at most 2^32), heap cells are shifted, data words agree. -/
import Nano.SelfHost.Bridge.MainShift1

namespace NanoMain
open Templates

/-- related optional results -/
def OptR {α : Type} (R : α → α → Prop) (δ hb : Nat) (H : Hp) (o o' : Option (α × Hp)) : Prop :=
  (o = none ∧ o' = none) ∨ ∃ a a' H1 H1', o = some (a, H1) ∧ o' = some (a', H1') ∧ R a a' ∧ HR δ hb H1 H1' ∧
    Bnd hb H1 ∧ H.top ≤ H1.top

theorem ofO_out {α : Type} {R : α → α → Prop} {δ hb : Nat} {H : Hp} {o o' : Option (α × Hp)} (f : Fail)
    (h : OptR R δ hb H o o') : OutR R δ hb H (ofO f o) (ofO f o') := by
  rcases h with ⟨rfl, rfl⟩ | ⟨a, a', H1, H1', rfl, rfl, h1, h2, h3, h4⟩
  · exact rfl
  · exact ⟨h1, h2, h3, h4⟩

section
variable {δ hb : Nat}

theorem hread_sh {H H' : Hp} (hH : HR δ hb H H') (a : Nat) : hread (hb + δ) H' (a + δ) = hread hb H a := by
  unfold hread
  by_cases h : hb ≤ a ∧ a < H.top
  · rw [if_pos h, if_pos ⟨by omega, by rw [hH.1]; omega⟩, hH.2 a h.1]
  · rw [if_neg h, if_neg (fun h' => h ⟨by omega, by rw [hH.1] at h'; omega⟩)]

theorem bsize_sh : Sim1 δ hb .b .w (fun a sp H => ofO .stuck (bsizeF hb a sp H))
    (fun a sp H => ofO .stuck (bsizeF (hb + δ) a sp H)) := by
  intro a a' sp sp' H H' ha hH hB hS
  refine ofO_out _ ?_
  simp only [bsizeF]
  simp only [WR] at ha
  rw [ha, hread_sh hH]
  cases hread hb H a.toNat with
  | none => exact .inl ⟨rfl, rfl⟩
  | some l => exact .inr ⟨l, l, H, H', rfl, rfl, rfl, hH, hB, Nat.le_refl _⟩

theorem rd_sh (c29 : UInt64) (inp : Nat → UInt64) : Sim1 δ hb .w .w (fun a sp H => ofO .stuck (rdF1 c29 inp a sp H))
    (fun a sp H => ofO .stuck (rdF1 c29 inp a sp H)) := by
  intro a a' sp sp' H H' ha hH hB hS
  simp only [WR] at ha; subst ha
  exact ⟨rfl, hH, hB, Nat.le_refl _⟩

theorem alu_sh (op : Nat) : Sim2 δ hb .w .w .w (fun a b sp H => ofO .stuck (Templates.aluF2 op a b sp H))
    (fun a b sp H => ofO .stuck (Templates.aluF2 op a b sp H)) := by
  intro a a' b b' sp sp' H H' ha hb' hH hB hS
  simp only [WR] at ha hb'; subst ha hb'
  exact ⟨rfl, hH, hB, Nat.le_refl _⟩

theorem bget_sh (hδ : δ ≤ 2 ^ 32) : Sim2 δ hb .b .w .w (fun a b sp H => ofO .stuck (bgetF hb a b sp H))
    (fun a b sp H => ofO .stuck (bgetF (hb + δ) a b sp H)) := by
  intro a a' i i' sp sp' H H' ha hi hH hB hS
  refine ofO_out _ ?_
  simp only [WR] at ha hi; subst i'
  simp only [bgetF]
  rw [ha, hread_sh hH]
  cases hl : hread hb H a.toNat with
  | none => exact .inl ⟨rfl, rfl⟩
  | some l =>
    simp only [Option.bind_some]
    split
    · have e : a.toNat + δ + 16 + 8 * i.toNat = a.toNat + 16 + 8 * i.toNat + δ := by omega
      rw [e, hread_sh hH]
      by_cases h1 : a.toNat + 16 + 8 * i.toNat < 2 ^ 62
      · by_cases h2 : a.toNat + 16 + 8 * i.toNat + δ < 2 ^ 62
        · rw [if_pos h1, if_pos h2]
          cases hread hb H (a.toNat + 16 + 8 * i.toNat) with
          | none => exact .inl ⟨rfl, rfl⟩
          | some w => exact .inr ⟨w, w, H, H', rfl, rfl, rfl, hH, hB, Nat.le_refl _⟩
        · rw [if_pos h1, if_neg h2]
          have : hread hb H (a.toNat + 16 + 8 * i.toNat) = none := by
            unfold hread; rw [if_neg (by unfold Bnd at hB; omega)]
          rw [this]; exact .inl ⟨rfl, rfl⟩
      · rw [if_neg h1, if_neg (by omega)]; exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨0, 0, H, H', rfl, rfl, rfl, hH, hB, Nat.le_refl _⟩

theorem bufInfo_sh (hδ8 : δ % 8 = 0) {H H' : Hp} (hH : HR δ hb H H') {a a' : UInt64} (ha : a'.toNat = a.toNat + δ) :
    bufInfo (hb + δ) H' a' = bufInfo hb H a := by
  unfold bufInfo
  rw [ha]
  by_cases h : hb ≤ a.toNat ∧ a.toNat % 8 = 0
  · rw [if_pos h, if_pos ⟨by omega, by omega⟩, hread_sh hH, show a.toNat + δ + 8 = a.toNat + 8 + δ by omega,
      hread_sh hH, hH.1]
    congr 1; funext l; congr 1; funext c
    by_cases h2 : l.toNat ≤ c.toNat ∧ a.toNat + 16 + 8 * c.toNat ≤ H.top
    · rw [if_pos h2, if_pos ⟨h2.1, by omega⟩]
    · rw [if_neg h2, if_neg (fun h' => h2 ⟨h'.1, by omega⟩)]
  · rw [if_neg h, if_neg (fun h' => h ⟨by omega, by omega⟩)]

theorem bufInfo_top {H : Hp} {a l c : UInt64} (h : bufInfo hb H a = some (l, c)) :
    hb ≤ a.toNat ∧ l.toNat ≤ c.toNat ∧ a.toNat + 16 + 8 * c.toNat ≤ H.top := by
  obtain ⟨h1, -, -, h4, h5⟩ := bufInfo_spec h; exact ⟨h1, h4, h5⟩

theorem bpush_sh (hδ8 : δ % 8 = 0) (hδ : δ ≤ 2 ^ 32) : Sim2 δ hb .b .w .b (bpushFF hb) (bpushFF (hb + δ)) := by
  intro a a' v v' sp sp' H H' ha hv hH hB hS
  simp only [WR] at ha hv; subst hv
  unfold bpushFF
  rw [bufInfo_sh hδ8 hH ha]
  cases hbi : bufInfo hb H a with
  | none => exact rfl
  | some lc =>
    obtain ⟨l, c⟩ := lc
    obtain ⟨b1, b2, b3⟩ := bufInfo_top hbi
    simp only
    split
    · rename_i hlt
      refine ofO_out _ ?_
      simp only [bpushF, hbi, Option.bind_some]
      rw [bufInfo_sh hδ8 hH ha, hbi]; simp only [Option.bind_some]
      have hB0 := hB; unfold Bnd at hB0
      rw [if_pos ⟨hlt, by omega⟩, if_pos ⟨hlt, by rw [ha]; omega⟩]
      refine .inr ⟨_, _, _, _, rfl, rfl, ha, ⟨hH.1, fun x hx => ?_⟩, hB, Nat.le_refl _⟩
      simp only [ha]
      by_cases e1 : x = a.toNat
      · rw [if_pos (by omega), if_pos e1]
      · rw [if_neg (by omega), if_neg e1]
        by_cases e2 : x = a.toNat + 16 + 8 * l.toNat
        · rw [if_pos (by omega), if_pos e2]
        · rw [if_neg (by omega), if_neg e2, hH.2 x hx]
    · exact rfl

theorem bset_sh (hδ8 : δ % 8 = 0) (hδ : δ ≤ 2 ^ 32) : Sim3 δ hb .b .w .w .b (fun a b c sp H => ofO .stuck (bsetF hb a b c sp H))
    (fun a b c sp H => ofO .stuck (bsetF (hb + δ) a b c sp H)) := by
  intro a a' i i' v v' sp sp' H H' ha hi hv hH hB hS
  simp only [WR] at ha hi hv; subst i' v'
  refine ofO_out _ ?_
  simp only [bsetF]
  rw [bufInfo_sh hδ8 hH ha]
  cases hbi : bufInfo hb H a with
  | none => exact .inl ⟨rfl, rfl⟩
  | some lc =>
    obtain ⟨l, c⟩ := lc
    obtain ⟨b1, b2, b3⟩ := bufInfo_top hbi
    have hB0 := hB; unfold Bnd at hB0
    simp only [Option.bind_some]
    split
    · rename_i hlt
      rw [if_pos (by omega), if_pos (by rw [ha]; omega)]
      refine .inr ⟨_, _, _, _, rfl, rfl, ha, ⟨hH.1, fun x hx => ?_⟩, hB, Nat.le_refl _⟩
      simp only [ha]
      by_cases e2 : x = a.toNat + 16 + 8 * i.toNat
      · rw [if_pos (by omega), if_pos e2]
      · rw [if_neg (by omega), if_neg e2, hH.2 x hx]
    · exact .inr ⟨a, a', H, H', rfl, rfl, ha, hH, hB, Nat.le_refl _⟩

theorem bnew_sh (κ : Nat) (hδ : δ ≤ 2 ^ 32) {RE : Env → Env → Prop} :
    Sim δ hb RE (WR δ .b) (bnewF κ) (bnewF κ) := by
  intro env env' sp sp' H H' he hH hB hS
  refine ofO_out _ ?_
  simp only [bnewS]
  have hB0 := hB; unfold Bnd at hB0
  have hr := room_iff (c := 8 * (κ + 2) + 8) hH.1 hS
  by_cases h : H.top + 8 * (κ + 2) + 8 ≤ sp ∧ sp < 2 ^ 62 ∧ κ < 2 ^ 40
  · have hlive : sp' = sp + δ ∧ sp ≤ 2 ^ 32 := by
      rcases hS with h' | ⟨h1, -⟩
      · exact h'
      · omega
    rw [if_pos h, if_pos ⟨by have := hr.1 (by omega); omega, by omega, h.2.2⟩]
    have w1 : WR δ .b (UInt64.ofNat H.top) (UInt64.ofNat H'.top) := by
      simp only [WR, hH.1]
      have e1 : (UInt64.ofNat (H.top + δ)).toNat = H.top + δ := by simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show H.top + δ < 2 ^ 64 by omega)]
      have e2 : (UInt64.ofNat H.top).toNat = H.top := by simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show H.top < 2 ^ 64 by omega)]
      rw [e1, e2]
    refine .inr ⟨_, _, _, _, rfl, rfl, w1, ⟨by show H'.top + 8 * (κ + 2) = H.top + 8 * (κ + 2) + δ; rw [hH.1]; omega,
      fun x hx => ?_⟩, ⟨hB0.1, by show hb ≤ H.top + 8 * (κ + 2); omega, by show H.top + 8 * (κ + 2) ≤ 2 ^ 32; omega⟩,
      by show H.top ≤ H.top + 8 * (κ + 2); omega⟩
    show (if x + δ = H'.top then some 0 else if x + δ = H'.top + 8 then some (UInt64.ofNat κ)
      else if x + δ < H'.top then H'.m (x + δ) else none) =
      (if x = H.top then some 0 else if x = H.top + 8 then some (UInt64.ofNat κ) else if x < H.top then H.m x else none)
    simp only [hH.1]
    by_cases e1 : x = H.top
    · rw [if_pos (by omega), if_pos e1]
    · rw [if_neg (by omega), if_neg e1]
      by_cases e2 : x = H.top + 8
      · rw [if_pos (by omega), if_pos e2]
      · rw [if_neg (by omega), if_neg e2]
        by_cases e3 : x < H.top
        · rw [if_pos (by omega), if_pos e3, hH.2 x hx]
        · rw [if_neg (by omega), if_neg e3]
  · rw [if_neg h, if_neg (fun h' => h ⟨by have := hr.2 (by omega); omega, by
      rcases hS with h'' | ⟨h1, h2⟩
      · omega
      · omega, h'.2.2⟩)]
    exact .inl ⟨rfl, rfl⟩

end

end NanoMain
