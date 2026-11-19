/- Machine bridge (Opus box E), exactness part: the remaining Gen emitters are `template.map encG`.
`g26_exact` (LET / CONTINUE pop of w words = `popN`), `g32_bpush` (PUT / BPUSH = `bpushT 6`), `g32_bset` (`bsetT`),
`g32_bnew` (`bnewT 1 q κ` with κ = u).  Together with ExprExact / CallExact every word of a CG code block is an encG word
of a J template (exit placeholders and patched jumps aside). -/
import Nano.V2Self.Proof.ExprExact
import Nano.V2Self.Proof.CallExact
import Nano.V2Self.Proof.Heap
namespace Templates
open CallProbe C

theorem g26_exact (p : Nat) (hp : p < 251) : ∀ (n w s : Nat) (o : Buf), w ≤ n → s + w < 251 →
    g26 n p.toUInt64 s.toUInt64 w.toUInt64 o = o ++ (popN p s w).map encG
  | 0, w, s, o, hw, _ => by
      have : w = 0 := by omega
      subst this; simp [g26, popN]
  | n + 1, w, s, o, hw, hs => by
    rcases w with _ | w
    · simp [g26, popN]
    · have hne : ¬ ((w + 1).toUInt64 == 0) = true := by
        simp [Nat.toUInt64, UInt64.ofNat_add]
        intro h; have := congrArg UInt64.toNat h; simp at this; omega
      have e1 : (w + 1).toUInt64 - 1 = w.toUInt64 := by simp
      have e2 : s.toUInt64 + (w + 1).toUInt64 - 1 = (s + w).toUInt64 := by
        rw [toU_add, toU_add]; simp [← UInt64.add_assoc]
      have g := g24_off p (s + w) hp (by omega)
      have hoff : offOf p (s + w) = slotOff p (s + w) := by
        unfold offOf slotOff; split <;> rfl
      simp only [g26, hne, if_false, Bool.false_eq_true]
      rw [e1, e2, g, g26_exact p hp n w s _ (by omega) (by omega)]
      simp [popN, popSlot, encG, bpush, hoff, iu, g10, g11, g12]

section prims
local macro "gsimp" : tactic => `(tactic| simp [encG, bpush, iu, g10, g11, g12, g1, g2, g3, g4, aluF, g_0, g_3, g_16, g_19, g_31, g_35, g_51, g_63, g_99, g_103, g_127, g_4095, g_15, g_1])

theorem g32_bset (o : Buf) (u : UInt64) : g32 o 8 u = o ++ bsetT.map encG := by
  unfold g32; simp [bsetT]; gsimp

/-- C's capacity jump `g13 0 h 6` from word h is the template's `jal x0 (6 − h)` -/
theorem jal6 (q : Nat) (hq : q < 2 ^ 32) :
    g13 0 (UInt64.ofNat q) 6 = encG (.jal 0 (((6 : Nat) : Int) - (q : Int))) := by
  unfold g13; simp only [encG]; congr 1
  apply UInt64.toNat.inj
  rw [iu_toNat]
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_sub, Nat.shiftLeft_eq]
  omega

theorem g32_bpush_any (o : Buf) (p u : UInt64) (h1 : p ≠ 1) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) (h6 : p ≠ 6)
    (h7 : p ≠ 7) (h8 : p ≠ 8) (ho : o.length + 6 < 2 ^ 32) :
    g32 o p u = o ++ (bpushT 6 o.length).map encG := by
  have hh : ∀ l : Buf, bsize l = l.length.toUInt64 := fun _ => rfl
  have j := jal6 (o.length + 6) (by omega)
  unfold g32 g30
  simp [h1, h2, h3, h5, h6, h7, h8, hh, bpush]
  rw [show UInt64.ofNat o.length + 6 = UInt64.ofNat (o.length + 6) from by simp [UInt64.ofNat_add], j]
  simp [bpushT]; gsimp

theorem g32_bpush (o : Buf) (u : UInt64) (ho : o.length + 6 < 2 ^ 32) : g32 o 9 u = o ++ (bpushT 6 o.length).map encG :=
  g32_bpush_any o 9 u (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ho

/-- PUT (p = 4) is BPUSH's code (no `p == 4` branch in g32) -/
theorem g32_put (o : Buf) (u : UInt64) (ho : o.length + 6 < 2 ^ 32) : g32 o 4 u = o ++ (bpushT 6 o.length).map encG :=
  g32_bpush_any o 4 u (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ho

theorem liT_le (d : Nat) (v : UInt64) : (liT d v).length ≤ 17 := by
  by_cases hv : v.toNat < 2048
  · rw [liT_len_small _ _ hv]; omega
  · rw [liT_len_big _ _ hv]; omega

theorem jal1 (q : Nat) (hq : q < 2 ^ 32) :
    g13 0 (UInt64.ofNat q + 2) 1 = encG (.jal 0 (((1 : Nat) : Int) - ((q : Int) + 2))) := by
  unfold g13; show g5 0 _ = g5 0 _; rw [jal_off q hq]

/-- BNEW (p = 5) with κ = u is `bnewT 1 q κ` (OOM stub = word 1) -/
theorem g32_bnew (o : Buf) (κ : Nat) (ho : o.length + 50 < 2 ^ 32) :
    g32 o 5 (UInt64.ofNat κ) = o ++ (bnewT 1 o.length κ).map encG := by
  have hh : ∀ l : Buf, bsize l = l.length.toUInt64 := fun _ => rfl
  have eW : (UInt64.ofNat κ + 2) <<< 3 = UInt64.ofNat ((κ + 2) * 8) := by
    apply UInt64.toNat.inj
    simp [UInt64.toNat_shiftLeft, UInt64.toNat_add, Nat.shiftLeft_eq]
  have e5 : (6 : UInt64) = (6 : Nat).toUInt64 := rfl
  have e7 : (7 : UInt64) = (7 : Nat).toUInt64 := rfl
  have l1 := liT_le 6 (UInt64.ofNat ((κ + 2) * 8))
  have l2 := liT_le 7 (UInt64.ofNat κ)
  have l3 := liT_le 6 ((UInt64.ofNat κ + 2) * 8)
  unfold g32
  simp only [show ((5 : UInt64) == 1) = false from rfl, show ((5 : UInt64) == 3) = false from rfl,
    show ((5 : UInt64) == 2) = false from rfl, show ((5 : UInt64) == 5) = true from rfl, if_true, if_false,
    Bool.false_eq_true]
  rw [eW, e5, g23_exact _ 6 _ (by decide)]
  simp only [hh, bpush, List.length_append, List.length_map, List.length_cons, List.length_nil]
  rw [show (o.length + (0 + 1) + (liT 6 (UInt64.ofNat ((κ + 2) * 8))).length).toUInt64 + 2 =
      UInt64.ofNat (o.length + 1 + (liT 6 (UInt64.ofNat ((κ + 2) * 8))).length) + 2 from by simp [Nat.toUInt64],
    jal1 _ (by omega), e7, g23_exact _ 7 _ (by decide), g21_eq,
    show (5 : UInt64) = (5 : Nat).toUInt64 from rfl, g22_exact _ 5 (by decide) (by simp; omega)]
  simp [bnewT, encG, iu, g10, g12, g1, g4, aluF, List.append_assoc]
  congr 2; omega
end prims
