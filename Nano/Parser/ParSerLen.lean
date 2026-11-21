/- Nano/Parser/ParSerLen: the serialization of a parsed program is linear in its tokens (box D, item hXl):
`ser_len : ParsesProgram ts p → (serialize p).length ≤ 4 * ts.length + 1`.  Every expression node costs at most 3 words
per consumed token; a def header + terminator costs 8 words for at least 2 tokens.  Widths and slot numbers are NOT
bounded by the parser (nested pair lets double widths); only the word count is. -/
import Nano.Parser.ParSpec
namespace ParSerLen
open ParSpec

abbrev L (e : Nd) : Nat := e.ser.length

theorem serL_len_cons (n : Nd) (r : List Nd) : (serL (n :: r)).length = L n + (serL r).length := by
  simp [serL]

theorem serL_dropInp : ∀ (ps : List Ps) (xs : List Nd), (serL (dropInp ps xs)).length ≤ (serL xs).length
  | [], xs => by simp [dropInp, serL]
  | _ :: _, [] => by simp [dropInp, serL]
  | p :: ps, x :: xs => by
    have ih := serL_dropInp ps xs
    simp only [dropInp, List.zip_cons_cons, List.filterMap_cons] at ih ⊢
    cases p <;> simp only [serL, List.length_append] <;> omega

theorem L_mkPairFlat : ∀ cs : List Nd, L (mkPairFlat cs) ≤ 2 + (serL cs).length
  | [] => by simp [L, mkPairFlat, Nd.ser, serL]
  | [c] => by simp [mkPairFlat, serL]
  | c :: d :: r => by simp only [L, mkPairFlat, Nd.ser, List.length_cons]; omega

def QE (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pExpr f cx tl ts nx = some (e, ty, r, nx') → L e + 3 * r.length ≤ 3 * ts.length
def QB (f : Nat) : Prop := ∀ cx tl minp ts nx e ty r nx', pBin f cx tl minp ts nx = some (e, ty, r, nx') →
  L e + 3 * r.length ≤ 3 * ts.length
def QL (f : Nat) : Prop := ∀ cx minp a ta ts nx e ty r nx', pLoop f cx minp a ta ts nx = some (e, ty, r, nx') →
  L e + 3 * r.length ≤ L a + 3 * ts.length
def QA (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pApp f cx tl ts nx = some (e, ty, r, nx') → L e + 3 * r.length ≤ 3 * ts.length
def QC (f : Nat) : Prop := ∀ cx n ts nx e ty r nx', pCallDef f cx n ts nx = some (e, ty, r, nx') →
  L e + 3 * r.length ≤ 3 + 3 * ts.length
def QG (f : Nat) : Prop := ∀ cx ps ts nx as r nx', pArgs f cx ps ts nx = some (as, r, nx') →
  (serL (as.map (·.1))).length + 3 * r.length ≤ 3 * ts.length
def QT (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pAtom f cx tl ts nx = some (e, ty, r, nx') → L e + 3 * r.length ≤ 3 * ts.length
def QU (f : Nat) : Prop := ∀ cx ts nx e sh r nx', pTup f cx ts nx = some (e, sh, r, nx') → L e + 3 * r.length ≤ 3 * ts.length

theorem qE_step (f : Nat) (hB : ∀ g ≤ f, QB g) (hE : ∀ g ≤ f, QE g) : QE (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pExpr at h
  split at h
  · cases h
  · obtain ⟨⟨v, tv, r1, nx1⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    have nv := hE _ (by omega) _ _ _ _ _ _ _ _ hv
    simp only at h
    split at h
    · obtain ⟨⟨b, tb, r3, nx3⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, rfl, -⟩ := he
      have nb := hE _ (by omega) _ _ _ _ _ _ _ _ hb
      simp only [L, Nd.ser, List.length_cons, List.length_append, List.length_cons] at nv nb ⊢; omega
    · cases h
  · obtain ⟨⟨v, tv, r1, nx1⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    have nv := hE _ (by omega) _ _ _ _ _ _ _ _ hv
    simp only at h
    split at h
    · obtain ⟨⟨b, tb, r3, nx3⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, rfl, -⟩ := he
      have nb := hE _ (by omega) _ _ _ _ _ _ _ _ hb
      simp only [L, Nd.ser, List.length_cons, List.length_append] at nv nb ⊢; omega
    · cases h
  · obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    have na := hB _ (by omega) _ _ _ _ _ _ _ _ _ ha
    simp only at h
    split at h
    · split at h
      · obtain ⟨⟨b, tb, r3, nx2⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
        have nb := hB _ (by omega) _ _ _ _ _ _ _ _ _ hb
        simp only at h
        split at h
        · obtain ⟨⟨t, tt, r5, nx3⟩, ht, h⟩ := Option.bind_eq_some_iff.1 h
          have nt := hE _ (by omega) _ _ _ _ _ _ _ _ ht
          simp only at h
          split at h
          · obtain ⟨⟨el, te, r7, nx4⟩, hel, h⟩ := Option.bind_eq_some_iff.1 h
            have ne := hE _ (by omega) _ _ _ _ _ _ _ _ hel
            obtain ⟨ty', _, he⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, rfl, -⟩ := he
            simp only [L, Nd.ser, List.length_cons, List.length_append] at na nb nt ne ⊢; omega
          · cases h
        · cases h
      · cases h
    · cases h
  · exact hB _ (by omega) _ _ _ _ _ _ _ _ _ h

theorem qB_step (f : Nat) (hA : ∀ g ≤ f, QA g) (hL : ∀ g ≤ f, QL g) : QB (f + 1) := by
  intro cx tl minp ts nx e ty r nx' h
  unfold pBin at h
  obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
  have na := hA _ (by omega) _ _ _ _ _ _ _ _ ha
  simp only at h
  split at h
  · split at h
    · obtain ⟨⟨a', ta', r', nx''⟩, ha', h⟩ := Option.bind_eq_some_iff.1 h
      have := hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h
      have := hA _ (by omega) _ _ _ _ _ _ _ _ ha'; simp only at *; omega
    · have := hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h; omega
  · have := hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h; omega

theorem qL_step (f : Nat) (hB : ∀ g ≤ f, QB g) (hL : ∀ g ≤ f, QL g) : QL (f + 1) := by
  intro cx minp a ta ts nx e ty r nx' h
  unfold pLoop at h
  split at h
  · split at h
    · split at h
      · cases h; omega
      · split at h
        · split at h
          · split at h
            · have := hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h
              simp only [L, Nd.ser, List.length_cons, List.length_append, List.length_nil] at this ⊢; omega
            · cases h
          · obtain ⟨⟨b, tb, r', nx''⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
            have nb := hB _ (by omega) _ _ _ _ _ _ _ _ _ hb
            simp only at h
            split at h
            · have := hL _ (by omega) _ _ _ _ _ _ _ _ _ _ h
              simp only [L, Nd.ser, List.length_cons, List.length_append] at this nb ⊢; omega
            · cases h
        · cases h
    · cases h; omega
  · cases h; omega

theorem qC_step (f : Nat) (hG : ∀ g ≤ f, QG g) : QC (f + 1) := by
  intro cx n ts nx e ty r nx' h
  unfold pCallDef at h
  split at h
  · rename_i id d _
    obtain ⟨⟨as, r1, nx1⟩, hg, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, rfl, -⟩ := he
    have := hG _ (by omega) _ _ _ _ _ _ _ hg
    have := serL_dropInp d.params (as.map (·.1))
    simp only [L, Nd.ser, List.length_cons]; omega
  · cases h

theorem qG_step (f : Nat) (hT : ∀ g ≤ f, QT g) (hG : ∀ g ≤ f, QG g) : QG (f + 1) := by
  intro cx ps ts nx as r nx' h
  unfold pArgs at h
  split at h
  · cases h
  · cases h; simp [serL]
  · obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    have na := hT _ (by omega) _ _ _ _ _ _ _ _ ha
    simp only at h
    split at h
    · obtain ⟨⟨as', r2, nx2⟩, hg, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, -⟩ := he
      have ng := hG _ (by omega) _ _ _ _ _ _ _ hg
      simp only [List.map_cons, serL_len_cons] at ng ⊢; omega
    · cases h

theorem qA_step (f : Nat) (hT : ∀ g ≤ f, QT g) (hG : ∀ g ≤ f, QG g) (hC : ∀ g ≤ f, QC g) : QA (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pApp at h
  split at h
  · cases h
  · split at h
    · rename_i pid ps rs hps
      obtain ⟨⟨as, r1, nx1⟩, hg, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, rfl, -⟩ := he
      have := hG _ (by omega) _ _ _ _ _ _ _ hg
      have := serL_dropInp ps (as.map (·.1))
      simp only [L, Nd.ser, List.length_cons] at *; omega
    · have := hT _ (by omega) _ _ _ _ _ _ _ _ h; simp only [List.length_cons] at *; omega
  · repeat' (first | (cases h; done) | split at h)
    all_goals first
      | (have := hT _ (by omega) _ _ _ _ _ _ _ _ h; simp only [List.length_cons] at *; omega)
      | (have := hC _ (by omega) _ _ _ _ _ _ _ _ h; simp only [List.length_cons] at *; omega)
      | (obtain ⟨⟨as, r2, nx2⟩, hg, h⟩ := Option.bind_eq_some_iff.1 h
         have ng := hG _ (by omega) _ _ _ _ _ _ _ hg
         simp only at h
         split at h
         · cases h
         · cases h
           have key : ∀ ps, L (.cont (mkPairFlat (dropInp ps (as.map (·.1))))) ≤ 3 + (serL (as.map (·.1))).length :=
             fun ps => by
               have := L_mkPairFlat (dropInp ps (as.map (·.1))); have := serL_dropInp ps (as.map (·.1))
               simp only [L, Nd.ser, List.length_cons] at *; omega
           refine Nat.le_trans (Nat.add_le_add_right (key _) _) ?_
           simp only [List.length_cons] at *; omega)
  · have := hT _ (by omega) _ _ _ _ _ _ _ _ h; omega

theorem qU_step (f : Nat) (hE : ∀ g ≤ f, QE g) (hU : ∀ g ≤ f, QU g) : QU (f + 1) := by
  intro cx ts nx e sh r nx' h
  unfold pTup at h
  split at h
  · cases h
  · obtain ⟨⟨e1, t, r1, nx1⟩, he1, h⟩ := Option.bind_eq_some_iff.1 h
    have n1 := hE _ (by omega) _ _ _ _ _ _ _ _ he1
    simp only at h
    split at h
    · cases h; simp only [List.length_cons] at *; omega
    · obtain ⟨⟨rest, sr, r3, nx3⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, rfl, -⟩ := he
      have n2 := hU _ (by omega) _ _ _ _ _ _ _ hr
      simp only [L, Nd.ser, serL, List.length_cons, List.length_append, List.length_nil] at *; omega
    · cases h
  · cases h

theorem qT_step (f : Nat) (hE : ∀ g ≤ f, QE g) (hU : ∀ g ≤ f, QU g) : QT (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pAtom at h
  split at h
  · cases h
  · cases h; simp only [L, Nd.ser, serL, List.length_cons, List.length_nil]; omega
  · cases h; simp only [L, Nd.ser, serL, List.length_cons, List.length_nil]; omega
  · cases h; simp only [L, Nd.ser, serL, List.length_cons, List.length_nil]; omega
  · split at h
    · cases h; simp only [L, Nd.ser, serL, List.length_cons, List.length_nil]; omega
    · cases h; simp only [L, Nd.ser, serL, List.length_cons, List.length_nil]; omega
    · cases h
    · split at h
      · split at h
        · cases h; simp only [L, Nd.ser, serL, List.length_cons, List.length_nil]; omega
        · cases h
      · cases h
  · obtain ⟨⟨e1, t, r1, nx1⟩, he1, h⟩ := Option.bind_eq_some_iff.1 h
    have n1 := hE _ (by omega) _ _ _ _ _ _ _ _ he1
    simp only at h
    split at h
    · cases h; simp only [List.length_cons] at *; omega
    · obtain ⟨⟨e2, t2, r2, nx2⟩, he2, h⟩ := Option.bind_eq_some_iff.1 h
      have n2 := hE _ (by omega) _ _ _ _ _ _ _ _ he2
      simp only at h
      split at h
      · obtain ⟨⟨tl', st, r3, nx3⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -, rfl, -⟩ := he
        have n3 := hU _ (by omega) _ _ _ _ _ _ _ hr
        simp only [L, Nd.ser, serL, List.length_cons, List.length_append, List.length_nil] at *; omega
      · cases h
    · cases h
  · cases h

theorem q_all : ∀ f, ∀ g ≤ f, QE g ∧ QB g ∧ QL g ∧ QA g ∧ QC g ∧ QG g ∧ QT g ∧ QU g := by
  have base : QE 0 ∧ QB 0 ∧ QL 0 ∧ QA 0 ∧ QC 0 ∧ QG 0 ∧ QT 0 ∧ QU 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ _ _ _ h; simp [pExpr] at h
    · intro _ _ _ _ _ _ _ _ _ h; simp [pBin] at h
    · intro _ _ _ _ _ _ _ _ _ _ h; simp [pLoop] at h
    · intro _ _ _ _ _ _ _ _ h; simp [pApp] at h
    · intro _ _ _ _ _ _ _ _ h; simp [pCallDef] at h
    · intro _ _ _ _ _ _ _ h; simp [pArgs] at h
    · intro _ _ _ _ _ _ _ _ h; simp [pAtom] at h
    · intro _ _ _ _ _ _ _ h; simp [pTup] at h
  intro f
  induction f with
  | zero => intro g hg; rw [Nat.le_zero.1 hg]; exact base
  | succ f ih =>
    intro g hg
    rcases Nat.lt_or_eq_of_le hg with hg | rfl
    · exact ih g (by omega)
    · have pE := fun g h => (ih g h).1; have pB := fun g h => (ih g h).2.1; have pL := fun g h => (ih g h).2.2.1
      have pA := fun g h => (ih g h).2.2.2.1; have pC := fun g h => (ih g h).2.2.2.2.1
      have pG := fun g h => (ih g h).2.2.2.2.2.1; have pT := fun g h => (ih g h).2.2.2.2.2.2.1
      have pU := fun g h => (ih g h).2.2.2.2.2.2.2
      exact ⟨qE_step f pB pE, qB_step f pA pL, qL_step f pB pL, qA_step f pT pG pC, qC_step f pG, qG_step f pT pG,
        qT_step f pE pU, qU_step f pE pU⟩

theorem pExpr_len {f cx tl ts nx e ty r nx'} (h : pExpr f cx tl ts nx = some (e, ty, r, nx')) :
    L e + 3 * r.length ≤ 3 * ts.length :=
  (q_all f f (Nat.le_refl _)).1 _ _ _ _ _ _ _ _ h

/-! ## headers consume tokens -/
theorem pTy_le : ∀ f, (∀ ts t r, pTyAtom f ts = some (t, r) → r.length < ts.length) ∧
    (∀ ts t r, pTy f ts = some (t, r) → r.length < ts.length)
  | 0 => ⟨fun _ _ _ h => by simp [pTyAtom] at h, fun _ _ _ h => by simp [pTy] at h⟩
  | f + 1 => by
    have ih := pTy_le f
    refine ⟨fun ts t r h => ?_, fun ts t r h => ?_⟩
    · unfold pTyAtom at h
      split at h
      all_goals (try (simp only [Nat.add_right_cancel_iff, Nat.succ.injEq] at *; subst_vars))
      all_goals first
        | (cases h; simp only [List.length_cons]; omega)
        | (obtain ⟨⟨t1, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
           have := ih.2 _ _ _ h1
           simp only at h; split at h
           · cases h; simp only [List.length_cons] at *; omega
           · cases h)
        | cases h
    · unfold pTy at h
      obtain ⟨⟨a, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
      have h1' := ih.1 _ _ _ h1
      simp only at h; split at h
      · obtain ⟨⟨b, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.1 h
        have := ih.2 _ _ _ h2
        cases h; simp only [List.length_cons] at *; omega
      · cases h; omega

theorem pArrows_le : ∀ f ts l r, pArrows f ts = some (l, r) → r.length < ts.length
  | 0, _, _, _, h => by simp [pArrows] at h
  | f + 1, ts, l, r, h => by
    unfold pArrows at h
    obtain ⟨⟨t, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
    have := (pTy_le f).2 _ _ _ h1
    simp only at h; split at h
    · obtain ⟨⟨l2, r2⟩, h2, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
      have := pArrows_le f _ _ _ h2; simp only [List.length_cons] at *; omega
    · cases h; omega

theorem ids_le : ∀ ts ns r, pBinders.ids ts = some (ns, r) → r.length ≤ ts.length
  | [], _, _, h => by simp [pBinders.ids] at h; obtain ⟨-, rfl⟩ := h; simp
  | .id a :: ts, ns, r, h => by
    simp only [pBinders.ids] at h
    obtain ⟨⟨l, r'⟩, h1, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
    have := ids_le _ _ _ h1; simp only [List.length_cons] at *; omega
  | .k _ :: ts, ns, r, h => by simp only [pBinders.ids, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
  | .num _ :: ts, ns, r, h => by simp only [pBinders.ids, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp

theorem pBinders_le : ∀ f b ts g r, pBinders f b ts = some (g, r) → r.length ≤ ts.length
  | 0, _, _, _, _, h => by simp [pBinders] at h
  | f + 1, b, ts, g, r, h => by
    unfold pBinders at h
    split at h
    all_goals (try (simp only [Nat.add_right_cancel_iff, Nat.succ.injEq] at *; subst_vars))
    · cases h
    · obtain ⟨⟨ns, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
      have e1 := ids_le _ _ _ h1
      simp only at h; split at h
      · obtain ⟨⟨t, r3⟩, h3, h⟩ := Option.bind_eq_some_iff.1 h
        have e3 := (pTy_le _).2 _ _ _ h3
        simp only at h; split at h
        · obtain ⟨⟨g', r5⟩, h5, he⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
          have := pBinders_le _ _ _ _ _ h5; simp only [List.length_cons] at *; omega
        · obtain ⟨⟨g', r5⟩, h5, he⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
          have := pBinders_le _ _ _ _ _ h5; simp only [List.length_cons] at *; omega
        · cases h
      · cases h
    · cases h; omega

theorem armPat_le (n : Nat) : ∀ ts l r, armPat n ts = some (l, r) → r.length ≤ ts.length
  | .k 19 :: r, l, r', h => by simp only [armPat, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
  | .k 15 :: .id a :: r, l, r', h => by
    simp only [armPat] at h
    obtain ⟨⟨l', r''⟩, h1, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
    have := armPat_le n _ _ _ h1; simp only [List.length_cons] at *; omega
  | [], _, _, h => by simp [armPat] at h
  | .k 15 :: [], _, _, h => by simp [armPat] at h
  | .k 15 :: .k _ :: _, _, _, h => by simp [armPat] at h
  | .k 15 :: .num _ :: _, _, _, h => by simp [armPat] at h
  | .k (t + 20) :: _, _, _, h => by simp [armPat] at h
  | .k 16 :: _, _, _, h => by simp [armPat] at h
  | .k 17 :: _, _, _, h => by simp [armPat] at h
  | .k 18 :: _, _, _, h => by simp [armPat] at h
  | .k 0 :: _, _, _, h => by simp [armPat] at h
  | .k 1 :: _, _, _, h => by simp [armPat] at h
  | .k 2 :: _, _, _, h => by simp [armPat] at h
  | .k 3 :: _, _, _, h => by simp [armPat] at h
  | .k 4 :: _, _, _, h => by simp [armPat] at h
  | .k 5 :: _, _, _, h => by simp [armPat] at h
  | .k 6 :: _, _, _, h => by simp [armPat] at h
  | .k 7 :: _, _, _, h => by simp [armPat] at h
  | .k 8 :: _, _, _, h => by simp [armPat] at h
  | .k 9 :: _, _, _, h => by simp [armPat] at h
  | .k 10 :: _, _, _, h => by simp [armPat] at h
  | .k 11 :: _, _, _, h => by simp [armPat] at h
  | .k 12 :: _, _, _, h => by simp [armPat] at h
  | .k 13 :: _, _, _, h => by simp [armPat] at h
  | .k 14 :: _, _, _, h => by simp [armPat] at h
  | .num _ :: _, _, _, h => by simp [armPat] at h
  | .id _ :: _, _, _, h => by simp [armPat] at h

/-! ## defs and programs -/
theorem pDef_len {fuel defs ts di da r} (h : pDef fuel defs ts = some (di, da, r)) :
    da.ser.length + 4 * r.length ≤ 4 * ts.length := by
  unfold pDef at h
  split at h
  · split at h
    · cases h
    · split at h
      · -- fuel loop
        obtain ⟨⟨tys, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
        have e1 := pArrows_le _ _ _ _ h1
        simp only at h
        split at h
        · split at h
          · cases h
          · split at h
            · obtain ⟨⟨zn, r3⟩, h3, h⟩ := Option.bind_eq_some_iff.1 h
              have e3 := armPat_le _ _ _ _ h3
              split at h
              · cases h
              · obtain ⟨envZ, -, h⟩ := Option.bind_eq_some_iff.1 h
                obtain ⟨⟨z, tz, r4, nx1⟩, h4, h⟩ := Option.bind_eq_some_iff.1 h
                have e4 := pExpr_len h4
                simp only at h
                split at h
                · cases h
                · split at h
                  · obtain ⟨⟨sn, r6⟩, h6, h⟩ := Option.bind_eq_some_iff.1 h
                    have e6 := armPat_le _ _ _ _ h6
                    split at h
                    · cases h
                    · obtain ⟨envS, -, h⟩ := Option.bind_eq_some_iff.1 h
                      obtain ⟨⟨sb, ts', r7, nx2⟩, h7, h⟩ := Option.bind_eq_some_iff.1 h
                      have e7 := pExpr_len h7
                      simp only at h
                      split at h
                      · split at h
                        · cases h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h
                        simp only [DefA.ser, L, Nd.ser, List.length_append, List.length_cons, List.length_nil] at *
                        omega
                      · cases h
                  · cases h
            · cases h
        · cases h
      · -- plain def
        obtain ⟨⟨groups, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
        have e1 := pBinders_le _ _ _ _ _ h1
        simp only at h
        split at h
        · obtain ⟨⟨resT, r3⟩, h3, h⟩ := Option.bind_eq_some_iff.1 h
          have e3 := (pTy_le _).2 _ _ _ h3
          simp only at h
          split at h
          · split at h
            · cases h
            · obtain ⟨⟨b, tb, r5, nx⟩, h5, h⟩ := Option.bind_eq_some_iff.1 h
              have e5 := pExpr_len h5
              simp only at h
              split at h
              · cases h
              · split at h
                · cases h
                simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h
                simp only [DefA.ser, L, List.length_append, List.length_cons, List.length_nil] at *
                omega
          · cases h
        · cases h
  · cases h

theorem pDefs_len (fuel : Nat) : ∀ (f : Nat) (defs : List DefI) (ts : List Tok) (ds : List DefI) (as : List DefA),
    pDefs fuel f defs ts = some (ds, as) → (as.flatMap DefA.ser).length ≤ 4 * ts.length
  | 0, _, _, _, _, h => by simp [pDefs] at h
  | f + 1, defs, ts, ds, as, h => by
    unfold pDefs at h
    split at h
    · cases h
    · cases h; simp
    · rename_i f0 heq _
      obtain rfl : f = f0 := by omega
      obtain ⟨⟨di, da, r⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨ds', as'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
      have := pDef_len hd
      have := pDefs_len fuel f _ _ _ _ hr
      simp only [List.flatMap_cons, List.length_append]; omega

theorem idn_le : ∀ l n r, idn l = some (n, r) → r.length < l.length
  | 0 :: r, n, r', h => by simp only [idn, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
  | 1 :: b :: r, n, r', h => by
    simp only [idn] at h
    obtain ⟨⟨n', r''⟩, h1, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
    have := idn_le _ _ _ h1; simp only [List.length_cons]; omega
  | [], _, _, h => by simp [idn] at h
  | [1], _, _, h => by simp [idn] at h
  | (k + 2) :: _, _, _, h => by simp [idn] at h

theorem detokA_len : ∀ f l acc toks, detokA f l acc = some toks → toks.length ≤ acc.length + l.length
  | _, [], acc, toks, h => by simp only [detokA, Option.some.injEq] at h; subst h; simp
  | 0, _ :: _, _, _, h => by simp [detokA] at h
  | f + 1, t :: r, acc, toks, h => by
    simp only [detokA] at h
    split at h
    · split at h
      · have := detokA_len f _ _ _ h; simp only [List.length_drop, List.length_cons] at *; omega
      · cases h
    · split at h
      · obtain ⟨⟨n, r'⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
        have := idn_le _ _ _ h1
        have := detokA_len f _ _ _ h; simp only [List.length_cons] at *; omega
      · split at h
        · have := detokA_len f _ _ _ h; simp only [List.length_cons] at *; omega
        · cases h

theorem tokens_len {ts : List UInt64} {toks : List Tok} (h : tokens ts = some toks) : toks.length ≤ ts.length := by
  have := detokA_len _ _ _ _ h; simpa using this

/-- **the serialization is linear in the token stream** -/
theorem ser_len {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) : (serialize p).length ≤ 4 * ts.length + 1 := by
  unfold ParsesProgram refParse at h
  obtain ⟨toks, ht, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨ds, as⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
  have e1 := tokens_len ht
  have e2 := pDefs_len _ _ _ _ _ _ hd
  simp only at h
  split at h
  · split at h
    · cases h; simp only [serialize, List.length_cons]; omega
    · cases h
  · cases h

/-- E's `hXl` -/
theorem ser_lt {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) (hts : ts.length < 2 ^ 24) :
    (serialize p).length < 2 ^ 31 := by
  have := ser_len h; omega

end ParSerLen
