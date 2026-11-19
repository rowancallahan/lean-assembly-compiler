/- Nano/V2Self/Proof/ParInvPrimary: Layer-3 handler `prim md` (task 3, v104 / v104b), box C.
`prim_nonid`: every branch except an identifier at the cursor (if, let, numeral, paren, `[]`, prim heads). -/
import Nano.V2Self.Proof.ParInvNum
import Nano.V2Self.Proof.ParInvPrim
namespace ParInv
open C BufL ParSpec ParRun

theorem v104b_cell (g : Buf) (a b : UInt64) :
    v104b g a b =
      (if bget g (d11 + bget g 3) == 32 then v1 (v1 (bset g 3 (bget g 3 + 1)) 6 0 b) 1 0 2
      else if bget g (d11 + bget g 3) == 2 then v1 (bset g 3 (bget g 3 + 1)) 41 0 b
      else if bget g (d11 + bget g 3) == 5 then
        v5 (bset (v87 g (bget g 3)) 3 (bget (v87 g (bget g 3)) 3 + 9)) 1 (bget (v87 g (bget g 3)) 31) 0 1 0 0
      else if bget g (d11 + bget g 3) == 6 then v1 (v1 (bset g 3 (bget g 3 + 1)) 40 0 0) 1 0 b
      else if bget g (d11 + bget g 3) == 14 then v104b g a b
      else if bget g (d11 + bget g 3) == 30 then
        (if bget g (d11 + bget g 3 + 1) == 31 then v5 (bset g 3 (bget g 3 + 2)) 9 5 0 3 0 0 else bset g 0 0)
      else v93 g (bget g 3) b) := by
  by_cases c32 : bget g (d11 + bget g 3) = 32
  · simp [v104b, c32]
  by_cases c2 : bget g (d11 + bget g 3) = 2
  · simp [v104b, c2]
  by_cases c5 : bget g (d11 + bget g 3) = 5
  · simp [v104b, c5]
  by_cases c6 : bget g (d11 + bget g 3) = 6
  · simp [v104b, c6]
  by_cases c14 : bget g (d11 + bget g 3) = 14
  · simp [c14]
  simp [v104b, c32, c2, c5, c6, c14]

theorem primAr_le (p : Nat) : primAr p ≤ 3 := by
  unfold primAr; split
  · omega
  · split
    · omega
    · split <;> omega

/-- the non-identifier branches of v104b on Rep -/
theorem prim_nonid {g ts : Buf} {st : St} {fs : List Frame} {a : UInt64} {md : Nat} (R1 : Rep g ts st fs)
    (hnf : fs.all (fun f => !f.isFlat)) (c14 : bget g (d11 + bget g 3) ≠ 14)
    (hm2 : md = 2 → bget g (d11 + bget g 3) ≠ 32 ∧ bget g (d11 + bget g 3) ≠ 2)
    (hs : bget (v104b g a (b01 (md == 1))) 0 ≠ 0) :
    ∃ k st', stepF (.prim md) st = some (k, st') ∧ Rep (v104b g a (b01 (md == 1))) ts st' (k ++ fs) := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  rw [v104b_cell] at hs ⊢
  have dead : ∀ x : Buf, x = bset g 0 0 → bget x 0 ≠ 0 → False := fun x e hx => hx (by rw [e]; exact stat0 _ (by omega))
  -- B's mode guard is off whenever the token is not if / let
  have guard : ∀ t rest, st.toks = .k t :: rest → t ≠ 32 → t ≠ 2 → ¬ (md = 2 ∧ (st.toks.head? = some (.k 32) ∨ st.toks.head? = some (.k 2))) := by
    intro t rest et t32 t2 ⟨_, h2⟩; rw [et] at h2; simp at h2; omega
  by_cases c32 : bget g (d11 + bget g 3) = 32
  · simp only [c32, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, R2⟩ := cur_tok R1 32 c32 (by decide) (by decide) (by decide)
    have nm2 : md ≠ 2 := fun e => (hm2 e).1 c32
    have R3 := rep_push (.ifCmp (md == 1)) 0 (b01 (md == 1)) R2 (by simp [inDefF, Frame.isDefs]) rfl (pushOK hs)
    have R4 := rep_push (.expr 0 2) 0 2 R3 (by simp [inDefF, Frame.isDefs]) ⟨rfl, rfl⟩ hs
    refine ⟨[.expr 0 2, .ifCmp (md == 1)], _, ?_, R4⟩
    simp [stepF, et, nm2]
  have n32 : (bget g (d11 + bget g 3) == 32) = false := by simpa using c32
  simp only [n32, Bool.false_eq_true, if_false] at hs ⊢
  by_cases c2 : bget g (d11 + bget g 3) = 2
  · simp only [c2, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, R2⟩ := cur_tok R1 2 c2 (by decide) (by decide) (by decide)
    have nm2 : md ≠ 2 := fun e => (hm2 e).2 c2
    have R3 := rep_push (.letStart (md == 1)) 0 (b01 (md == 1)) R2 (by simp [inDefF, Frame.isDefs]) rfl hs
    refine ⟨[.letStart (md == 1)], _, ?_, R3⟩
    simp [stepF, et, nm2]
  have n2 : (bget g (d11 + bget g 3) == 2) = false := by simpa using c2
  simp only [n2, Bool.false_eq_true, if_false] at hs ⊢
  by_cases c5 : bget g (d11 + bget g 3) = 5
  · simp only [c5, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨v, rest, et, R2⟩ := rep_const R1 hnf c5 hs
    refine ⟨[], _, ?_, R2⟩
    simp [stepF, et]
  have n5 : (bget g (d11 + bget g 3) == 5) = false := by simpa using c5
  simp only [n5, Bool.false_eq_true, if_false] at hs ⊢
  by_cases c6 : bget g (d11 + bget g 3) = 6
  · simp only [c6, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, R2⟩ := cur_tok R1 6 c6 (by decide) (by decide) (by decide)
    have R3 := rep_push .parenClose 0 0 R2 (by simp [inDefF, Frame.isDefs]) trivial (pushOK hs)
    have R4 := rep_push (.expr 0 (bm (md == 1))) 0 (b01 (md == 1)) R3 (by simp [inDefF, Frame.isDefs]) ⟨rfl, b01_toNat _⟩ hs
    refine ⟨[.expr 0 (bm (md == 1)), .parenClose], _, ?_, R4⟩
    have g6 := guard 6 rest et (by decide) (by decide)
    simp [stepF, et]
  have n6 : (bget g (d11 + bget g 3) == 6) = false := by simpa using c6
  have n14 : (bget g (d11 + bget g 3) == 14) = false := by simpa using c14
  simp only [n6, n14, Bool.false_eq_true, if_false] at hs ⊢
  have p3le := R1.2.2.2.1.le
  by_cases c30 : bget g (d11 + bget g 3) = 30
  · simp only [c30, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw R1.2.2.2.1 R1.1 R1.2.1 c30 (by decide) (by decide) (by decide)
    have ea : d11 + bget g 3 + 1 = d11 + (bget g 3 + 1) := by rw [UInt64.add_assoc]
    rw [ea] at hs ⊢
    by_cases c31 : bget g (d11 + (bget g 3 + 1)) = 31
    · simp only [c31, beq_self_eq_true, if_true] at hs ⊢
      obtain ⟨rest2, et2, tr2⟩ := tok_kw tr R1.1 R1.2.1 c31 (by decide) (by decide) (by decide)
      have e2 : bget g 3 + 1 + 1 = bget g 3 + 2 := by rw [UInt64.add_assoc]; rfl
      rw [e2] at tr2
      have R2 := rep_set3 R1 tr2
      obtain ⟨st', em, R3⟩ := rep_v5g R2 hnf 0 9 5 0 (some .ls) false 3 .ls (by decide) (fun _ _ => ⟨by decide, by decide⟩)
        (by decide) (by simpa [b01] using hs)
      rw [mkNode_leaf0] at em
      cases em
      refine ⟨[], _, ?_, by simpa [b01] using R3⟩
      simp [stepF, et, et2]
    · have n : (bget g (d11 + (bget g 3 + 1)) == 31) = false := by simpa using c31
      simp only [n, Bool.false_eq_true, if_false] at hs; exact (dead _ rfl hs).elim
  · have n30 : (bget g (d11 + bget g 3) == 30) = false := by simpa using c30
    simp only [n30, Bool.false_eq_true, if_false] at hs ⊢
    generalize hT : bget g (d11 + bget g 3) = T at c32 c2 c5 c6 c14 c30
    simp only [v93, v0, hT] at hs ⊢
    have g31 : ∀ z : UInt64, bget (bset g 31 z) 31 = z := fun z => bget_bset_eq _ _ _ _ rfl (by simp; omega)
    simp only [g31] at hs ⊢
    by_cases hr : 38 < T ∧ T < 48
    · obtain ⟨t1, t2⟩ := hr
      have t1' := UInt64.lt_iff_toNat_lt.mp t1; have t2' := UInt64.lt_iff_toNat_lt.mp t2
      simp only [show (38 : UInt64).toNat = 38 from rfl, show (48 : UInt64).toNat = 48 from rfl] at t1' t2'
      simp only [t1, t2, if_true] at hs ⊢
      have ej : (T - 38).toNat = T.toNat - 38 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
      have j0 : (T - 38 == 0) = false := by
        apply beq_false_of_ne; intro e; have := congrArg UInt64.toNat e; rw [ej] at this; simp at this; omega
      simp only [j0, Bool.false_eq_true, if_false] at hs ⊢
      have R0 := rep_31 R1 (T - 38)
      have e3' : bget (bset g 31 (T - 38)) 3 = bget g 3 := bget_bset' _ _ _ _ (by decide)
      have c0 : bget (bset g 31 (T - 38)) (d11 + bget (bset g 31 (T - 38)) 3) = T := by
        rw [e3', bget_bset' _ _ _ _ (by rw [d11a _ (by omega), show (31 : UInt64).toNat = 31 from rfl]; omega)]; exact hT
      obtain ⟨rest, et, R2⟩ := cur_tok R0 T c0 (by intro e; subst e; simp at t1') (by intro e; subst e; simp at t1')
        (by intro e; subst e; simp at t1')
      have e3 : bget (bset g 31 (T - 38)) 3 = bget g 3 := bget_bset' _ _ _ _ (by decide)
      rw [e3] at R2
      rw [e3'] at hs ⊢
      have hp : T.toNat - 38 < 2 ^ 64 := by omega
      have ecw : calleeW (.pr (T.toNat - 38)) = 512 + (T - 38) := by
        simp only [calleeW]; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, ej]; simp <;> omega
      have e8 := R2.2.2.2.2.2.2.2.1.2.2.1
      have R3 := rep_push (.mkCallN (.pr (T.toNat - 38)) st.vals.length) (512 + (T - 38)) (bget (bset (bset g 31 (T - 38)) 3 (bget g 3 + 1)) 8)
        R2 (by simp [inDefF, Frame.isDefs]) ⟨ecw.symm, e8⟩ (pushOK hs)
      have ev91 : v91 (T - 38) = (primAr (T.toNat - 38)).toUInt64 := by
        rw [← v91_eq hp]; congr 1; apply UInt64.toNat_inj.mp; rw [ej]; simp <;> omega
      have R4 := rep_push (.args (.pr (T.toNat - 38)) (primAr (T.toNat - 38))) (512 + (T - 38)) (v91 (T - 38)) R3
        (by simp [inDefF, Frame.isDefs]) ⟨ecw.symm, by rw [ev91]; have := primAr_le (T.toNat - 38); simp; omega⟩ hs
      refine ⟨[.args (.pr (T.toNat - 38)) (primAr (T.toNat - 38)), .mkCallN (.pr (T.toNat - 38)) st.vals.length], _, ?_, R4⟩
      have h32 : T.toNat ≠ 32 := by omega
      have h2' : T.toNat ≠ 2 := by omega
      have h6 : T.toNat ≠ 6 := by omega
      have h30 : T.toNat ≠ 30 := by omega
      have nm : ¬ (md = 2 ∧ (some (Tok.k T.toNat) = some (.k 32) ∨ some (Tok.k T.toNat) = some (.k 2))) := by
        intro ⟨_, h⟩; simp at h; omega
      simp only [stepF, et, List.head?_cons, nm, if_false]
      split
      all_goals first
        | (rename_i heq; simp at heq; omega)
        | (rename_i heq; simp at heq)
        | skip
      rename_i heq
      obtain ⟨e1, e2⟩ := heq
      subst e1; subst e2
      rw [if_pos ⟨h30, by omega, by omega⟩]
    · have z : (if 38 < T then if T < 48 then T - 38 else 0 else 0 : UInt64) = 0 := by
        by_cases a1 : 38 < T
        · have a2 : ¬ T < 48 := fun x => hr ⟨a1, x⟩
          simp [a1, a2]
        · simp [a1]
      simp only [z, beq_self_eq_true, if_true] at hs
      exact absurd (stat0 _ (by simp [length_bset]; omega)) hs

/-! ## identifiers: the def lookup over all rows (finished defs and the current one) -/
theorem defTabRows_of {h : Buf} {st : St} (hD : DefsRep h st true) (h7 : (bget h 7).toNat < 2 ^ 24) :
    ∃ tab : List (UInt64 × List UInt64), tab.length = (rows st).length ∧ DefTabRep h tab ∧
      ∀ i (hi : i < tab.length) (hi' : i < (rows st).length), (tab[i].2).map UInt64.toNat = ((rows st)[i]'hi').name := by
  obtain ⟨tab, hl, hT, hn⟩ := defTab_of hD h7
  obtain ⟨_, _, _, _, rc, _⟩ := hD
  simp only [if_true] at rc
  obtain ⟨⟨nm, hok, hmap⟩, _⟩ := rc.1
  refine ⟨tab ++ [(bget h (d7 + 8 * st.defs.length.toUInt64), nm)], by simp [rows, hl], fun i hi => ?_, fun i hi hi' => ?_⟩
  · by_cases hin : i < tab.length
    · rw [List.getElem_append_left hin]; exact hT i hin
    · have : i = st.defs.length := by simp at hi; omega
      subst this
      rw [List.getElem_append_right (by omega)]
      simp only [hl, Nat.sub_self, List.getElem_cons_zero]
      exact ⟨by simp, hok, by obtain ⟨_, _, hb⟩ := hok; omega⟩
  · by_cases hin : i < tab.length
    · rw [List.getElem_append_left hin]
      have := hn i hin (by omega)
      simp only [rows]; rw [List.getElem_append_left (by omega)]; exact this
    · have : i = st.defs.length := by simp at hi; omega
      subst this
      rw [List.getElem_append_right (by omega)]
      simp only [rows, hl, Nat.sub_self, List.getElem_cons_zero]
      rw [List.getElem_append_right (by omega)]; simp [hmap]

theorem v8_rows {h : Buf} {st : St} {p : UInt64} {nm : List UInt64} (hD : DefsRep h st true)
    (h7 : (bget h 7).toNat < 2 ^ 24) (hl : 31 < h.length) (hn : NameOK h p nm) :
    Same 22 h (v8 16777216 h (bget h 12 + 1) p) ∧
    bget (v8 16777216 h (bget h 12 + 1) p) 22 = (((findD (rows st) (nm.map UInt64.toNat)).map (· + 1)).getD 0).toUInt64 := by
  obtain ⟨tab, htl, hTab, hnames⟩ := defTabRows_of hD h7
  have e12 := hD.1; have hlt := hD.2.1
  have hnm : nm.length < 2 ^ 24 := by obtain ⟨_, _, hb⟩ := hn; omega
  have hr : (rows st).length = st.defs.length + 1 := by simp [rows]
  obtain ⟨s22, h22⟩ := v8_lookup tab p nm (st.defs.length + 1) 16777216 h (bget h 12 + 1)
    (by rw [tn_add _ _ (by simp; omega), e12]; rfl) (by omega) (by omega) (by omega) hl (by omega) hTab hn hnm
  refine ⟨s22, ?_⟩
  rw [h22, idxOf_findD tab (rows st) nm _ rfl (by omega) (fun i hi hi' => hnames i hi hi') _ (by omega), ← hr, List.take_length]

/-- the identifier branch of v104b, up to the cursor move: v0 (scratch), v7 (bindings), v8 (all rows), v86 (skip) -/
theorem prim_id_setup {g ts : Buf} {st : St} {fs : List Frame} (R1 : Rep g ts st fs) (hin : inDefF fs = true)
    (c14 : bget g (d11 + bget g 3) = 14) :
    ∃ (nm : List UInt64) (rest : List Tok) (q : UInt64), st.toks = .id (nm.map UInt64.toNat) :: rest ∧
      let g1 := bset g 31 0
      let g2 := v7 16777216 g1 (bget g1 4) (bget g 3)
      let g3 := v8 16777216 g2 (bget g2 12 + 1) (bget g 3)
      v86 16777216 g3 (bget g3 3 + 1) = bset g3 3 q ∧ bget (v0 g (bget g 3)) 31 = 0 ∧ v0 g (bget g 3) = g1 ∧
      Rep (bset g3 3 q) ts { st with toks := rest } fs ∧
      ((bget g3 21 = 0 ∧ findB st.binds (nm.map UInt64.toNat) = none) ∨
        (∃ i, bget g3 21 = (i + 1).toUInt64 ∧ ∃ hi : i < st.binds.length,
          findB st.binds (nm.map UInt64.toNat) = some (st.binds[i]'hi))) ∧
      bget g3 22 = (((findD (rows st) (nm.map UInt64.toNat)).map (· + 1)).getD 0).toUInt64 ∧
      Same 21 g g2 ∧ Same 22 g2 g3 := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have h7 : (bget g 7).toNat < 2 ^ 24 := by rw [R1.1.2.2.2]; have := R1.2.1; simp; omega
  obtain ⟨nm, rest, et, hNm, tr⟩ := tok_id R1.2.2.2.1 R1.1 c14
  have z0 : v0 g (bget g 3) = bset g 31 0 := by simp [v0, c14]
  have R1' := rep_31 R1 0
  have e31 : ∀ i : UInt64, i.toNat ≠ 31 → bget (bset g 31 0) i = bget g i := fun i hi => bget_bset' _ _ _ _ (by simp; omega)
  have et1 : TokAgree g (bset g 31 0) := ⟨e31 7 (by decide), fun i hi => e31 i (by omega)⟩
  have hNm1 : NameOK (bset g 31 0) (bget g 3) nm := nameOK_frame et1 (by omega) hNm
  have h71 : (bget (bset g 31 0) 7).toNat < 2 ^ 24 := by rw [e31 7 (by decide)]; exact h7
  have hl1 : 31 < (bset g 31 0).length := by simp [length_bset]; omega
  obtain ⟨s21, hfb⟩ := v7_findB R1'.2.2.2.2.2.1 h71 hl1 hNm1
  have R2 := rep_same R1' s21 (Or.inl rfl) (v7_drop _ _ _ _)
  generalize hg2 : v7 16777216 (bset g 31 0) (bget (bset g 31 0) 4) (bget g 3) = g2 at s21 hfb R2
  have et2 : TokAgree (bset g 31 0) g2 := ⟨s21.2 7 (by decide) (by decide), fun i hi => s21.2 i (by omega) (by omega)⟩
  have hNm2 : NameOK g2 (bget g 3) nm := nameOK_frame et2 (by omega) hNm1
  have h72 : (bget g2 7).toNat < 2 ^ 24 := by rw [et2.1]; exact h71
  have hl2 : 31 < g2.length := by rw [s21.1]; exact hl1
  have hD2 : DefsRep g2 st true := by have := R2.2.2.2.2.2.2.1; rwa [hin] at this
  obtain ⟨s22, h22⟩ := v8_rows hD2 h72 hl2 hNm2
  have R3 := rep_same R2 s22 (Or.inr rfl) (v8_drop _ _ _ _)
  generalize hg3 : v8 16777216 g2 (bget g2 12 + 1) (bget g 3) = g3 at s22 h22 R3
  have et3 : TokAgree g2 g3 := ⟨s22.2 7 (by decide) (by decide), fun i hi => s22.2 i (by omega) (by omega)⟩
  have hNm3 : NameOK g3 (bget g 3) nm := nameOK_frame et3 (by omega) hNm2
  have e33 : bget g3 3 = bget g 3 := by rw [s22.2 3 (by decide) (by decide), s21.2 3 (by decide) (by decide), e31 3 (by decide)]
  have p1 : (bget g 3 + 1).toNat = (bget g 3).toNat + 1 := by have := hNm.2.2; rw [UInt64.toNat_add]; simp; omega
  have sk := v86_skip nm 16777216 g3 (bget g 3 + 1) hNm3.2.1 (by have := hNm3.2.2; rw [p1]; omega) (by have := hNm.2.2; omega)
  have eq : bget g 3 + 1 + 2 * nm.length.toUInt64 + 1 = bget g 3 + 2 + 2 * nm.length.toUInt64 := by
    apply UInt64.toNat_inj.mp
    have l2 : (2 * nm.length.toUInt64).toNat = 2 * nm.length := by have := hNm.2.2; rw [UInt64.toNat_mul]; simp; omega
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, l2]; simp; omega
  rw [eq] at sk
  have et13 : TokAgree g g3 := ⟨by rw [et3.1, et2.1, et1.1], fun i hi => by rw [et3.2 i hi, et2.2 i hi, et1.2 i hi]⟩
  have c21 : bget g3 21 = bget g2 21 := s22.2 21 (by decide) (by decide)
  subst hg3; subst hg2
  refine ⟨nm, rest, _, et, by rw [e33]; exact sk, by rw [z0]; exact bget_bset_eq _ _ _ _ rfl (by simp; omega), z0,
    rep_set3 R3 (tokAt_frame et13 hn7 tr), by rw [c21]; exact hfb, h22, ?_, s22⟩
  exact ⟨by rw [s21.1, length_bset], fun i a b => by rw [s21.2 i a b, e31 i b]⟩

end ParInv
