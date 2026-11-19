/- Nano/V2Self/Proof/Parser/ParInvAtom: Layer 3, pieces for task 43 `argAtom` (v120), box G: `tok_num` (a numeral under the cursor),
`v9_cw` (v9's width word = Layer 2's `cw`), `ShapeCode.nt_code`.  The handler itself waits for `rep_v5` without the
`A, B < 2^64` bounds (a LOC node's slot is only known mod 2^64). -/
import Nano.V2Self.Proof.Parser.ParInvArgName
namespace ParInv
open C BufL ParSpec ParRun

theorem tok_num {h ts : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) (hT : TokensAt h ts) (hc : bget h (d11 + p) = 5) :
    ∃ v rest, toks = .num v :: rest := by
  cases r with
  | nil e => exfalso; rw [e, hT.2.2.2, hT.2.1] at hc; exact absurd hc (by decide)
  | kw t _ b t5 _ _ _ => rw [b] at hc; exact absurd hc t5
  | num _ _ _ => exact ⟨_, _, rfl⟩
  | id _ a _ => rw [a.1] at hc; exact absurd hc (by decide)

theorem ShapeCode.nt_code {h : Buf} {c : UInt64} (r : ShapeCode h c .nt) : c = 4 := by
  cases r; rfl

/-- v9's width word is `cw` of the decoded shape (code 0 counts 1) -/
theorem v9_cw {h : Buf} {w : UInt64} {o : Option Sh} (r : ShOpt h w o) :
    (if w < 5 then 1 else bget h ((d7 + 8192) + 3 * (w - 5) + 2)) = (cw o).toUInt64 := by
  cases o with
  | none => simp only [ShOpt] at r; subst r; rfl
  | some s =>
    simp only [ShOpt] at r
    cases r with
    | uw => rfl
    | bf => rfl
    | ls => rfl
    | nt => rfl
    | pr h5 _ _ _ hw _ _ =>
      have : ¬ w < 5 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
      simp only [this, if_false, hw, cw, Sh.width]

theorem tok_cell_num {h : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) {v : Nat} {rest : List Tok}
    (e : toks = .num v :: rest) : bget h (d11 + p) = 5 := by
  cases r with
  | nil _ => cases e
  | kw t _ _ _ _ _ _ => cases e
  | num _ _ b5 => exact b5
  | id _ _ _ => cases e

theorem tok_cell_id {h : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) {x : List Nat} {rest : List Tok}
    (e : toks = .id x :: rest) : bget h (d11 + p) = 14 := by
  cases r with
  | nil _ => cases e
  | kw t _ _ _ _ _ _ => cases e
  | num _ _ _ => cases e
  | id _ a14 _ => exact a14.1

/-! ## task 43: `argAtom` (v120) -/
theorem h_argAtom {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.argAtom :: fs))
    (hnf : fs.all (fun f => !f.isFlat)) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF .argAtom st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rT := R1.1; have rts := R1.2.1; have r3 := R1.2.2.2.1
  have h7 : (bget g 7).toNat < 2 ^ 24 := by rw [rT.2.2.2]; simp; omega
  have p3 := r3.le
  have hl31 : 31 < g.length := by omega
  by_cases c6 : bget g (d11 + bget g 3) = 6
  · have ev : step h = v1 (v1 (bset g 3 (bget g 3 + 1)) 40 0 0) 1 0 0 := by rw [E]; simp [v96, v120, c6]
    rw [ev] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c6 (by decide) (by decide) (by decide)
    have R2 := rep_cursor R1 (bget g 3 + 1) tr
    have R3 := rep_push .parenClose 0 0 R2 rfl trivial (fun z => hs (v1_zero _ _ _ _ z))
    have R4 := rep_push (.expr 0 0) 0 0 R3 rfl ⟨rfl, rfl⟩ hs
    exact ⟨[.expr 0 0, .parenClose], { st with toks := rest }, by simp [stepF, et], R4⟩
  by_cases c5 : bget g (d11 + bget g 3) = 5
  · have ev : step h = v1 g 3 0 0 := by rw [E]; simp [v96, v120, c5]
    rw [ev] at hs ⊢
    obtain ⟨v, rest, et⟩ := tok_num r3 rT c5
    have R2 := rep_push (.prim 0) 0 0 R1 rfl rfl hs
    exact ⟨[.prim 0], st, by simp [stepF, et], R2⟩
  by_cases c14 : bget g (d11 + bget g 3) = 14
  · obtain ⟨nm, rest, et, hNm, tr⟩ := tok_id r3 rT c14
    have rB := R1.2.2.2.2.2.1
    obtain ⟨s21, hfb⟩ := v7_findB rB h7 hl31 hNm
    have hdrop := v7_drop 16777216 g (bget g 4) (bget g 3)
    have ev : step h = v120 g a b := by rw [E]; simp [v96]
    rw [ev] at hs ⊢
    unfold v120 at hs ⊢
    simp only [UInt64.add_zero, c14, show ((14 : UInt64) == 6) = false from rfl, show ((14 : UInt64) == 5) = false from rfl,
      beq_self_eq_true, if_true, Bool.false_eq_true, if_false, k0, beq_iff_eq] at hs ⊢
    generalize v7 16777216 g (bget g 4) (bget g 3) = g1 at s21 hfb hdrop hs ⊢
    have R1' : Rep g1 ts st fs := rep_same R1 s21 (Or.inl rfl) hdrop
    rcases hfb with ⟨h0, hnone⟩ | ⟨i, hi1, hilt, hsome⟩
    · rw [if_pos h0] at hs ⊢
      have R2 := rep_push .argName 0 0 R1' rfl trivial hs
      exact ⟨[.argName], st, by simp [stepF, et, hnone], R2⟩
    · have hne : bget g1 21 ≠ 0 := by
        rw [hi1]; intro e; have q := congrArg UInt64.toNat e; have := rB.2.1; simp at q; omega
      have i1024 : i < 1024 := by have := rB.2.1; omega
      have e3 : bget g1 3 = bget g 3 := s21.2 3 (by decide) (by decide)
      have e7 : bget g1 7 = bget g 7 := s21.2 7 (by decide) (by decide)
      have hseq : NameSeq g1 (bget g 3 + 1) nm :=
        nameSeq_same s21 (by decide) nm _ (by have := hNm.2.2; rw [tn_add _ _ (by simp; omega)]; simp; omega) hNm.2.1
      have hskip := v86_skip nm 16777216 g1 (bget g 3 + 1) hseq
        (by rw [e7, tn_add _ _ (by simp; omega)]; have := hNm.2.2; simp; omega) (by have := hNm.2.2; omega)
      rw [if_neg hne, e3, hskip] at hs ⊢
      generalize hP : bget g 3 + 1 + 2 * nm.length.toUInt64 + 1 = P at hs ⊢
      have c2g : ∀ j : UInt64, j.toNat ≠ 3 → bget (bset g1 3 P) j = bget g1 j := fun j a => bget_bset' _ _ _ _ (by simp; omega)
      have hj1 : (i + 1).toUInt64 - 1 = i.toUInt64 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
      have rc : ∀ k : UInt64, k.toNat < 4 → bget (bset g1 3 P) (d9 + 4 * i.toUInt64 + k) = bget g (d9 + 4 * i.toUInt64 + k) := fun k hk => by
        have c := rowCell i i1024 k hk
        rw [c2g _ (by rw [c]; omega), s21.2 _ (by rw [c]; omega) (by rw [c]; omega)]
      obtain ⟨_, a1, a2, a3⟩ := rB.2.2 i hilt
      simp only [c2g 21 (by decide), hi1, hj1, rc 1 (by decide), rc 2 (by decide)] at hs ⊢
      generalize hwv : bget g (d9 + 4 * i.toUInt64 + 2) = wv at hs a2 ⊢
      by_cases cw4 : wv = 4
      · rw [if_pos cw4] at hs
        exact absurd (stat0 _ (by simp only [length_bset]; rw [s21.1]; omega)) hs
      rw [if_neg cw4] at hs ⊢
      have hnt : (st.binds[i]'hilt).sh ≠ some .nt := by
        intro e; rw [e] at a2; exact cw4 (ShapeCode.nt_code a2)
      have es2 : ShTabAgree g (bset g1 3 P) := fun j a _ => by rw [c2g j (by omega), s21.2 j (by omega) (by omega)]
      have ev9 : v9 (bset g1 3 P) wv = bset (bset g1 3 P) 31 (cw (st.binds[i]'hilt).sh).toUInt64 := by
        unfold v9; rw [v9_cw (a2.frame es2)]
      rw [ev9] at hs ⊢
      have l2 : (bset g1 3 P).length = g.length := by rw [length_bset, s21.1]
      have c3g : ∀ j : UInt64, j.toNat ≠ 31 → bget (bset (bset g1 3 P) 31 (cw (st.binds[i]'hilt).sh).toUInt64) j = bget (bset g1 3 P) j :=
        fun j a => bget_bset' _ _ _ _ (by simp; omega)
      have ef : bget (bset (bset g1 3 P) 31 (cw (st.binds[i]'hilt).sh).toUInt64) (d9 + 4 * i.toUInt64 + 3) = b01 (st.binds[i]'hilt).inp := by
        rw [c3g _ (by rw [rowCell i i1024 3 (by decide)]; simp; omega), rc 3 (by decide)]; exact a3
      have e31 : bget (bset (bset g1 3 P) 31 (cw (st.binds[i]'hilt).sh).toUInt64) 31 = (cw (st.binds[i]'hilt).sh).toUInt64 :=
        bget_bset_same _ _ _ (by rw [l2]; exact hl31)
      have eB : (if b01 (st.binds[i]'hilt).inp = 1 then 0 else (cw (st.binds[i]'hilt).sh).toUInt64) =
          (if (st.binds[i]'hilt).inp then 0 else cw (st.binds[i]'hilt).sh).toUInt64 := by
        cases (st.binds[i]'hilt).inp <;> simp [b01]
      rw [ef, e31, eB, a1] at hs ⊢
      have et1 : TokAgree g g1 := ⟨e7, fun j hj => s21.2 j (by omega) (by omega)⟩
      have epos : P = bget g 3 + 2 + 2 * nm.length.toUInt64 := by
        rw [← hP, show (2 : UInt64) = 1 + 1 from rfl]; ac_rfl
      have R2 := rep_cursor R1' P (by rw [epos]; exact tokAt_frame et1 hn tr)
      have R3 : Rep (bset (bset g1 3 P) 31 (cw (st.binds[i]'hilt).sh).toUInt64) ts { st with toks := rest } fs :=
        rep_scratch R2 (fun j _ a => c3g j a) (drop_bset _ _ _ (by decide))
      have es3 : ShTabAgree g (bset (bset g1 3 P) 31 (cw (st.binds[i]'hilt).sh).toUInt64) :=
        fun j a b => by rw [c3g j (by omega)]; exact es2 j a b
      obtain ⟨st', hm, R4⟩ := rep_v5g R3 hnf 0 2 (st.binds[i]'hilt).slot (if (st.binds[i]'hilt).inp then 0 else cw (st.binds[i]'hilt).sh)
        (st.binds[i]'hilt).sh false wv (a2.frame es3) (by decide) (fun h2 => absurd rfl h2) (by decide) hs
      refine ⟨[], st', ?_, R4⟩
      obtain ⟨_, rfl⟩ := mkNode_inv hm
      simp only [stepF, et, hsome, locOf, if_neg hnt]
      simp
  · have ev : step h = v1 g 55 0 0 := by rw [E]; simp [v96, v120, c6, c5, c14]
    rw [ev] at hs ⊢
    have R2 := rep_push .argName 0 0 R1 rfl trivial hs
    refine ⟨[.argName], st, ?_, R2⟩
    simp only [stepF]
    split
    · rename_i r' heq
      exact absurd (UInt64.toNat_inj.mp (by rw [tok_cell_k r3 heq]; rfl)) c6
    · rename_i v r' heq
      exact absurd (tok_cell_num r3 heq) c5
    · rename_i x r' heq
      exact absurd (tok_cell_id r3 heq) c14
    · rfl

end ParInv
