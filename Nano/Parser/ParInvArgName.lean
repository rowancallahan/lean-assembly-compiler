/- Nano/Parser/ParInvArgName: Layer-3 handler for task 55 `argName` (v126), box G: a constant def (lookup, zero parameters,
CALL node with no children), `[]` (BNEW as a List) or `bnew`. -/
import Nano.Parser.ParInvName
namespace ParInv
open C BufL ParSpec ParRun

theorem mkNode_leaf (st : St) (t a b : Nat) (s : Sh) : mkNode st t a b (some s) false 0 = some (leaf st t a b s) := by
  simp [mkNode, leaf]

theorem v0_ne (t : UInt64) (h : t ≠ 43) : (if 38 < t then if t < 48 then t - 38 else 0 else 0 : UInt64) ≠ 5 := by
  split
  · split
    · rename_i h1 _
      intro e; apply h
      apply UInt64.toNat_inj.mp
      have := congrArg UInt64.toNat e
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp h1)))] at this
      have h1' := UInt64.lt_iff_toNat_lt.mp h1
      simp at this h1' ⊢; omega
    · decide
  · decide

theorem h_argName {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.argName :: fs))
    (hnf : fs.all (fun f => !f.isFlat)) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF .argName st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rT := R1.1; have rts := R1.2.1; have r3 := R1.2.2.2.1
  have p3 : (bget g 3).toNat < 2 ^ 40 := by have := r3.le; omega
  have hl31 : 31 < g.length := by omega
  by_cases c30 : bget g (d11 + bget g 3) = 30
  · have ev : step h = (if bget g (d11 + bget g 3 + 1) = 31 then
        v5 (bset g 3 (bget g 3 + 2)) (9 : Nat).toUInt64 (5 : Nat).toUInt64 (0 : Nat).toUInt64 3 (b01 false) (0 : Nat).toUInt64
        else bset g 0 0) := by rw [E]; simp [v96, v126, c30, b01]
    rw [ev] at hs ⊢
    by_cases c31 : bget g (d11 + bget g 3 + 1) = 31
    · rw [if_pos c31] at hs ⊢
      obtain ⟨rest1, et1, tr1⟩ := tok_kw r3 rT rts c30 (by decide) (by decide) (by decide)
      obtain ⟨rest, et, tr⟩ := tok_kw (t := 31) tr1 rT rts (by rw [← UInt64.add_assoc]; exact c31) (by decide) (by decide) (by decide)
      subst et
      have tr' : TokAt g (bget g 3 + 2) rest := by rw [show bget g 3 + 2 = bget g 3 + 1 + 1 by rw [UInt64.add_assoc]; rfl]; exact tr
      have R2 := rep_cursor R1 (bget g 3 + 2) tr'
      obtain ⟨st', hm, R3⟩ := rep_v5 R2 hnf 0 9 5 0 (some .ls) false 3 ShapeCode.ls (by decide) (by decide) (by decide) (by decide) hs
      rw [mkNode_leaf] at hm; cases hm
      exact ⟨[], _, by simp [stepF, et1], R3⟩
    · rw [if_neg c31] at hs; exact absurd (stat0 _ (by omega)) hs
  by_cases c14 : bget g (d11 + bget g 3) = 14
  · obtain ⟨nm, rest, et, hNm, tr⟩ := tok_id r3 rT c14
    have h7 : (bget g 7).toNat < 2 ^ 24 := by rw [rT.2.2.2]; simp; omega
    have rD := R1.2.2.2.2.2.2.1
    obtain ⟨s22, _⟩ := v8_findD rD (by omega) hl31 hNm
    have hval := v8_val rD (by omega) hl31 hNm
    have hdrop := v8_drop g (bget g 12) (bget g 3)
    have ev : step h = (if bget (v8 g (bget g 12) (bget g 3)) 22 = 0 then bset (v8 g (bget g 12) (bget g 3)) 0 0
        else if bget (v8 g (bget g 12) (bget g 3)) (d7 + 8 * (bget (v8 g (bget g 12) (bget g 3)) 22 - 1) + 6) = 0 then
          v5 (v86 16777216 (v8 g (bget g 12) (bget g 3)) (bget g 3 + 1)) (8 : Nat).toUInt64
            (bget (v8 g (bget g 12) (bget g 3)) 22 - 1) (0 : Nat).toUInt64
            (bget (v8 g (bget g 12) (bget g 3)) (d7 + 8 * (bget (v8 g (bget g 12) (bget g 3)) 22 - 1) + 3))
            (b01 false) (0 : Nat).toUInt64
        else bset (v8 g (bget g 12) (bget g 3)) 0 0) := by rw [E]; simp [v96, v126, c14, b01]
    generalize v8 g (bget g 12) (bget g 3) = g1 at ev s22 hval hdrop
    rw [ev] at hs ⊢
    have dead : bget (bset g1 0 0) 0 ≠ 0 → False := fun x => x (stat0 _ (by rw [s22.1]; omega))
    cases hf : findD st.defs (nm.map UInt64.toNat) with
    | none =>
      rw [hf] at hval
      rw [if_pos (by simpa using hval)] at hs
      exact (dead hs).elim
    | some j =>
      rw [hf] at hval
      simp only [Option.map_some, Option.getD_some] at hval
      have jlt := findD_lt hf
      have j512 : j < 512 := by have := rD.2.1; omega
      have hne : bget g1 22 ≠ 0 := by
        rw [hval]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
      have hj1 : bget g1 22 - 1 = j.toUInt64 := by
        rw [hval]; apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
      rw [if_neg hne, hj1] at hs ⊢
      obtain ⟨_, _, _, rres, _, rcnt, _, _⟩ := (rD.2.2.2.1 j jlt).1
      have c6 := defCell j j512 6 (by decide)
      have c3 := defCell j j512 3 (by decide)
      have e6 : bget g1 (d7 + 8 * j.toUInt64 + 6) = bget g (d7 + 8 * j.toUInt64 + 6) :=
        s22.2 _ (by rw [c6]; simp; omega) (by rw [c6]; simp; omega)
      have e3 : bget g1 (d7 + 8 * j.toUInt64 + 3) = bget g (d7 + 8 * j.toUInt64 + 3) :=
        s22.2 _ (by rw [c3]; simp; omega) (by rw [c3]; simp; omega)
      rw [e6, e3] at hs ⊢
      by_cases hp0 : bget g (d7 + 8 * j.toUInt64 + 6) = 0
      · rw [if_pos hp0] at hs ⊢
        have hpl : (st.defs[j]'jlt).params.length = 0 := by rw [← rcnt, hp0]; rfl
        have e7 : bget g1 7 = bget g 7 := s22.2 7 (by decide) (by decide)
        have hseq : NameSeq g1 (bget g 3 + 1) nm :=
          nameSeq_same s22 (by decide) nm _ (by have := hNm.2.2; rw [tn_add _ _ (by simp; omega)]; simp; omega) hNm.2.1
        have hskip := v86_skip nm 16777216 g1 (bget g 3 + 1) hseq
          (by rw [e7, tn_add _ _ (by simp; omega)]; have := hNm.2.2; simp; omega) (by have := hNm.2.2; omega)
        rw [hskip] at hs ⊢
        have R1' : Rep g1 ts st fs := rep_same R1 s22 (Or.inr rfl) hdrop
        have et1 : TokAgree g g1 := ⟨e7, fun i hi => s22.2 i (by omega) (by omega)⟩
        have epos : bget g 3 + 1 + 2 * nm.length.toUInt64 + 1 = bget g 3 + 2 + 2 * nm.length.toUInt64 := by
          rw [show (2 : UInt64) = 1 + 1 from rfl]; ac_rfl
        have tr' : TokAt g1 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1) rest := by
          rw [epos]; exact tokAt_frame et1 hn tr
        have R2 := rep_cursor R1' _ tr'
        have es : ShTabAgree g (bset g1 3 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1)) :=
          fun i a _ => by rw [bget_bset' _ _ _ _ (by simp; omega), s22.2 i (by omega) (by omega)]
        obtain ⟨st', hm, R3⟩ := rep_v5 R2 hnf 0 8 j 0 (st.defs[j]'jlt).res false _ (rres.frame es) (by decide) (by omega)
          (by decide) (by decide) hs
        refine ⟨[], st', ?_, R3⟩
        simp only [stepF, et, hf, List.getElem?_eq_getElem jlt, hpl, if_true]
        rw [hm]; rfl
      · rw [if_neg hp0] at hs; exact (dead hs).elim
  by_cases c43 : bget g (d11 + bget g 3) = 43
  · have ev : step h = v5 (bset (bset g 31 5) 3 (bget g 3 + 1)) (9 : Nat).toUInt64 (5 : Nat).toUInt64 (0 : Nat).toUInt64 2 (b01 false)
        (0 : Nat).toUInt64 := by rw [E]; simp [v96, v126, v0, c43, b01, bb31 g hl31]
    rw [ev] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c43 (by decide) (by decide) (by decide)
    have c31 : ∀ i : UInt64, i.toNat ≠ 31 → bget (bset g 31 5) i = bget g i := fun i a => bget_bset' _ _ _ _ (by simp; omega)
    have R2 : Rep (bset g 31 5) ts st fs := rep_scratch R1 (fun i _ a => c31 i a) (drop_bset _ _ _ (by decide))
    have tr' : TokAt (bset g 31 5) (bget g 3 + 1) rest := tokAt_frame ⟨c31 7 (by decide), fun i hi => c31 i (by omega)⟩ hn tr
    have R3 := rep_cursor R2 (bget g 3 + 1) tr'
    obtain ⟨st', hm, R4⟩ := rep_v5 R3 hnf 0 9 5 0 (some .bf) false 2 ShapeCode.bf (by decide) (by decide) (by decide) (by decide) hs
    rw [mkNode_leaf] at hm; cases hm
    exact ⟨[], _, by simp [stepF, et], R4⟩
  · have hz := v0_ne _ c43
    have ev : step h = bset (bset g 31 (if 38 < bget g (d11 + bget g 3) then if bget g (d11 + bget g 3) < 48 then
        bget g (d11 + bget g 3) - 38 else 0 else 0)) 0 0 := by
      rw [E]; simp [v96, v126, v0, c30, c14, bb31 g hl31, hz]
    rw [ev] at hs; exact absurd (stat0 _ (by simp [length_bset]; omega)) hs

end ParInv
