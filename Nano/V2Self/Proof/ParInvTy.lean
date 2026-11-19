/- Nano/V2Self/Proof/ParInvTy: Layer-3 handlers, TYPES (box G).  Task 62 `tyCross` (v129): `×` pushes 63 (with the left shape code h[25]) above
61, any other token pops.  Generic: `rep_cursor` (move the token cursor), `tok_cell_k` (a keyword token's cell). -/
import Nano.V2Self.Proof.ParInvArg
namespace ParInv
open C BufL ParSpec ParRun

/-- the cell under the cursor of a keyword token -/
theorem tok_cell_k {h : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) {T : Nat} {rest : List Tok}
    (e : toks = .k T :: rest) : (bget h (d11 + p)).toNat = T := by
  cases r with
  | nil _ => cases e
  | kw t _ b _ _ _ _ => rw [b]; injection e with e1 _; injection e1
  | num _ _ _ _ _ _ _ => cases e
  | id _ _ _ => cases e

/-- **cursor move**: setting h[3] to a position that decodes `rest` -/
theorem rep_cursor {g ts : Buf} {st : St} {fs : List Frame} (R : Rep g ts st fs) (p' : UInt64) {rest : List Tok}
    (hK : TokAt g p' rest) : Rep (bset g 3 p') ts { st with toks := rest } fs := by
  obtain ⟨hn, hl, har⟩ := rep_bounds R
  have u3 : (3 : UInt64).toNat = 3 := rfl
  have cells : ∀ i : UInt64, i.toNat ≠ 3 → bget (bset g 3 p') i = bget g i := fun i a => bget_bset' _ _ _ _ (by rw [u3]; omega)
  have et' : TokAgree g (bset g 3 p') := ⟨cells 7 (by decide), fun i hi => cells i (by omega)⟩
  refine rep_tok R (by simp [length_bset]) (fun i _ b _ => cells i b) (drop_bset _ _ _ (by decide))
    (by rw [bget_bset_eq _ _ _ _ rfl (by rw [u3]; omega)]; exact tokAt_frame et' hn hK) ?_ rfl
  exact tasks_frame R.2.2.2.2.2.2.2.2.2.2.2.2.2 (cells 5 (by decide)) (fun i a b => cells i (by omega)) et' hn
    (fun i a _ => cells i (by omega)) (fun i a _ => cells i (by omega)) har

/-! ## task 62: `tyCross` (v129) -/
theorem h_tyCross {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.tyCross :: fs)) (hty : st.ty.isSome)
    (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF .tyCross st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rT := R1.1; have rts := R1.2.1; have r3 := R1.2.2.2.1; have r25 := R1.2.2.2.2.2.2.2.2.1
  have ev : step h = (if bget g (d11 + bget g 3) = 16 then v1 (v1 (bset g 3 (bget g 3 + 1)) 63 (bget g 25) 0) 61 0 0 else g) := by
    rw [E]; simp [v96, v129, k41]
  rw [ev] at hs ⊢
  by_cases hc : bget g (d11 + bget g 3) = 16
  · rw [if_pos hc] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts hc (by decide) (by decide) (by decide)
    obtain ⟨l, hl'⟩ := Option.isSome_iff_exists.mp hty
    have R2 := rep_cursor R1 (bget g 3 + 1) tr
    have sc : ShapeCode (bset g 3 (bget g 3 + 1)) (bget g 25) l :=
      (r25 l hl').frame (fun i a _ => bget_bset' _ _ _ _ (by simp; omega))
    have R3 := rep_push (.tyPair l) (bget g 25) 0 R2 rfl sc (fun z => hs (v1_zero _ _ _ _ z))
    have R4 := rep_push .tyAtom 0 0 R3 rfl trivial hs
    refine ⟨[.tyAtom, .tyPair l], { st with toks := rest }, ?_, R4⟩
    simp [stepF, et, hl']
  · rw [if_neg hc]
    refine ⟨[], st, ?_, R1⟩
    simp only [stepF]
    split
    · rename_i r' heq
      exact absurd (UInt64.toNat_inj.mp (by rw [tok_cell_k r3 heq]; rfl)) hc
    · rfl

/-- **type cell**: h[25] := a shape code -/
theorem rep_ty {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (w : UInt64) (s : Sh) (hw : ShapeCode h w s) :
    Rep (bset h 25 w) ts { st with ty := some s } fs := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have u25 : (25 : UInt64).toNat = 25 := rfl
  have e : ∀ i : UInt64, i.toNat ≠ 25 → bget (bset h 25 w) i = bget h i := fun i a => bget_bset' _ _ _ _ (by rw [u25]; omega)
  have et : TokAgree h (bset h 25 w) := ⟨e 7 (by decide), fun i hi => e i (by omega)⟩
  have es : ShTabAgree h (bset h 25 w) := fun i a _ => e i (by omega)
  exact ⟨tokensAt_frame rT et rts, rts, by rw [e 0 (by decide)]; exact r0,
    by rw [e 3 (by decide)]; exact tokAt_frame et hn r3, by rw [e 11 (by decide)]; exact r11,
    binds_frame rB (e 4 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    defs_frame rD (e 12 (by decide)) (e 27 (by decide)) (e 26 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    arena_frame rA (e 8 (by decide)) (e 9 (by decide)) (fun i a _ => e i (by omega)) es,
    fun s' hs' => by
      cases hs'
      rw [bget_bset_eq _ _ _ _ rfl (by rw [u25]; omega)]; exact hw.frame es,
    fun x hx => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [e 30 (by decide)]; exact r30, by rw [e 32 (by decide)]; exact r32, out_frame rO (drop_bset _ _ _ (by decide)),
    tasks_frame rK (e 5 (by decide)) (fun i _ _ => e i (by omega)) et hn es (fun i a _ => e i (by omega)) har⟩

/-- a leaf type: scratch write, cursor move, type cell, then task 62 -/
theorem ty_leaf {g ts : Buf} {st : St} {fs : List Frame} (R1 : Rep g ts st fs) (w : UInt64) (s : Sh) (hw : ShapeCode g w s)
    (z p' : UInt64) {rest : List Tok} (hK : TokAt g p' rest)
    (hs : bget (v1 (bset (bset (bset g 31 z) 3 p') 25 w) 62 0 0) 0 ≠ 0) :
    Rep (v1 (bset (bset (bset g 31 z) 3 p') 25 w) 62 0 0) ts { st with toks := rest, ty := some s } (.tyCross :: fs) := by
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have c31 : ∀ i : UInt64, i.toNat ≠ 31 → bget (bset g 31 z) i = bget g i := fun i a => bget_bset' _ _ _ _ (by simp; omega)
  have R2 : Rep (bset g 31 z) ts st fs := rep_scratch R1 (fun i _ a => c31 i a) (drop_bset _ _ _ (by decide))
  have hK' : TokAt (bset g 31 z) p' rest := tokAt_frame ⟨c31 7 (by decide), fun i hi => c31 i (by omega)⟩ hn hK
  have R3 := rep_cursor R2 p' hK'
  have hw' : ShapeCode (bset (bset g 31 z) 3 p') w s :=
    hw.frame (fun i a _ => by rw [bget_bset' _ _ _ _ (by simp; omega), c31 i (by omega)])
  have R4 := rep_ty R3 w s hw'
  exact rep_push .tyCross 0 0 R4 rfl trivial hs

/-! ## task 61: `tyAtom` (v128) -/
theorem h_tyAtom {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.tyAtom :: fs)) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF .tyAtom st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rT := R1.1; have rts := R1.2.1; have r3 := R1.2.2.2.1
  have p3 : (bget g 3).toNat < 2 ^ 40 := by have := r3.le; omega
  have hl31 : 31 < g.length := by omega
  have g3 : ∀ w, bget (bset g 31 w) 3 = bget g 3 := fun w => bget_bset' _ _ _ _ (by decide)
  have gn : ∀ w, bget (bset g 31 w) (d11 + bget g 3 + 1) = bget g (d11 + bget g 3 + 1) :=
    fun w => bget_bset' _ _ _ _ (by rw [d11a1 _ p3]; simp; omega)
  have dead : ∀ z, bget (bset (bset g 31 z) 0 0) 0 ≠ 0 → False := fun z x => x (stat0 _ (by simp [length_bset]; omega))
  by_cases c6 : bget g (d11 + bget g 3) = 6
  · have ev : step h = v1 (v1 (v1 (bset g 3 (bget g 3 + 1)) 62 0 0) 4 0 0) 61 0 0 := by rw [E]; simp [v96, v128, c6]
    rw [ev] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c6 (by decide) (by decide) (by decide)
    have R2 := rep_cursor R1 (bget g 3 + 1) tr
    have R3 := rep_push .tyCross 0 0 R2 rfl trivial (fun z => hs (v1_zero _ _ _ _ (v1_zero _ _ _ _ z)))
    have R4 := rep_push .rparen 0 0 R3 rfl trivial (fun z => hs (v1_zero _ _ _ _ z))
    have R5 := rep_push .tyAtom 0 0 R4 rfl trivial hs
    exact ⟨[.tyAtom, .rparen, .tyCross], { st with toks := rest }, by simp [stepF, et], R5⟩
  by_cases c3 : bget g (d11 + bget g 3) = 3
  · have ev : step h = v1 (bset (bset (bset g 31 1) 3 (bget g 3 + 1)) 25 1) 62 0 0 := by
      rw [E]; simp [v96, v128, v94, c3, bb31 g hl31, k1, g3]
    rw [ev] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c3 (by decide) (by decide) (by decide)
    exact ⟨[.tyCross], _, by simp [stepF, et], ty_leaf R1 1 .uw .uw 1 _ tr hs⟩
  by_cases c36 : bget g (d11 + bget g 3) = 36
  · have ev : step h = v1 (bset (bset (bset g 31 2) 3 (bget g 3 + 1)) 25 2) 62 0 0 := by
      rw [E]; simp [v96, v128, v94, c36, bb31 g hl31, k1, g3]
    rw [ev] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c36 (by decide) (by decide) (by decide)
    exact ⟨[.tyCross], _, by simp [stepF, et], ty_leaf R1 2 .bf .bf 2 _ tr hs⟩
  by_cases c35 : bget g (d11 + bget g 3) = 35
  · have ev : step h = v1 (bset (bset (bset g 31 4) 3 (bget g 3 + 1)) 25 4) 62 0 0 := by
      rw [E]; simp [v96, v128, v94, c35, bb31 g hl31, k1, g3]
    rw [ev] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c35 (by decide) (by decide) (by decide)
    exact ⟨[.tyCross], _, by simp [stepF, et], ty_leaf R1 4 .nt .nt 4 _ tr hs⟩
  by_cases c37 : bget g (d11 + bget g 3) = 37
  · have ev : step h = (if bget g (d11 + bget g 3 + 1) = 38 then v1 (bset (bset (bset g 31 3) 3 (bget g 3 + 1 + 1)) 25 3) 62 0 0
        else bset (bset g 31 3) 0 0) := by
      rw [E]; simp [v96, v128, v94, c37, bb31 g hl31, k1, g3, gn]
    rw [ev] at hs ⊢
    by_cases c38 : bget g (d11 + bget g 3 + 1) = 38
    · rw [if_pos c38] at hs ⊢
      obtain ⟨rest1, et1, tr1⟩ := tok_kw r3 rT rts c37 (by decide) (by decide) (by decide)
      obtain ⟨rest, et, tr⟩ := tok_kw (t := 38) tr1 rT rts (by rw [← UInt64.add_assoc]; exact c38) (by decide) (by decide) (by decide)
      subst et
      exact ⟨[.tyCross], _, by simp [stepF, et1], ty_leaf R1 3 .ls .ls 3 _ tr hs⟩
    · rw [if_neg c38] at hs; exact (dead _ hs).elim
  · have ev : step h = bset (bset g 31 0) 0 0 := by
      rw [E]; simp [v96, v128, v94, c6, c3, c36, c35, c37, bb31 g hl31]
    rw [ev] at hs; exact (dead _ hs).elim

end ParInv
