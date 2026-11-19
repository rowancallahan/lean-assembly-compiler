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

end ParInv
