/- Nano/V2Self/Proof/ParInvBind: Layer-3 handlers, BINDERS (box G).  Task 66 `binders` (v131): `(` opens a binder group (task 67 with the
current binding count), `:` starts the result type (61 above 70). -/
import Nano.V2Self.Proof.ParInvTy
namespace ParInv
open C BufL ParSpec ParRun

/-! ## task 66: `binders` (v131) -/
theorem h_binders {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.binders :: fs)) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF .binders st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rT := R1.1; have rts := R1.2.1; have r3 := R1.2.2.2.1
  have rB4 : (bget g 4).toNat = st.binds.length := R1.2.2.2.2.2.1.1
  have g4 : ∀ v, bget (bset g 3 v) 4 = bget g 4 := fun v => bget_bset' _ _ _ _ (by decide)
  by_cases c6 : bget g (d11 + bget g 3) = 6
  · have ev : step h = v1 (bset g 3 (bget g 3 + 1)) 67 (bget g 4) 0 := by rw [E]; simp [v96, v131, c6, g4]
    rw [ev] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c6 (by decide) (by decide) (by decide)
    have R2 := rep_cursor R1 (bget g 3 + 1) tr
    have R3 := rep_push (.group st.binds.length) (bget g 4) 0 R2 rfl rB4 hs
    exact ⟨[.group st.binds.length], { st with toks := rest }, by simp [stepF, et], R3⟩
  by_cases c8 : bget g (d11 + bget g 3) = 8
  · have ev : step h = v1 (v1 (bset g 3 (bget g 3 + 1)) 70 0 0) 61 0 0 := by rw [E]; simp [v96, v131, c8]
    rw [ev] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c8 (by decide) (by decide) (by decide)
    have R2 := rep_cursor R1 (bget g 3 + 1) tr
    have R3 := rep_push .plainBody 0 0 R2 rfl trivial (fun z => hs (v1_zero _ _ _ _ z))
    have R4 := rep_push .tyAtom 0 0 R3 rfl trivial hs
    exact ⟨[.tyAtom, .plainBody], { st with toks := rest }, by simp [stepF, et], R4⟩
  · have ev : step h = bset g 0 0 := by rw [E]; simp [v96, v131, c6, c8]
    rw [ev] at hs; exact absurd (stat0 _ (by omega)) hs

end ParInv
