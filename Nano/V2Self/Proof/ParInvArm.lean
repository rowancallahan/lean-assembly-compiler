/- Nano/V2Self/Proof/ParInvArm: Layer-3 handlers for the fuel-loop ARMS (box G, taken over from the parser lead):
task 79 `mkLoop` (v140): the step arm's shape code equals the def's result code, then the LOOP node (tag 10, two children). -/
import Nano.V2Self.Proof.ParInvPair
namespace ParInv
open C BufL ParSpec ParRun

/-- one code, one optional shape -/
theorem ShOpt.same {h : Buf} {c : UInt64} {o o' : Option Sh} (r : ShOpt h c o) (r' : ShOpt h c o') : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some s' => simp only [ShOpt] at r r'; subst r; exact absurd rfl r'.ne0
  | some s =>
    cases o' with
    | none => simp only [ShOpt] at r r'; subst r'; exact absurd rfl r.ne0
    | some s' => exact congrArg some (ShapeCode.det r r')

/-! ## task 79: `mkLoop` (v140) -/
theorem h_mkLoop {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.mkLoop :: fs)) (hD : inDefF fs = true)
    (hnf : fs.all (fun f => !f.isFlat)) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF .mkLoop st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have ev : step h = (if bget g (d5 + 8 * bget g (d3 + bget g 8 - 1) + 3) = bget g (d7 + 8 * bget g 12 + 3) then
      v5 g (10 : Nat).toUInt64 (0 : Nat).toUInt64 (0 : Nat).toUInt64 (bget g (d7 + 8 * bget g 12 + 3)) (b01 false) (2 : Nat).toUInt64
      else bset g 0 0) := by rw [E]; simp [v96, v140, b01]
  rw [ev] at hs ⊢
  by_cases c1 : bget g (d5 + 8 * bget g (d3 + bget g 8 - 1) + 3) = bget g (d7 + 8 * bget g 12 + 3)
  · rw [if_pos c1] at hs ⊢
    have rA := R1.2.2.2.2.2.2.2.1
    have rD : DefsRep g st true := hD ▸ R1.2.2.2.2.2.2.1
    have h12 : bget g 12 = st.defs.length.toUInt64 := by rw [← rD.1]; simp
    have hres : ShOpt g (bget g (d7 + 8 * bget g 12 + 3)) st.cur.res := by
      rw [h12]; have := rD.2.2.2.2.1; simp only [if_true] at this; exact this.1.2.2.2.1
    obtain ⟨st', em, R2⟩ := rep_v5 R1 hnf 2 10 0 0 st.cur.res false _ hres (by decide) (by decide) (by decide) (by decide) hs
    obtain ⟨hle, _⟩ := mkNode_inv em
    obtain ⟨s, rest, ev2⟩ : ∃ s rest, st.vals = s :: rest := by
      match hv : st.vals with
      | s :: rest => exact ⟨s, rest, rfl⟩
      | [] => simp [hv] at hle
    have l0 : 0 < st.vals.length := by rw [ev2]; simp
    have o0 := opCell rA.2.2.1 rA.2.2.2.1 0 l0
    simp only [show ((0 : Nat) + 1).toUInt64 = 1 from rfl] at o0
    obtain ⟨_, rs⟩ := val_rep rA 0 l0
    have fs' : ShOpt g (bget g (d5 + 8 * opAt g (st.vals.length - 1 - 0) + 3)) (st.vals[0]'l0).sh := rs.fields.2.2.2.1
    rw [← o0, c1] at fs'
    have hsh := ShOpt.same fs' hres
    simp only [ev2, List.getElem_cons_zero] at hsh
    exact ⟨[], st', by simp [stepF, ev2, hsh, em], R2⟩
  · rw [if_neg c1] at hs; exact absurd (stat0 _ (by omega)) hs

end ParInv
