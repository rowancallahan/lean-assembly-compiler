/- Nano/V2Self/Proof/ParInvLet: Layer-3 handlers of the `let` family (box C): `letStart` (41, v112), `letPairX` (50, v113),
`letPairY` (51, v114), `stash` (52, v115). -/
import Nano.V2Self.Proof.ParInvExpr2
import Nano.V2Self.Proof.ParInvDefs
namespace ParInv
open C BufL ParSpec ParRun

theorem TokAt.id_inv {h : Buf} {p : UInt64} {x : List Nat} {rest : List Tok} (r : TokAt h p (.id x :: rest)) :
    ∃ nm, NameOK h p nm ∧ nm.map UInt64.toNat = x ∧ TokAt h (p + 2 + 2 * nm.length.toUInt64) rest := by
  cases r with
  | id nm a tr => exact ⟨nm, a, rfl, tr⟩

/-- an identifier at the cursor: its spelling, and `v86` moves the cursor past it (represents the rest) -/
theorem cur_id {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (hc : bget h (d11 + bget h 3) = 14) :
    ∃ x rest q, st.toks = .id x :: rest ∧ NameAt h (bget h 3) x ∧ v86 16777216 h (bget h 3 + 1) = bset h 3 q ∧
      Rep (bset h 3 q) ts { st with toks := rest } fs := by
  rcases tok_cases r.2.2.2.1 r.1 with ⟨_, h0⟩ | ⟨_, _, _, h5⟩ | ⟨x, rest, et, _⟩ | ⟨t, _, _, ht, _, _, t14, _⟩
  · rw [hc] at h0; exact absurd h0 (by decide)
  · rw [hc] at h5; exact absurd h5 (by decide)
  · have p3 := r.2.2.2.1
    rw [et] at p3
    obtain ⟨nm, a, ex, tr⟩ := p3.id_inv
    have hn7 := (rep_bounds r).1
    have b1 := a.2.2
    have h7' : (bget h 7).toNat < 2 ^ 24 := by rw [r.1.2.2.2]; have := r.2.1; simp; omega
    have p1 : (bget h 3 + 1).toNat = (bget h 3).toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have sk := v86_skip nm 16777216 h (bget h 3 + 1) a.2.1 (by have := p1; omega) (by omega)
    refine ⟨x, rest, _, et, ⟨nm, a, ex⟩, sk, ?_⟩
    have eq : bget h 3 + 1 + 2 * nm.length.toUInt64 + 1 = bget h 3 + 2 + 2 * nm.length.toUInt64 := by
      apply UInt64.toNat_inj.mp
      have l2 : (2 * nm.length.toUInt64).toNat = 2 * nm.length := by rw [UInt64.toNat_mul]; simp; omega
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, l2]; simp; omega
    rw [eq]; exact rep_set3 r tr
  · rw [hc] at ht; exact absurd ht.symm t14

theorem nameAt_rep {h h' ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (e : TokAgree h h') {pos : UInt64} {x : List Nat}
    (n : NameAt h pos x) : NameAt h' pos x :=
  nameAt_frame e (by have := (rep_bounds r).1; omega) n

theorem tokAgree_set3 (h : Buf) (q : UInt64) : TokAgree h (bset h 3 q) :=
  ⟨bget_bset' _ _ _ _ (by decide), fun i hi => bget_bset' _ _ _ _ (by rw [show (3 : UInt64).toNat = 3 from rfl]; omega)⟩

/-! ## task 41: `letStart tl` (v112): `x :=` or `(` -/
theorem h_letStart {h ts : Buf} {st : St} {tl : Bool} {fs : List Frame} (r : Rep h ts st (.letStart tl :: fs))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.letStart tl) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, eb, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [FrameArgs] at eb
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E eb
  subst eb
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  rw [E] at hs ⊢
  simp only [Frame.code, v96, v112, UInt64.add_zero] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  by_cases c14 : bget h1 (d11 + bget h1 3) = 14
  · simp only [c14, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨x, r0, q, et, nx, sk, R2⟩ := cur_id R1 c14
    rw [sk] at hs ⊢
    generalize hH2 : bset h1 3 q = H2 at hs R2 ⊢
    have hn2 := (rep_bounds R2)
    by_cases c9 : bget H2 (d11 + bget H2 3) = 9
    · simp only [c9, beq_self_eq_true, if_true] at hs ⊢
      obtain ⟨r1, et2, R3⟩ := cur_tok R2 9 c9 (by decide) (by decide) (by decide)
      have ta : TokAgree h1 (bset H2 3 (bget H2 3 + 1)) := by
        rw [← hH2]; exact ⟨by rw [(tokAgree_set3 _ _).1, (tokAgree_set3 _ _).1],
          fun i hi => by rw [(tokAgree_set3 _ _).2 i hi, (tokAgree_set3 _ _).2 i hi]⟩
      have R4 := rep_push (.letSemi x tl) (bget h1 3) (b01 tl) R3 (by simp [inDefF, Frame.isDefs])
        ⟨nameAt_rep R1 ta nx, rfl⟩ (pushOK hs)
      have R5 := rep_push (.expr 0 0) 0 0 R4 (by simp [inDefF, Frame.isDefs]) ⟨rfl, rfl⟩ hs
      refine ⟨[.expr 0 0, .letSemi x tl], _, ?_, R5⟩
      have et2' : r0 = .k 9 :: r1 := et2
      simp [stepF, et, et2']
    · have n9 : (bget H2 (d11 + bget H2 3) == 9) = false := by simpa using c9
      simp only [n9, if_false] at hs; exact absurd (stat0 _ (by omega)) hs
  · have n14 : (bget h1 (d11 + bget h1 3) == 14) = false := by simpa using c14
    simp only [n14, if_false] at hs ⊢
    by_cases c6 : bget h1 (d11 + bget h1 3) = 6
    · simp only [c6, beq_self_eq_true, if_true] at hs ⊢
      obtain ⟨r1, et, R2⟩ := cur_tok R1 6 c6 (by decide) (by decide) (by decide)
      have R3 := rep_push (.letPairX tl) 0 (b01 tl) R2 (by simp [inDefF, Frame.isDefs]) rfl hs
      exact ⟨[.letPairX tl], _, by simp [stepF, et], R3⟩
    · have n6 : (bget h1 (d11 + bget h1 3) == 6) = false := by simpa using c6
      simp only [n6, if_false] at hs; exact absurd (stat0 _ (by omega)) hs

end ParInv
