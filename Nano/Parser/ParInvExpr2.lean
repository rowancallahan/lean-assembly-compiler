/- Nano/Parser/ParInvExpr2: Layer-3 handlers, token + push families of the expression core (box C):
`parenClose` (40, v105), `tupRest` (90, v204), `ifCmp` (6, v108), `ifThen` (7, v109). -/
import Nano.Parser.ParInvBuild
namespace ParInv
open C BufL ParSpec ParRun

/-- a keyword `T` at the cursor: the spec token, and the advanced cursor represents the rest -/
theorem cur_tok {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (T : UInt64) (hc : bget h (d11 + bget h 3) = T)
    (T0 : T ≠ 0) (T5 : T ≠ 5) (T14 : T ≠ 14) :
    ∃ rest, st.toks = .k T.toNat :: rest ∧ Rep (bset h 3 (bget h 3 + 1)) ts { st with toks := rest } fs := by
  obtain ⟨rest, et, tr⟩ := tok_kw r.2.2.2.1 r.1 r.2.1 hc T0 T5 T14
  exact ⟨rest, et, rep_set3 r tr⟩

theorem b01_toNat (b : Bool) : (b01 b).toNat = bm b := by cases b <;> rfl

theorem pushOK {h : Buf} {c a b : UInt64} (hs : bget (v1 h c a b) 0 ≠ 0) : bget h 0 ≠ 0 := fun z => hs (v1_zero _ _ _ _ z)

/-- the shape of v105 / v204: `)` closes, `,` opens the next tuple component -/
theorem paren_like {h ts : Buf} {st : St} {f : Frame} {fs : List Frame} (r : Rep h ts st (f :: fs)) (hf : f.isDefs = false)
    (ev : ∀ g a b, v96 g f.code.toUInt64 a b =
      if bget g (d11 + bget g 3) == 7 then bset g 3 (bget g 3 + 1) else
      if bget g (d11 + bget g 3) == 15 then v1 (v1 (v1 (bset g 3 (bget g 3 + 1)) 42 0 0) 90 0 0) 1 0 0 else bset g 0 0)
    (s7 : ∀ rest, st.toks = .k 7 :: rest → stepF f st = some ([], { st with toks := rest }))
    (s15 : ∀ rest, st.toks = .k 15 :: rest → stepF f st = some ([.expr 0 0, .tupRest, .mkPair], { st with toks := rest }))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF f st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r (by simp [inDefF, hf])
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  rw [E, ev] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  by_cases c7 : bget h1 (d11 + bget h1 3) = 7
  · simp only [c7, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, R2⟩ := cur_tok R1 7 c7 (by decide) (by decide) (by decide)
    exact ⟨[], _, s7 rest et, R2⟩
  · have n7 : (bget h1 (d11 + bget h1 3) == 7) = false := by simpa using c7
    simp only [n7, if_false] at hs ⊢
    by_cases c15 : bget h1 (d11 + bget h1 3) = 15
    · simp only [c15, beq_self_eq_true, if_true] at hs ⊢
      obtain ⟨rest, et, R2⟩ := cur_tok R1 15 c15 (by decide) (by decide) (by decide)
      have R3 := rep_push .mkPair 0 0 R2 (by simp [inDefF, Frame.isDefs]) trivial (pushOK (pushOK hs))
      have R4 := rep_push .tupRest 0 0 R3 (by simp [inDefF, Frame.isDefs]) trivial (pushOK hs)
      have R5 := rep_push (.expr 0 0) 0 0 R4 (by simp [inDefF, Frame.isDefs]) ⟨rfl, rfl⟩ hs
      exact ⟨_, _, s15 rest et, R5⟩
    · have n15 : (bget h1 (d11 + bget h1 3) == 15) = false := by simpa using c15
      simp only [n15, if_false] at hs; exact absurd (stat0 _ (by omega)) hs

theorem h_parenClose {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.parenClose :: fs)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF .parenClose st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) :=
  paren_like r rfl (fun g a b => by simp [Frame.code, v96, v105, k40]) (fun rest e => by simp [stepF, e])
    (fun rest e => by simp [stepF, e]) hs

theorem h_tupRest {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.tupRest :: fs)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF .tupRest st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) :=
  paren_like r rfl (fun g a b => by simp [Frame.code, v96, v204, k40]) (fun rest e => by simp [stepF, e])
    (fun rest e => by simp [stepF, e]) hs

/-! ## task 6: `ifCmp tl` (v108): `==` / `<`, then the condition's right operand (mode 2) -/
theorem h_ifCmp {h ts : Buf} {st : St} {tl : Bool} {fs : List Frame} (r : Rep h ts st (.ifCmp tl :: fs)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.ifCmp tl) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, eb, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [FrameArgs] at eb
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E eb
  subst eb
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  have ev : step h = (if bget h1 (d11 + bget h1 3) == 23 then
      v1 (v1 (bset h1 3 (bget h1 3 + 1)) 7 1 (b01 tl)) 1 0 2
    else if bget h1 (d11 + bget h1 3) == 20 then v1 (v1 (bset h1 3 (bget h1 3 + 1)) 7 2 (b01 tl)) 1 0 2 else bset h1 0 0) := by
    rw [E]; simp only [Frame.code, v96, v108, k1, k0, UInt64.add_zero]
    by_cases c23 : bget h1 (d11 + bget h1 3) = 23
    · simp [c23]
    · by_cases c20 : bget h1 (d11 + bget h1 3) = 20
      · simp [c20]
      · simp [c23, c20]
  rw [ev] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have fin : ∀ (c : Nat) (T : UInt64), bget h1 (d11 + bget h1 3) = T → T ≠ 0 → T ≠ 5 → T ≠ 14 →
      bget (v1 (v1 (bset h1 3 (bget h1 3 + 1)) 7 c.toUInt64 (b01 tl)) 1 0 2) 0 ≠ 0 → c < 2 ^ 64 →
      (∀ rest, st.toks = .k T.toNat :: rest → stepF (.ifCmp tl) st = some ([.expr 0 2, .ifThen c tl], { st with toks := rest })) →
      ∃ k st', stepF (.ifCmp tl) st = some (k, st') ∧
        Rep (v1 (v1 (bset h1 3 (bget h1 3 + 1)) 7 c.toUInt64 (b01 tl)) 1 0 2) ts st' (k ++ fs) := by
    intro c T hc T0 T5 T14 hs' hc64 hst
    obtain ⟨rest, et, R2⟩ := cur_tok R1 T hc T0 T5 T14
    have R3 := rep_push (.ifThen c tl) c.toUInt64 (b01 tl) R2 (by simp [inDefF, Frame.isDefs])
      ⟨by simp; omega, rfl⟩ (pushOK hs')
    have R4 := rep_push (.expr 0 2) 0 2 R3 (by simp [inDefF, Frame.isDefs]) ⟨rfl, rfl⟩ hs'
    exact ⟨_, _, hst rest et, R4⟩
  by_cases c23 : bget h1 (d11 + bget h1 3) = 23
  · simp only [c23, beq_self_eq_true, if_true] at hs ⊢
    exact fin 1 23 c23 (by decide) (by decide) (by decide) hs (by decide) (fun rest e => by simp [stepF, e])
  · have n23 : (bget h1 (d11 + bget h1 3) == 23) = false := by simpa using c23
    simp only [n23, if_false] at hs ⊢
    by_cases c20 : bget h1 (d11 + bget h1 3) = 20
    · simp only [c20, beq_self_eq_true, if_true] at hs ⊢
      exact fin 2 20 c20 (by decide) (by decide) (by decide) hs (by decide) (fun rest e => by simp [stepF, e])
    · have n20 : (bget h1 (d11 + bget h1 3) == 20) = false := by simpa using c20
      simp only [n20, if_false] at hs; exact absurd (stat0 _ (by omega)) hs

/-! ## task 7: `ifThen c tl` (v109): `then`, the branches in the inherited tail mode, `else`, the IF node -/
theorem h_ifThen {h ts : Buf} {st : St} {c : Nat} {tl : Bool} {fs : List Frame} (r : Rep h ts st (.ifThen c tl :: fs))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.ifThen c tl) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  subst eb
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  have ev : step h = (if bget h1 (d11 + bget h1 3) == 33 then
      v1 (v1 (v1 (v1 (bset h1 3 (bget h1 3 + 1)) 9 a 0) 1 0 (b01 tl)) 8 0 0) 1 0 (b01 tl) else bset h1 0 0) := by
    rw [E]; simp [Frame.code, v96, v109]
  rw [ev] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  by_cases c33 : bget h1 (d11 + bget h1 3) = 33
  · simp only [c33, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, R2⟩ := cur_tok R1 33 c33 (by decide) (by decide) (by decide)
    have R3 := rep_push (.mkIte c) a 0 R2 (by simp [inDefF, Frame.isDefs]) ea (pushOK (pushOK (pushOK hs)))
    have R4 := rep_push (.expr 0 (bm tl)) 0 (b01 tl) R3 (by simp [inDefF, Frame.isDefs]) ⟨rfl, b01_toNat tl⟩ (pushOK (pushOK hs))
    have R5 := rep_push .ifElse 0 0 R4 (by simp [inDefF, Frame.isDefs]) trivial (pushOK hs)
    have R6 := rep_push (.expr 0 (bm tl)) 0 (b01 tl) R5 (by simp [inDefF, Frame.isDefs]) ⟨rfl, b01_toNat tl⟩ hs
    exact ⟨[.expr 0 (bm tl), .ifElse, .expr 0 (bm tl), .mkIte c], _, by simp [stepF, et], R6⟩
  · have n33 : (bget h1 (d11 + bget h1 3) == 33) = false := by simpa using c33
    simp only [n33, if_false] at hs; exact absurd (stat0 _ (by omega)) hs

end ParInv
