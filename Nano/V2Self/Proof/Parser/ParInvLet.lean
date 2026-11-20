/- Nano/V2Self/Proof/Parser/ParInvLet: Layer-3 handlers of the `let` family (box C): `letStart` (41, v112), `letPairX` (50, v113),
`letPairY` (51, v114), `stash` (52, v115). -/
import Nano.V2Self.Proof.Parser.ParInvExpr2
import Nano.V2Self.Proof.Parser.ParInvDefs
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
  have ev : step h = v112 h1 a (b01 tl) := by rw [E]; simp [Frame.code, v96]
  rw [ev] at hs ⊢
  simp only [v112, UInt64.add_zero] at hs ⊢
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

/-- token-region names depend only on the token words -/
theorem nameSeq_ts {h h' ts : Buf} (a1 : TokensAt h ts) (a2 : TokensAt h' ts) (hts : ts.length < 2 ^ 24) :
    ∀ (l : List UInt64) (a : UInt64), a.toNat + 2 * l.length < ts.length → NameSeq h a l → NameSeq h' a l
  | [], a, ha, x => by
    simp only [NameSeq] at x ⊢
    have e1 := a1.1 a.toNat (by omega); have e2 := a2.1 a.toNat (by omega)
    simp only [UInt64.ofNat_toNat] at e1 e2
    rw [e2, ← e1]; exact x
  | c :: t, a, ha, x => by
    simp only [NameSeq] at x ⊢
    obtain ⟨x1, x2, x3⟩ := x
    simp at ha
    have a2' : (a + 2).toNat = a.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
    have a1' : (a + 1).toNat = a.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have e1 := a1.1 a.toNat (by omega); have e2 := a2.1 a.toNat (by omega)
    have f1 := a1.1 (a.toNat + 1) (by omega); have f2 := a2.1 (a.toNat + 1) (by omega)
    simp only [UInt64.ofNat_toNat] at e1 e2
    have g : ∀ g : Buf, bget g (d11 + a + 1) = bget g (d11 + (a.toNat + 1).toUInt64) := by
      intro g; congr 1; apply UInt64.toNat_inj.mp; rw [d11a1 _ (by omega), d11a _ (by simp; omega)]; simp; omega
    refine ⟨by rw [e2, ← e1]; exact x1, by rw [g, f2, ← f1, ← g]; exact x2, nameSeq_ts a1 a2 hts t (a + 2) (by rw [a2']; omega) x3⟩

theorem nameAt_ts {h h' ts : Buf} (a1 : TokensAt h ts) (a2 : TokensAt h' ts) (hts : ts.length < 2 ^ 24) {pos : UInt64} {x : List Nat}
    (n : NameAt h pos x) : NameAt h' pos x := by
  obtain ⟨nm, ⟨n1, n2, n3⟩, n4⟩ := n
  have h7 : (bget h 7).toNat = ts.length := by rw [a1.2.2.2]; simp; omega
  have h7' : bget h' 7 = bget h 7 := by rw [a1.2.2.2, a2.2.2.2]
  have p1 : (pos + 1).toNat = pos.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨nm, ⟨?_, nameSeq_ts a1 a2 hts nm (pos + 1) (by rw [p1]; omega) n2, by rw [h7']; exact n3⟩, n4⟩
  have e1 := a1.1 pos.toNat (by omega); have e2 := a2.1 pos.toNat (by omega)
  simp only [UInt64.ofNat_toNat] at e1 e2
  rw [e2, ← e1]; exact n1

/-- the cursor moved twice (v86 skip, then one keyword) keeps the token region -/
theorem tokAgree_set33 (h : Buf) (q q' : UInt64) : TokAgree h (bset (bset h 3 q) 3 q') :=
  ⟨by rw [(tokAgree_set3 _ _).1, (tokAgree_set3 _ _).1], fun i hi => by rw [(tokAgree_set3 _ _).2 i hi, (tokAgree_set3 _ _).2 i hi]⟩

/-! ## task 50: `letPairX tl` (v113): `x ,` -/
theorem h_letPairX {h ts : Buf} {st : St} {tl : Bool} {fs : List Frame} (r : Rep h ts st (.letPairX tl :: fs))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.letPairX tl) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, eb, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [FrameArgs] at eb
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E eb
  subst eb
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  have ev : step h = v113 h1 a (b01 tl) := by rw [E]; simp [Frame.code, v96]
  rw [ev] at hs ⊢
  simp only [v113, UInt64.add_zero, k40] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  by_cases c14 : bget h1 (d11 + bget h1 3) = 14
  · simp only [c14, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨x, r0, q, et, nx, sk, R2⟩ := cur_id R1 c14
    rw [sk] at hs ⊢
    generalize hH2 : bset h1 3 q = H2 at hs R2 ⊢
    have hn2 := rep_bounds R2
    by_cases c15 : bget H2 (d11 + bget H2 3) = 15
    · simp only [c15, beq_self_eq_true, if_true] at hs ⊢
      obtain ⟨r1, et2, R3⟩ := cur_tok R2 15 c15 (by decide) (by decide) (by decide)
      have ta : TokAgree h1 (bset H2 3 (bget H2 3 + 1)) := by rw [← hH2]; exact tokAgree_set33 _ _ _
      have R4 := rep_push (.letPairY x tl) (bget h1 3) (b01 tl) R3 (by simp [inDefF, Frame.isDefs])
        ⟨nameAt_rep R1 ta nx, rfl⟩ hs
      refine ⟨[.letPairY x tl], _, ?_, R4⟩
      have et2' : r0 = .k 15 :: r1 := et2
      simp [stepF, et, et2']
    · have n : (bget H2 (d11 + bget H2 3) == 15) = false := by simpa using c15
      simp only [n, if_false] at hs; exact absurd (stat0 _ (by omega)) hs
  · have n : (bget h1 (d11 + bget h1 3) == 14) = false := by simpa using c14
    simp only [n, if_false] at hs; exact absurd (stat0 _ (by omega)) hs

/-! ## task 51: `letPairY x tl` (v114): `y ) :=`, then the value, the stash of x, the binder -/
theorem h_letPairY {h ts : Buf} {st : St} {x : List Nat} {tl : Bool} {fs : List Frame} (r : Rep h ts st (.letPairY x tl :: fs))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.letPairY x tl) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  subst eb
  have ea1 : NameAt (bset h 5 fs.length.toUInt64) a x :=
    nameAt_frame ⟨bget_bset' _ _ _ _ (by decide), fun i hi => bget_bset' _ _ _ _ (by rw [show (5 : UInt64).toNat = 5 from rfl]; omega)⟩
      (by have := (rep_bounds r).1; omega) ea
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1 ea1
  have ev : step h = v114 h1 a (b01 tl) := by rw [E]; simp [Frame.code, v96]
  rw [ev] at hs ⊢
  simp only [v114, UInt64.add_zero] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  by_cases c14 : bget h1 (d11 + bget h1 3) = 14
  · simp only [c14, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨y, r0, q, et, ny, sk, R2⟩ := cur_id R1 c14
    rw [sk] at hs ⊢
    generalize hH2 : bset h1 3 q = H2 at hs R2 ⊢
    have hn2 := rep_bounds R2
    by_cases c7 : bget H2 (d11 + bget H2 3) = 7
    · simp only [c7, beq_self_eq_true, if_true] at hs ⊢
      obtain ⟨r1, et2, R3⟩ := cur_tok R2 7 c7 (by decide) (by decide) (by decide)
      generalize hH3 : bset H2 3 (bget H2 3 + 1) = H3 at hs R3 ⊢
      have hn3 := rep_bounds R3
      by_cases c9 : bget H3 (d11 + bget H3 3) = 9
      · simp only [c9, beq_self_eq_true, if_true] at hs ⊢
        obtain ⟨r2, et3, R4⟩ := cur_tok R3 9 c9 (by decide) (by decide) (by decide)
        have ta : TokAgree h1 (bset H3 3 (bget H3 3 + 1)) := by
          rw [← hH3, ← hH2]
          exact ⟨by rw [(tokAgree_set3 _ _).1, (tokAgree_set3 _ _).1, (tokAgree_set3 _ _).1],
            fun i hi => by rw [(tokAgree_set3 _ _).2 i hi, (tokAgree_set3 _ _).2 i hi, (tokAgree_set3 _ _).2 i hi]⟩
        have R5 := rep_push (.letPairSemi y tl) (bget h1 3) (b01 tl) R4 (by simp [inDefF, Frame.isDefs])
          ⟨nameAt_rep R1 ta ny, rfl⟩ (pushOK (pushOK hs))
        have R6 := rep_push (.stash x) a (b01 tl) R5 (by simp [inDefF, Frame.isDefs]) (nameAt_ts R1.1 R5.1 R1.2.1 ea1) (pushOK hs)
        have R7 := rep_push (.expr 0 0) 0 0 R6 (by simp [inDefF, Frame.isDefs]) ⟨rfl, rfl⟩ hs
        refine ⟨[.expr 0 0, .stash x, .letPairSemi y tl], _, ?_, R7⟩
        have et2' : r0 = .k 7 :: r1 := et2
        have et3' : r1 = .k 9 :: r2 := et3
        simp [stepF, et, et2', et3']
      · have n : (bget H3 (d11 + bget H3 3) == 9) = false := by simpa using c9
        simp only [n, if_false] at hs; exact absurd (stat0 _ (by omega)) hs
    · have n : (bget H2 (d11 + bget H2 3) == 7) = false := by simpa using c7
      simp only [n, if_false] at hs; exact absurd (stat0 _ (by omega)) hs
  · have n : (bget h1 (d11 + bget h1 3) == 14) = false := by simpa using c14
    simp only [n, if_false] at hs; exact absurd (stat0 _ (by omega)) hs

/-! ## task 52: `stash x` (v115): h[29] := the position of x -/
theorem rep_set29 {h ts : Buf} {st : St} {fs : List Frame} {pos : UInt64} {x : List Nat} (r : Rep h ts st fs) (hx : NameAt h pos x) :
    Rep (bset h 29 pos) ts { st with stash := some x } fs := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, _, r30, r32, rO, rK⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have u : (29 : UInt64).toNat = 29 := rfl
  have c : ∀ i : UInt64, i.toNat ≠ 29 → bget (bset h 29 pos) i = bget h i := fun i hi => bget_bset' _ _ _ _ (by rw [u]; omega)
  have et : TokAgree h (bset h 29 pos) := ⟨c 7 (by decide), fun i hi => c i (by omega)⟩
  have es : ShTabAgree h (bset h 29 pos) := fun i a _ => c i (by omega)
  have ea : ArenaAgree h (bset h 29 pos) := fun i a _ => c i (by omega)
  refine ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide)]; exact r0, by rw [c 3 (by decide)]; exact tokAt_frame et hn r3,
    by rw [c 11 (by decide)]; exact r11, binds_frame rB (c 4 (by decide)) (fun i a _ => c i (by omega)) et hn es,
    defs_frame rD (c 12 (by decide)) (c 27 (by decide)) (c 26 (by decide)) (fun i a _ => c i (by omega)) et hn es,
    arena_frame rA (c 8 (by decide)) (c 9 (by decide)) (fun i a _ => c i (by omega)) es,
    fun s hs => by rw [c 25 (by decide)]; exact (r25 s hs).frame es,
    fun y hy => by rw [bget_bset_eq _ _ _ _ rfl (by rw [u, rO.1]; omega)]; simp only [Option.some.injEq] at hy; subst hy; exact nameAt_frame et (by omega) hx,
    by rw [c 30 (by decide)]; exact r30, by rw [c 32 (by decide)]; exact r32, out_frame rO (drop_bset _ _ _ (by decide)),
    tasks_frame rK (c 5 (by decide)) (fun i a _ => c i (by omega)) et hn es ea rA.2.1⟩

theorem h_stash {h ts : Buf} {st : St} {x : List Nat} {fs : List Frame} (r : Rep h ts st (.stash x :: fs)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.stash x) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ea, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [FrameArgs] at ea
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E
  have ea1 : NameAt (bset h 5 fs.length.toUInt64) a x := nameAt_ts r.1 R1.1 r.2.1 ea
  generalize bset h 5 fs.length.toUInt64 = h1 at E R1 ea1
  have ev : step h = bset h1 29 a := by rw [E]; simp [Frame.code, v96, v115]
  rw [ev]
  exact ⟨[], _, rfl, rep_set29 R1 ea1⟩

end ParInv
