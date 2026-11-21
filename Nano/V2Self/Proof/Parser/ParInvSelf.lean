/- Nano/V2Self/Proof/Parser/ParInvSelf: task 46 (`v124`, a self-call `name fuel args…` in a step arm) on box C's Rep (parser lead).
The fuel argument must be a Nat binding; then CONTINUE's argument tasks are pushed: args / argCheck / mkCont for the current row. -/
import Nano.V2Self.Proof.Parser.ParInvClose
import Nano.V2Self.Proof.Parser.ParInvArgName
import Nano.V2Self.Proof.Parser.ParInvMkPair
namespace ParInv
open C BufL ParSpec ParRun

theorem ShOpt.nt_iff {h : Buf} {c : UInt64} {o : Option Sh} (r : ShOpt h c o) : c = 4 ↔ o = some .nt := by
  cases o with
  | none => simp only [ShOpt] at r; subst r; simp
  | some s =>
    simp only [ShOpt] at r
    constructor
    · intro e; subst e; exact congrArg some (ShapeCode.det r .nt)
    · intro e; cases e; exact r.nt_code

/-- **task 46** (self-call arguments) -/
theorem h_selfArgs {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.selfArgs :: fs)) (hfs : inDefF fs = true)
    (hp : st.cur.params ≠ []) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF .selfArgs st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rT := R1.1; have rts := R1.2.1; have r3 := R1.2.2.2.1
  have hl31 : 31 < g.length := by omega
  have ev0 : step h = v124 g a b := by rw [E]; rfl
  rw [ev0] at hs ⊢
  unfold v124 at hs ⊢
  simp only [UInt64.add_zero] at hs ⊢
  by_cases c14 : ¬ bget g (d11 + bget g 3) = 14
  · simp only [show (bget g (d11 + bget g 3) == 14) = false from by simpa using c14, Bool.false_eq_true, if_false] at hs
    exact absurd (stat0 _ (by omega)) hs
  have c14 : bget g (d11 + bget g 3) = 14 := Decidable.of_not_not c14
  simp only [c14, beq_self_eq_true, if_true] at hs ⊢
  obtain ⟨nm, rest, et, hNm, tr⟩ := tok_id r3 rT c14
  have h7 : (bget g 7).toNat < 2 ^ 24 := by rw [rT.2.2.2]; simp; omega
  have hB := R1.2.2.2.2.2.1
  have hbl := hB.2.1
  obtain ⟨hS, hres⟩ := v7_findB hB h7 hl31 hNm
  generalize hG1 : v7 16777216 g (bget g 4) (bget g 3) = G1 at hS hres hs ⊢
  have dead : bget (bset G1 0 0) 0 ≠ 0 → False := fun x => x (stat0 _ (by rw [hS.1]; omega))
  rcases hres with ⟨h21, hfb⟩ | ⟨i, h21, hi, hfb⟩
  · rw [h21] at hs; simp at hs; exact (dead hs).elim
  have h21' : bget G1 21 ≠ 0 := by rw [h21]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
  have hi1 : bget G1 21 - 1 = i.toUInt64 := by
    rw [h21]; apply UInt64.toNat_inj.mp; simp
  simp only [show (bget G1 21 == 0) = false from by simpa using h21', Bool.false_eq_true, if_false, hi1] at hs ⊢
  obtain ⟨_, _, hBr⟩ := hB
  obtain ⟨_, _, hsh, _⟩ := hBr i hi
  have ic : (d9 + 4 * i.toUInt64 + 2).toNat = 180288 + 4 * i + 2 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]; simp [show d9.toNat = 180288 from rfl]
    omega
  have hk : bget G1 (d9 + 4 * i.toUInt64 + 2) = bget g (d9 + 4 * i.toUInt64 + 2) := hS.2 _ (by rw [ic]; omega) (by rw [ic]; omega)
  rw [hk] at hs ⊢
  by_cases c4 : ¬ bget g (d9 + 4 * i.toUInt64 + 2) = 4
  · simp only [show (bget g (d9 + 4 * i.toUInt64 + 2) == 4) = false from by simpa using c4, Bool.false_eq_true, if_false] at hs
    exact (dead hs).elim
  have c4 : bget g (d9 + 4 * i.toUInt64 + 2) = 4 := Decidable.of_not_not c4
  have hnt : (st.binds[i]'hi).sh = some .nt := hsh.nt_iff.mp c4
  simp only [c4, beq_self_eq_true, if_true] at hs ⊢
  obtain ⟨hn14, hseq, hbnd⟩ := hNm
  have g3 : bget G1 3 = bget g 3 := hS.2 3 (by decide) (by decide)
  have g7 : bget G1 7 = bget g 7 := hS.2 7 (by decide) (by decide)
  have etA : TokAgree g G1 := ⟨g7, fun i hi => hS.2 i (by omega) (by omega)⟩
  have hp3 : (bget g 3).toNat < 2 ^ 32 := by omega
  have p1 : (bget g 3 + 1).toNat = (bget g 3).toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hseq' : NameSeq G1 (bget g 3 + 1) nm := nameSeq_frame etA nm _ (by rw [p1]; omega) hseq
  rw [g3, v86_skip nm 16777216 G1 (bget g 3 + 1) hseq' (by rw [g7, p1]; omega) (by omega)] at hs ⊢
  have ecur : bget g 3 + 1 + 2 * nm.length.toUInt64 + 1 = bget g 3 + 2 + 2 * nm.length.toUInt64 := by
    apply UInt64.toNat_inj.mp; simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  rw [ecur] at hs ⊢
  have RS := rep_scratch (h' := G1) R1 (fun i a b => hS.2 i a b) (by rw [← hG1]; exact v7_drop _ _ _ _)
  have trG : TokAt G1 (bget g 3 + 2 + 2 * nm.length.toUInt64) rest := tokAt_frame etA hn tr
  have RC := rep_cursor RS _ trG
  generalize hG2 : bset G1 3 (bget g 3 + 2 + 2 * nm.length.toUInt64) = G2 at RC hs ⊢
  have e2 : ∀ i : UInt64, i.toNat ≠ 3 → i.toNat ≠ 21 → i.toNat ≠ 31 → bget G2 i = bget g i := fun i a b c => by
    rw [← hG2, bget_bset' _ _ _ _ (by simp; omega)]; exact hS.2 i b c
  have rD := R1.2.2.2.2.2.2.1
  rw [hfs] at rD
  obtain ⟨d12, dlt, _, _, dcur, _, _, _⟩ := rD
  simp only [if_true] at dcur
  obtain ⟨⟨⟨_, _, _, _, _, c6, c57, _⟩, _⟩, d512⟩ := dcur
  have hj : bget g 12 = st.defs.length.toUInt64 := by apply UInt64.toNat_inj.mp; rw [d12]; simp; omega
  have r12 : bget G2 12 = st.defs.length.toUInt64 := by rw [e2 12 (by decide) (by decide) (by decide), hj]
  have ic6 : (d7 + 8 * st.defs.length.toUInt64 + 6).toNat = 147520 + 8 * st.defs.length + 6 := defCell _ (by omega) 6 (by decide)
  have r6 : bget G2 (d7 + 8 * st.defs.length.toUInt64 + 6) = bget g (d7 + 8 * st.defs.length.toUInt64 + 6) :=
    e2 _ (by rw [ic6]; omega) (by rw [ic6]; omega) (by rw [ic6]; omega)
  rw [r12, r6] at hs ⊢
  have hplen : st.cur.params.length ≠ 0 := by simpa using hp
  have hjv : bget g (d7 + 8 * st.defs.length.toUInt64 + 6) - 1 = (st.cur.params.length - 1).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [c6]; simp; omega)), c6]
    simp; omega
  rw [hjv] at hs ⊢
  have hsA : bget (v1 (v1 G2 54 st.defs.length.toUInt64 (st.cur.params.length - 1).toUInt64) 47 st.defs.length.toUInt64
      (st.cur.params.length - 1).toUInt64) 0 ≠ 0 := fun e => hs (v1_zero _ _ _ _ e)
  have hsB : bget (v1 G2 54 st.defs.length.toUInt64 (st.cur.params.length - 1).toUInt64) 0 ≠ 0 := fun e => hsA (v1_zero _ _ _ _ e)
  have tl : ∀ k : Nat, k < 4096 → (k.toUInt64).toNat = k := fun k hk => by simp; omega
  have R3 := rep_push (.mkCont st.defs.length (st.cur.params.length - 1)) _ _ RC (by simp [inDefF, Frame.isDefs, hfs])
    ⟨tl _ (by omega), tl _ (by omega)⟩ hsB
  have R4 := rep_push (.argCheck (.df st.defs.length) (st.cur.params.length - 1)) _ _ R3 (by simp [inDefF, Frame.isDefs, hfs])
    ⟨rfl, tl _ (by omega)⟩ hsA
  have R5 := rep_push (.args (.df st.defs.length) (st.cur.params.length - 1)) _ _ R4 (by simp [inDefF, Frame.isDefs, hfs])
    ⟨rfl, tl _ (by omega)⟩ hs
  refine ⟨[.args (.df st.defs.length) (st.cur.params.length - 1), .argCheck (.df st.defs.length) (st.cur.params.length - 1),
    .mkCont st.defs.length (st.cur.params.length - 1)], _, ?_, R5⟩
  simp [stepF, et, hfb, hnt]


/-- `v5` (node build) leaves the def table and everything above it alone -/
theorem rep_v5_hi {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs)
    (n t A B : Nat) (sh : Option Sh) (p : Bool) (w : UInt64) (hw : ShOpt h w sh) (ht : t < 2 ^ 64)
    (hab : t ≠ 2 → t ≠ 5 → A < 2 ^ 64 ∧ B < 2 ^ 64) (hn : n ≤ 4096)
    (hs : bget (v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (b01 p) n.toUInt64) 0 ≠ 0) :
    ∀ i : UInt64, 147520 ≤ i.toNat → bget (v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (b01 p) n.toUInt64) i = bget h i := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds r
  have rA := r.2.2.2.2.2.2.2.1
  obtain ⟨g1, g2, g3⟩ := v5_guards _ _ _ _ _ _ _ (by omega) hs
  have en : n.toUInt64.toNat = n := by simp; omega
  have h8 := rA.2.2.1; have h9 := rA.1; have hv4 := rA.2.2.2.1
  have g1' := UInt64.lt_iff_toNat_lt.mp g1
  have g2' := UInt64.lt_iff_toNat_lt.mp g2
  rw [tn_add _ _ (by simp; omega), en] at g2'
  simp only [show d13.toNat = 16384 from rfl] at g1'
  have hle : n ≤ st.vals.length := by simp at g2'; omega
  have g3' := UInt64.lt_iff_toNat_lt.mp g3
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [en]; omega)), en] at g3'
  simp only [show d4.toNat = 4096 from rfl] at g3'
  obtain ⟨_, _, _, _, HI, _⟩ := arena_v5g h st.arena st.vals n t A B sh p w rA hle (by omega) (by omega) (by omega) hw ht hab
  simpa [b01] using HI

/-- **task 54** (CONTINUE): the self-call arguments are packed (PAIR unless exactly one) under a pending CONT node of the def's
result shape -/
theorem h_mkCont {h ts : Buf} {st : St} {f k : Nat} {fs : List Frame} (r : Rep h ts st (.mkCont f k :: fs))
    (hfs : inDefF fs = true) (hnf : fs.all (fun f => !f.isFlat)) (hf : f = st.defs.length) (hk : k ≤ 4096)
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k' st', stepF (.mkCont f k) st = some (k', st') ∧ Rep (step h) ts st' (k' ++ fs) := by
  obtain ⟨E, FA, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  have FA' := frameArgs_pop r fs.length.toUInt64 FA
  generalize (taskAt h fs.length).a = a at E FA'
  generalize (taskAt h fs.length).b = b at E FA'
  generalize bset h 5 fs.length.toUInt64 = g at E R1 FA'
  obtain ⟨ha, hb⟩ := FA'
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have ev : step h = v125 g a b := by rw [E]; rfl
  rw [ev] at hs ⊢
  subst hf
  have rD := R1.2.2.2.2.2.2.1
  rw [hfs] at rD
  obtain ⟨d12, dlt, _, _, dcur, _, _, _⟩ := rD
  simp only [if_true] at dcur
  obtain ⟨⟨⟨_, _, _, c3, _, _, _, _⟩, _⟩, d512⟩ := dcur
  have hA : a = st.defs.length.toUInt64 := by apply UInt64.toNat_inj.mp; rw [ha]; simp; omega
  have hB : b = k.toUInt64 := by apply UInt64.toNat_inj.mp; rw [hb]; simp; omega
  subst hA hB
  unfold v125 at hs ⊢
  simp only [] at hs ⊢
  generalize hw : bget g (d7 + 8 * st.defs.length.toUInt64 + 3) = w at hs ⊢ c3
  have hrow : (rows st)[st.defs.length]? = some st.cur := by simp [rows]
  by_cases k1 : k = 1
  · subst k1
    simp only [show ((1 : Nat).toUInt64 == 1) = true from rfl, if_true] at hs ⊢
    obtain ⟨st', hm, R2⟩ := rep_v5 R1 hnf 1 11 0 0 st.cur.res true w c3 (by decide) (by decide) (by decide) (by decide) hs
    exact ⟨[], st', by simp [stepF, hrow, hm], R2⟩
  · have kb : (k.toUInt64 == 1) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; apply k1
      have := congrArg UInt64.toNat e; simp at this; omega
    simp only [kb, Bool.false_eq_true, if_false] at hs ⊢
    have hs1 : bget (v5 g (6 : Nat).toUInt64 k.toUInt64 (0 : Nat).toUInt64 0 (b01 false) k.toUInt64) 0 ≠ 0 :=
      fun e => hs (v5_stat _ _ _ _ _ _ _ e)
    obtain ⟨st1, hm1, R2⟩ := rep_v5 R1 hnf k 6 k 0 none false 0 rfl (by decide) (by omega) (by decide) hk hs1
    have HI := rep_v5_hi R1 k 6 k 0 none false 0 rfl (by decide) (fun _ _ => ⟨by omega, by decide⟩) hk hs1
    have hcur1 : st1.cur = st.cur := by unfold mkNode at hm1; split at hm1 <;> cases hm1; rfl
    have es : ShTabAgree g (v5 g (6 : Nat).toUInt64 k.toUInt64 (0 : Nat).toUInt64 0 (b01 false) k.toUInt64) :=
      fun i a _ => HI i (by omega)
    obtain ⟨st', hm, R3⟩ := rep_v5 R2 hnf 1 11 0 0 st.cur.res true w (c3.frame es) (by decide) (by decide) (by decide) (by decide) hs
    exact ⟨[], st', by simp [stepF, hrow, k1, hm1, hcur1, hm], R3⟩

end ParInv
