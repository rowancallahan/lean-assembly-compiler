/- Nano/V2Self/Proof/ParInvStep: infrastructure for the Layer-3 handler lemmas (box C; shared with box D).
* region frame lemmas for every component of `Rep` (`TokAgree`: cell 7 and the token region ≥ 184384; …);
* `v1_eff` / `tasks_push`: pushing a task record; `step_top`: the machine step pops the top record of `TasksRep`. -/
import Nano.V2Self.Proof.ParInvState
namespace ParInv
open C BufL ParSpec ParRun

/-! ## the token region -/
/-- cell 7 (token count) and every cell from the token region on agree -/
def TokAgree (h h' : Buf) : Prop := bget h' 7 = bget h 7 ∧ ∀ i : UInt64, 184384 ≤ i.toNat → bget h' i = bget h i

theorem nameSeq_frame {h h' : Buf} (e : TokAgree h h') :
    ∀ (l : List UInt64) (a : UInt64), a.toNat + 2 * l.length + 1 < 2 ^ 40 → NameSeq h a l → NameSeq h' a l
  | [], a, ha, x => by
    simp only [NameSeq] at x ⊢
    rw [e.2 _ (by rw [d11a a (by omega)]; omega)]; exact x
  | c :: t, a, ha, x => by
    simp only [NameSeq] at x ⊢
    obtain ⟨e1, e2, e3⟩ := x
    have a2 : (a + 2).toNat = a.toNat + 2 := by rw [UInt64.toNat_add]; simp; simp at ha; omega
    refine ⟨?_, ?_, nameSeq_frame e t (a + 2) (by rw [a2]; simp at ha; omega) e3⟩
    · rw [e.2 _ (by rw [d11a a (by simp at ha; omega)]; omega)]; exact e1
    · rw [e.2 _ (by rw [d11a1 a (by simp at ha; omega)]; omega)]; exact e2

theorem nameOK_frame {h h' : Buf} (e : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 40) {pos : UInt64} {n : List UInt64}
    (x : NameOK h pos n) : NameOK h' pos n := by
  obtain ⟨e1, e2, e3⟩ := x
  have p1 : (pos + 1).toNat = pos.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨?_, nameSeq_frame e n (pos + 1) (by rw [p1]; omega) e2, by rw [e.1]; exact e3⟩
  rw [e.2 _ (by rw [d11a pos (by omega)]; omega)]; exact e1

theorem nameAt_frame {h h' : Buf} (e : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 40) {pos : UInt64} {x : List Nat}
    (r : NameAt h pos x) : NameAt h' pos x := by
  obtain ⟨nm, a, b⟩ := r; exact ⟨nm, nameOK_frame e hn a, b⟩

theorem tokAt_frame {h h' : Buf} (e : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) {p : UInt64} {toks : List Tok}
    (r : TokAt h p toks) : TokAt h' p toks := by
  induction r with
  | nil e0 => exact .nil (by rw [e.1]; exact e0)
  | kw t a b c d f _ ih =>
    have hp := UInt64.lt_iff_toNat_lt.mp a
    exact .kw t (by rw [e.1]; exact a) (by rw [e.2 _ (by rw [d11a _ (by omega)]; omega)]; exact b) c d f ih
  | @num p r bs a b c d f _ ih =>
    have hp := UInt64.lt_iff_toNat_lt.mp a
    refine .num bs (by rw [e.1]; exact a) (by rw [e.2 _ (by rw [d11a _ (by omega)]; omega)]; exact b) c (fun i hi => ?_) f ih
    have q : (p + 1 + i.toUInt64 : UInt64).toNat < 2 ^ 40 := by
      have hi' : i < 8 := hi
      have hp' : p.toNat < 2 ^ 40 := by omega
      have e1 : (p + 1).toNat = p.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have e2 : i.toUInt64.toNat = i := by simp; omega
      rw [UInt64.toNat_add, e1, e2]
      omega
    rw [e.2 _ (by rw [d11a _ q]; omega)]; exact d i hi
  | id nm a _ ih => exact .id nm (nameOK_frame e (by omega) a) ih

/-! ## the arena region -/
/-- the arena records [16448, 147520) agree -/
def ArenaAgree (h h' : Buf) : Prop := ∀ i : UInt64, 16448 ≤ i.toNat → i.toNat < 147520 → bget h' i = bget h i

theorem recAgree_of {h h' : Buf} (e : ArenaAgree h h') {ids : List UInt64} (hb : ∀ v ∈ ids, v.toNat < 16384) : RecAgree h h' ids := by
  intro v hv k hk
  have := hb v hv
  simp only [fld]; exact e _ (by rw [recK v k (by omega) hk]; omega) (by rw [recK v k (by omega) hk]; omega)

/-! ## frames -/
theorem frameArgs_frame {h h' : Buf} {arena : List RN} (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32)
    (es : ShTabAgree h h') (ea : ArenaAgree h h') (har : arena.length ≤ 16384) :
    ∀ (f : Frame) (a b : UInt64), FrameArgs h arena f a b → FrameArgs h' arena f a b := by
  have hn' : (bget h 7).toNat < 2 ^ 40 := by omega
  intro f a b r
  cases f <;> simp only [FrameArgs] at r ⊢
  all_goals first
    | exact r
    | exact ⟨nameAt_frame et hn' r.1, r.2⟩
    | exact nameAt_frame et hn' r
    | exact ShapeCode.frame r es
    | (obtain ⟨r1, ids, k, kb⟩ := r
       exact ⟨r1, ids, k.frame (recAgree_of ea (fun v hv => by have := kb v hv; omega)) es, kb⟩)

/-! ## pushing a task: `v1` -/
theorem taskCell (g : Nat) (hg : g < 4096) (k : UInt64) (hk : k.toNat < 3) : (d1 + 3 * g.toUInt64 + k).toNat = 64 + 3 * g + k.toNat := by
  have e3 : (3 * g.toUInt64).toNat = 3 * g := by rw [UInt64.toNat_mul]; simp; omega
  rw [UInt64.toNat_add, UInt64.toNat_add, e3]; simp [show d1.toNat = 64 from rfl]; omega

theorem v1_eff (h : Buf) (c a b : UInt64) (hg : (bget h 5).toNat < 4096) (hl : 12352 ≤ h.length) :
    let g := (bget h 5).toNat
    let h' := v1 h c a b
    h'.length = h.length ∧ taskAt h' g = ⟨c, a, b⟩ ∧ bget h' 5 = bget h 5 + 1 ∧
    ∀ i : UInt64, i.toNat ≠ 5 → (i.toNat < 64 + 3 * g ∨ 64 + 3 * g + 3 ≤ i.toNat) → bget h' i = bget h i := by
  intro g h'
  have u5 : (5 : UInt64).toNat = 5 := rfl
  have g1 : bget h 5 < d12 := UInt64.lt_iff_toNat_lt.mpr (by simp [show d12.toNat = 4096 from rfl]; omega)
  have eg : bget h 5 = g.toUInt64 := by simp [g]
  have c0 := taskCell g hg 0 (by decide); have c1 := taskCell g hg 1 (by decide); have c2 := taskCell g hg 2 (by decide)
  simp only [UInt64.add_zero, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl] at c0 c1 c2
  have hv : h' = bset (bset (bset (bset h (d1 + 3 * g.toUInt64) c) (d1 + 3 * g.toUInt64 + 1) a) (d1 + 3 * g.toUInt64 + 2) b) 5
      (g.toUInt64 + 1) := by
    show v1 h c a b = _
    unfold v1; simp only [g1, if_true]; rw [eg]
    congr 1
    · rw [bget_bset' _ _ _ _ (by rw [c2, u5]; omega), bget_bset' _ _ _ _ (by rw [c1, u5]; omega), bget_bset' _ _ _ _ (by rw [c0, u5]; omega), eg]
  refine ⟨by rw [hv]; simp [length_bset], ?_, ?_, ?_⟩
  · simp only [taskAt, hv]
    congr 1
    · rw [bget_bset' _ _ _ _ (by rw [c0, u5]; omega), bget_bset' _ _ _ _ (by rw [c0, c2]; omega), bget_bset' _ _ _ _ (by rw [c0, c1]; omega)]
      exact bget_bset_eq _ _ _ _ rfl (by rw [c0]; omega)
    · rw [bget_bset' _ _ _ _ (by rw [c1, u5]; omega), bget_bset' _ _ _ _ (by rw [c1, c2]; omega)]
      exact bget_bset_eq _ _ _ _ rfl (by simp only [length_bset]; rw [c1]; omega)
    · rw [bget_bset' _ _ _ _ (by rw [c2, u5]; omega)]
      exact bget_bset_eq _ _ _ _ rfl (by simp only [length_bset]; rw [c2]; omega)
  · rw [hv, eg]; exact bget_bset_eq _ _ _ _ rfl (by simp only [length_bset]; simp; omega)
  · intro i i5 hi
    rw [hv, bget_bset' _ _ _ _ (by rw [u5]; omega), bget_bset' _ _ _ _ (by rw [c2]; omega), bget_bset' _ _ _ _ (by rw [c1]; omega),
      bget_bset' _ _ _ _ (by rw [c0]; omega)]

theorem taskAt_frame {h h' : Buf} (i : Nat) (hi : i < 4096)
    (e : ∀ k : UInt64, k.toNat < 3 → bget h' (d1 + 3 * i.toUInt64 + k) = bget h (d1 + 3 * i.toUInt64 + k)) : taskAt h' i = taskAt h i := by
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  simp only [UInt64.add_zero] at e0
  simp only [taskAt, e0, e1, e2]

/-- the task records below `n` and the regions the frame arguments read are unchanged -/
theorem tasks_frame {h h' : Buf} {arena : List RN} {fs : List Frame} (r : TasksRep h arena fs) (e5 : bget h' 5 = bget h 5)
    (er : ∀ i : UInt64, 64 ≤ i.toNat → i.toNat < 64 + 3 * fs.length → bget h' i = bget h i)
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') (ea : ArenaAgree h h') (har : arena.length ≤ 16384) :
    TasksRep h' arena fs := by
  obtain ⟨r5, rl, rk⟩ := r
  refine ⟨by rw [e5]; exact r5, rl, fun k hk => ?_⟩
  have tk : taskAt h' (fs.length - 1 - k) = taskAt h (fs.length - 1 - k) :=
    taskAt_frame _ (by omega) (fun c hc => er _ (by rw [taskCell _ (by omega) c hc]; omega) (by rw [taskCell _ (by omega) c hc]; omega))
  simp only [tk]
  exact ⟨(rk k hk).1, frameArgs_frame et hn es ea har _ _ _ (rk k hk).2⟩

theorem v1_agree (h : Buf) (c a b : UInt64) (hg : (bget h 5).toNat < 4096) (hl : 12352 ≤ h.length) :
    TokAgree h (v1 h c a b) ∧ ShTabAgree h (v1 h c a b) ∧ ArenaAgree h (v1 h c a b) := by
  obtain ⟨_, _, _, U⟩ := v1_eff h c a b hg hl
  refine ⟨⟨U 7 (by decide) (Or.inl (by simp; omega)), fun i hi => U i (by omega) (Or.inr (by omega))⟩,
    fun i hi _ => U i (by omega) (Or.inr (by omega)), fun i hi _ => U i (by omega) (Or.inr (by omega))⟩

/-- **push**: `v1` with a frame's code and arguments extends the task-stack representation -/
theorem tasks_push {h : Buf} {arena : List RN} {fs : List Frame} (f : Frame) (a b : UInt64) (r : TasksRep h arena fs)
    (hfs : fs.length < 4096) (hl : 12352 ≤ h.length) (hn : (bget h 7).toNat < 2 ^ 32) (har : arena.length ≤ 16384)
    (hf : FrameArgs h arena f a b) : TasksRep (v1 h f.code.toUInt64 a b) arena (f :: fs) := by
  have hg : (bget h 5).toNat < 4096 := by rw [r.1]; exact hfs
  obtain ⟨L, T, E5, U⟩ := v1_eff h f.code.toUInt64 a b hg hl
  obtain ⟨et, es, ea⟩ := v1_agree h f.code.toUInt64 a b hg hl
  obtain ⟨r5, rl, rk⟩ := r
  refine ⟨by rw [E5, tn_add _ _ (by simp; omega)]; simp; omega, by simp; omega, fun k hk => ?_⟩
  cases k with
  | zero =>
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
    rw [← r5, T]
    exact ⟨rfl, frameArgs_frame et hn es ea har _ _ _ hf⟩
  | succ k =>
    simp only [List.length_cons, List.getElem_cons_succ] at hk ⊢
    rw [show fs.length + 1 - 1 - (k + 1) = fs.length - 1 - k by omega]
    have tk : taskAt (v1 h f.code.toUInt64 a b) (fs.length - 1 - k) = taskAt h (fs.length - 1 - k) :=
      taskAt_frame _ (by omega) (fun c hc => U _ (by rw [taskCell _ (by omega) c hc]; omega)
        (Or.inl (by rw [taskCell _ (by omega) c hc, r5]; omega)))
    rw [tk]
    exact ⟨(rk k (by omega)).1, frameArgs_frame et hn es ea har _ _ _ (rk k (by omega)).2⟩

/-- **pop**: a running machine with `Rep` on `f :: fs` steps into the handler of `f` with the decoded arguments -/
theorem step_top {h ts : Buf} {st : St} {f : Frame} {fs : List Frame} (r : TasksRep h st.arena (f :: fs)) (hl : 12352 ≤ h.length)
    (hn : (bget h 7).toNat < 2 ^ 32) (har : st.arena.length ≤ 16384) :
    let t := taskAt h fs.length
    step h = v96 (bset h 5 fs.length.toUInt64) f.code.toUInt64 t.a t.b ∧ FrameArgs h st.arena f t.a t.b ∧
      TasksRep (bset h 5 fs.length.toUInt64) st.arena fs := by
  intro t
  obtain ⟨r5, rl, rk⟩ := r
  simp only [List.length_cons] at r5 rl
  have g1 : bget h 5 - 1 = fs.length.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), r5]; simp; omega
  have t0 := rk 0 (by simp)
  simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero] at t0
  refine ⟨?_, t0.2, ?_⟩
  · simp only [step, g1, t, taskAt] at t0 ⊢
    rw [show (d1 + 3 * fs.length.toUInt64 : UInt64) = d1 + 3 * fs.length.toUInt64 + 0 by simp] at t0
    rw [← t0.1]
    simp
  · have u5 : (5 : UInt64).toNat = 5 := rfl
    refine ⟨by rw [bget_bset_eq _ _ _ _ rfl (by rw [u5]; omega)]; simp; omega, by omega, fun k hk => ?_⟩
    have tk : taskAt (bset h 5 fs.length.toUInt64) (fs.length - 1 - k) = taskAt h (fs.length - 1 - k) :=
      taskAt_frame _ (by omega) (fun c hc => bget_bset' _ _ _ _ (by rw [taskCell _ (by omega) c hc, u5]; omega))
    have := rk (k + 1) (by simp; omega)
    simp only [List.length_cons, List.getElem_cons_succ, show fs.length + 1 - 1 - (k + 1) = fs.length - 1 - k by omega] at this
    rw [tk]
    refine ⟨this.1, frameArgs_frame ⟨bget_bset' _ _ _ _ (by rw [u5]; decide), fun i hi => bget_bset' _ _ _ _ (by rw [u5]; omega)⟩ hn
      (fun i hi _ => bget_bset' _ _ _ _ (by rw [u5]; omega)) (fun i hi _ => bget_bset' _ _ _ _ (by rw [u5]; omega)) har _ _ _ this.2⟩

end ParInv
