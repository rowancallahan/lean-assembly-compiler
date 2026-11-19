/- Nano/V2Self/Proof/ParInvStep: infrastructure for the Layer-3 handler lemmas (box C; shared with box D).
* region frame lemmas for every component of `Rep` (`TokAgree`: cell 7 and the token region ≥ 184384; …);
* `v1_eff` / `tasks_push`: pushing a task record; `step_top`: the machine step pops the top record of `TasksRep`. -/
import Nano.V2Self.Proof.ParInvState
namespace ParInv
open C BufL ParSpec ParRun

/-! ## the token region -/
/-- cell 7 (token count) and every cell from the token region on agree -/
def TokAgree (h h' : Buf) : Prop := bget h' 7 = bget h 7 ∧ ∀ i : UInt64, 184384 ≤ i.toNat → bget h' i = bget h i

/-- the NARROW agreement the frame lemmas need: cell 7 and the token cells, the sentinel and the IRV word
`[184384, 184386 + h[7])` — it survives an output append `H ++ ws` (`TokAgree` is the wide form; it coerces) -/
def TokAgreeN (h h' : Buf) : Prop :=
  bget h' 7 = bget h 7 ∧ ∀ i : UInt64, 184384 ≤ i.toNat → i.toNat < 184386 + (bget h 7).toNat → bget h' i = bget h i

theorem TokAgree.n {h h' : Buf} (e : TokAgree h h') : TokAgreeN h h' := ⟨e.1, fun i a _ => e.2 i a⟩


/-- `NameSeq` reads cells `d11 + a .. d11 + a + 2|l|` only -/
theorem nameSeq_frameN {h h' : Buf} (e : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 40) :
    ∀ (l : List UInt64) (a : UInt64), a.toNat + 2 * l.length < (bget h 7).toNat → NameSeq h a l → NameSeq h' a l
  | [], a, ha, x => by
    simp only [NameSeq] at x ⊢
    rw [e.2 _ (by rw [d11a a (by omega)]; omega) (by rw [d11a a (by omega)]; simp at ha; omega)]; exact x
  | c :: t, a, ha, x => by
    simp only [NameSeq] at x ⊢
    obtain ⟨e1, e2, e3⟩ := x
    simp at ha
    have a2 : (a + 2).toNat = a.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
    refine ⟨?_, ?_, nameSeq_frameN e hn t (a + 2) (by rw [a2]; omega) e3⟩
    · rw [e.2 _ (by rw [d11a a (by omega)]; omega) (by rw [d11a a (by omega)]; omega)]; exact e1
    · rw [e.2 _ (by rw [d11a1 a (by omega)]; omega) (by rw [d11a1 a (by omega)]; omega)]; exact e2

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

theorem nameOK_frameN {h h' : Buf} (e : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 40) {pos : UInt64} {n : List UInt64}
    (x : NameOK h pos n) : NameOK h' pos n := by
  obtain ⟨e1, e2, e3⟩ := x
  have p1 : (pos + 1).toNat = pos.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨?_, nameSeq_frameN e hn n (pos + 1) (by rw [p1]; omega) e2, by rw [e.1]; exact e3⟩
  rw [e.2 _ (by rw [d11a pos (by omega)]; omega) (by rw [d11a pos (by omega)]; omega)]; exact e1

theorem nameOK_frame {h h' : Buf} (e : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 40) {pos : UInt64} {n : List UInt64}
    (x : NameOK h pos n) : NameOK h' pos n := nameOK_frameN e.n hn x

theorem nameAt_frameN {h h' : Buf} (e : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 40) {pos : UInt64} {x : List Nat}
    (r : NameAt h pos x) : NameAt h' pos x := by
  obtain ⟨nm, a, b⟩ := r; exact ⟨nm, nameOK_frameN e hn a, b⟩

theorem nameAt_frame {h h' : Buf} (e : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 40) {pos : UInt64} {x : List Nat}
    (r : NameAt h pos x) : NameAt h' pos x := nameAt_frameN e.n hn r

theorem TokAt.le {h : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) : p.toNat ≤ (bget h 7).toNat := by
  cases r with
  | nil e => rw [← e]; exact Nat.le_refl _
  | kw _ a => exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp a)
  | num _ a => exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp a)
  | id _ a => have := a.2.2; omega

theorem tokAt_frameN {h h' : Buf} (e : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 32) {p : UInt64} {toks : List Tok}
    (r : TokAt h p toks) : TokAt h' p toks := by
  induction r with
  | nil e0 => exact .nil (by rw [e.1]; exact e0)
  | kw t a b c d f _ ih =>
    have hp := UInt64.lt_iff_toNat_lt.mp a
    exact .kw t (by rw [e.1]; exact a) (by rw [e.2 _ (by rw [d11a _ (by omega)]; omega) (by rw [d11a _ (by omega)]; omega)]; exact b) c d f ih
  | @num p r bs a b c d f tl ih =>
    have hp := UInt64.lt_iff_toNat_lt.mp a
    have h9 := TokAt.le tl
    have hp9 : (p + 9).toNat = p.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
    rw [hp9] at h9
    refine .num bs (by rw [e.1]; exact a) (by rw [e.2 _ (by rw [d11a _ (by omega)]; omega) (by rw [d11a _ (by omega)]; omega)]; exact b) c
      (fun i hi => ?_) f ih
    have hi' : i < 8 := hi
    have q : (p + 1 + i.toUInt64 : UInt64).toNat = p.toNat + 1 + i := by
      have e1 : (p + 1).toNat = p.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have e2 : i.toUInt64.toNat = i := by simp; omega
      rw [UInt64.toNat_add, e1, e2]; omega
    rw [e.2 _ (by rw [d11a _ (by rw [q]; omega)]; omega) (by rw [d11a _ (by rw [q]; omega), q]; omega)]; exact d i hi
  | id nm a _ ih => exact .id nm (nameOK_frameN e (by omega) a) ih

theorem tokAt_frame {h h' : Buf} (e : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) {p : UInt64} {toks : List Tok}
    (r : TokAt h p toks) : TokAt h' p toks := tokAt_frameN e.n hn r

/-! ## the arena region -/
/-- the arena records [16448, 147520) agree -/
def ArenaAgree (h h' : Buf) : Prop := ∀ i : UInt64, 16448 ≤ i.toNat → i.toNat < 147520 → bget h' i = bget h i

theorem recAgree_of {h h' : Buf} (e : ArenaAgree h h') {ids : List UInt64} (hb : ∀ v ∈ ids, v.toNat < 16384) : RecAgree h h' ids := by
  intro v hv k hk
  have := hb v hv
  simp only [fld]; exact e _ (by rw [recK v k (by omega) hk]; omega) (by rw [recK v k (by omega) hk]; omega)

/-! ## frames -/
theorem frameArgs_frameN {h h' : Buf} {arena : List RN} (et : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 32)
    (es : ShTabAgree h h') (ea : ArenaAgree h h') (har : arena.length ≤ 16384) :
    ∀ (f : Frame) (a b : UInt64), FrameArgs h arena f a b → FrameArgs h' arena f a b := by
  have hn' : (bget h 7).toNat < 2 ^ 40 := by omega
  intro f a b r
  cases f <;> simp only [FrameArgs] at r ⊢
  all_goals first
    | exact r
    | exact ⟨nameAt_frameN et hn' r.1, r.2⟩
    | exact nameAt_frameN et hn' r
    | exact ShapeCode.frame r es
    | (obtain ⟨r1, ids, k, kb⟩ := r
       exact ⟨r1, ids, k.frame (recAgree_of ea (fun v hv => by have := kb v hv; omega)) es, kb⟩)

theorem frameArgs_frame {h h' : Buf} {arena : List RN} (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32)
    (es : ShTabAgree h h') (ea : ArenaAgree h h') (har : arena.length ≤ 16384) :
    ∀ (f : Frame) (a b : UInt64), FrameArgs h arena f a b → FrameArgs h' arena f a b := frameArgs_frameN et.n hn es ea har

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
theorem tasks_frameN {h h' : Buf} {arena : List RN} {fs : List Frame} (r : TasksRep h arena fs) (e5 : bget h' 5 = bget h 5)
    (er : ∀ i : UInt64, 64 ≤ i.toNat → i.toNat < 64 + 3 * fs.length → bget h' i = bget h i)
    (et : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') (ea : ArenaAgree h h') (har : arena.length ≤ 16384) :
    TasksRep h' arena fs := by
  obtain ⟨r5, rl, rk⟩ := r
  refine ⟨by rw [e5]; exact r5, rl, fun k hk => ?_⟩
  have tk : taskAt h' (fs.length - 1 - k) = taskAt h (fs.length - 1 - k) :=
    taskAt_frame _ (by omega) (fun c hc => er _ (by rw [taskCell _ (by omega) c hc]; omega) (by rw [taskCell _ (by omega) c hc]; omega))
  simp only [tk]
  exact ⟨(rk k hk).1, frameArgs_frameN et hn es ea har _ _ _ (rk k hk).2⟩

theorem tasks_frame {h h' : Buf} {arena : List RN} {fs : List Frame} (r : TasksRep h arena fs) (e5 : bget h' 5 = bget h 5)
    (er : ∀ i : UInt64, 64 ≤ i.toNat → i.toNat < 64 + 3 * fs.length → bget h' i = bget h i)
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') (ea : ArenaAgree h h') (har : arena.length ≤ 16384) :
    TasksRep h' arena fs := tasks_frameN r e5 er et.n hn es ea har

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

/-! ## component frames: each part of `Rep` reads a fixed set of cells -/
/-- cells in `[lo, hi)` agree -/
def RegAgree (h h' : Buf) (lo hi : Nat) : Prop := ∀ i : UInt64, lo ≤ i.toNat → i.toNat < hi → bget h' i = bget h i

theorem rowCell (i : Nat) (hi : i < 1024) (k : UInt64) (hk : k.toNat < 4) : (d9 + 4 * i.toUInt64 + k).toNat = 180288 + 4 * i + k.toNat := by
  have e4 : (4 * i.toUInt64).toNat = 4 * i := by rw [UInt64.toNat_mul]; simp; omega
  rw [UInt64.toNat_add, UInt64.toNat_add, e4]; simp [show d9.toNat = 180288 from rfl]; omega

theorem binds_frameN {h h' : Buf} {bs : List Bd} (r : BindsRep h bs) (e4 : bget h' 4 = bget h 4) (er : RegAgree h h' 180288 184384)
    (et : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') : BindsRep h' bs := by
  obtain ⟨r4, rl, rk⟩ := r
  refine ⟨by rw [e4]; exact r4, rl, fun i hi => ?_⟩
  have c : ∀ k : UInt64, k.toNat < 4 → bget h' (d9 + 4 * i.toUInt64 + k) = bget h (d9 + 4 * i.toUInt64 + k) :=
    fun k hk => er _ (by rw [rowCell i (by omega) k hk]; omega) (by rw [rowCell i (by omega) k hk]; omega)
  have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
  obtain ⟨a0, a1, a2, a3⟩ := rk i hi
  exact ⟨by rw [c0]; exact nameAt_frameN et (by omega) a0, by rw [c 1 (by decide)]; exact a1, by rw [c 2 (by decide)]; exact a2.frame es,
    by rw [c 3 (by decide)]; exact a3⟩

theorem binds_frame {h h' : Buf} {bs : List Bd} (r : BindsRep h bs) (e4 : bget h' 4 = bget h 4) (er : RegAgree h h' 180288 184384)
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') : BindsRep h' bs := binds_frameN r e4 er et.n hn es

theorem defCell (j : Nat) (hj : j < 512) (k : UInt64) (hk : k.toNat < 8) : (d7 + 8 * j.toUInt64 + k).toNat = 147520 + 8 * j + k.toNat := by
  have e8 : (8 * j.toUInt64).toNat = 8 * j := by rw [UInt64.toNat_mul]; simp; omega
  rw [UInt64.toNat_add, UInt64.toNat_add, e8]; simp [show d7.toNat = 147520 from rfl]; omega

theorem parCell (s : UInt64) (i : Nat) (hs : s.toNat + i < 4096) : (d7 + 4096 + s + i.toUInt64).toNat = 151616 + s.toNat + i := by
  rw [UInt64.toNat_add, UInt64.toNat_add, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; simp; omega

theorem parCell0 (i : Nat) (hi : i < 4096) : (d7 + 4096 + i.toUInt64).toNat = 151616 + i := by
  rw [UInt64.toNat_add, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; simp; omega

theorem shRow0 (k : Nat) (hk : k < 8192) : (d7 + 8192 + 3 * k.toUInt64).toNat = 155712 + 3 * k := by
  have e3 : (3 * k.toUInt64).toNat = 3 * k := by rw [UInt64.toNat_mul]; simp; omega
  rw [UInt64.toNat_add, e3, show (d7 + 8192 : UInt64).toNat = 155712 from rfl]; omega

theorem row_frameN {h h' : Buf} {j : Nat} {d : DefR} (hj : j < 512) (r : RowRep h j d) (er : RegAgree h h' 147520 180288)
    (et : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') : RowRep h' j d := by
  have c : ∀ k : UInt64, k.toNat < 8 → bget h' (d7 + 8 * j.toUInt64 + k) = bget h (d7 + 8 * j.toUInt64 + k) :=
    fun k hk => er _ (by rw [defCell j hj k hk]; omega) (by rw [defCell j hj k hk]; omega)
  have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
  obtain ⟨a0, a1, a2, a3, a4, a6, a5, ap⟩ := r
  refine ⟨by rw [c0]; exact nameAt_frameN et (by omega) a0, by rw [c 1 (by decide)]; exact a1, by rw [c 2 (by decide)]; exact a2,
    by rw [c 3 (by decide)]; exact a3.frame es, by rw [c 4 (by decide)]; exact a4, by rw [c 6 (by decide)]; exact a6,
    by rw [c 5 (by decide)]; exact a5, fun i hi => ?_⟩
  rw [c 5 (by decide), er _ (by rw [parCell _ _ (by omega)]; omega) (by rw [parCell _ _ (by omega)]; omega)]
  exact (ap i hi).frame es

theorem row_frame {h h' : Buf} {j : Nat} {d : DefR} (hj : j < 512) (r : RowRep h j d) (er : RegAgree h h' 147520 180288)
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') : RowRep h' j d := row_frameN hj r er et.n hn es

theorem rowZero_frame {h h' : Buf} {j : Nat} (hj : j < 512) (r : RowZero h j) (er : RegAgree h h' 147520 180288) : RowZero h' j :=
  fun k hk => by rw [er _ (by rw [defCell j hj k hk]; omega) (by rw [defCell j hj k hk]; omega)]; exact r k hk

theorem shRowK (i : Nat) (hi : i < 8192) (k : UInt64) (hk : k.toNat < 3) :
    (d7 + 8192 + 3 * i.toUInt64 + k).toNat = 155712 + 3 * i + k.toNat := by
  have e3 : (3 * i.toUInt64).toNat = 3 * i := by rw [UInt64.toNat_mul]; simp; omega
  rw [UInt64.toNat_add, UInt64.toNat_add, e3, show (d7 + 8192 : UInt64).toNat = 155712 from rfl]; omega

theorem defs_frameN {h h' : Buf} {st : St} {b : Bool} (r : DefsRep h st b) (e12 : bget h' 12 = bget h 12) (e27 : bget h' 27 = bget h 27)
    (e26 : bget h' 26 = bget h 26)
    (er : RegAgree h h' 147520 180288) (et : TokAgreeN h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') :
    DefsRep h' st b := by
  obtain ⟨r12, rl, r27, rd, rc, rz, r0, rs26, rs, rsd⟩ := r
  have c5 : ∀ j, j < 512 → bget h' (d7 + 8 * j.toUInt64 + 5) = bget h (d7 + 8 * j.toUInt64 + 5) :=
    fun j hj => er _ (by rw [defCell j hj 5 (by decide), show (5 : UInt64).toNat = 5 from rfl]; omega)
      (by rw [defCell j hj 5 (by decide), show (5 : UInt64).toNat = 5 from rfl]; omega)
  refine ⟨by rw [e12]; exact r12, rl, by rw [e27]; exact r27, fun j hj => ⟨row_frameN (by omega) (rd j hj).1 er et hn es,
    by rw [c5 j (by omega), e27]; exact (rd j hj).2⟩, ?_, fun j h1 h2 => rowZero_frame h2 (rz j h1 h2) er,
    fun i h1 h2 => by rw [er _ (by rw [parCell0 i h2]; omega) (by rw [parCell0 i h2]; omega)]; exact r0 i (by rw [← e27]; exact h1) h2,
    by rw [e26]; exact rs26, fun k h1 h2 => by rw [es _ (by rw [shRow0 k h2]; omega) (by rw [shRow0 k h2]; omega)]; exact rs k (by rw [← e26]; exact h1) h2,
    fun k hk => by
      rw [e26] at hk
      obtain ⟨l, r, a, b, w⟩ := rsd k hk
      have c : ∀ q : UInt64, q.toNat < 3 → bget h' (d7 + 8192 + 3 * k.toUInt64 + q) = bget h (d7 + 8192 + 3 * k.toUInt64 + q) :=
        fun q hq => es _ (by rw [shRowK k (by omega) q hq]; omega) (by rw [shRowK k (by omega) q hq]; omega)
      have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
      exact ⟨l, r, by rw [c0]; exact a.frame es, by rw [c 1 (by decide)]; exact b.frame es, by rw [c 2 (by decide)]; exact w⟩⟩
  cases b with
  | true =>
    simp only [if_true] at rc ⊢
    have hl := rc.2
    exact ⟨⟨row_frameN hl rc.1.1 er et hn es, by rw [c5 _ hl, e27]; exact rc.1.2⟩, hl⟩
  | false => simp only [Bool.false_eq_true, if_false] at rc ⊢; exact fun hl => rowZero_frame hl (rc hl) er

theorem defs_frame {h h' : Buf} {st : St} {b : Bool} (r : DefsRep h st b) (e12 : bget h' 12 = bget h 12) (e27 : bget h' 27 = bget h 27)
    (e26 : bget h' 26 = bget h 26)
    (er : RegAgree h h' 147520 180288) (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') :
    DefsRep h' st b := defs_frameN r e12 e27 e26 er et.n hn es

theorem arena_frame {h h' : Buf} {arena vals : List RN} (r : ArenaRep h arena vals) (e8 : bget h' 8 = bget h 8)
    (e9 : bget h' 9 = bget h 9) (er : RegAgree h h' 12352 147520) (es : ShTabAgree h h') : ArenaRep h' arena vals := by
  obtain ⟨r9, ral, r8, rvl, I, hI, hR, hD, hX⟩ := r
  have ea : ArenaAgree h h' := fun i a b => er i (by omega) b
  have op : ∀ k, k < 4096 → opAt h' k = opAt h k := fun k hk => er _ (by rw [d3k k hk]; omega) (by rw [d3k k hk]; omega)
  refine ⟨by rw [e9]; exact r9, ral, by rw [e8]; exact r8, rvl, I, fun u hu => ?_, fun k hk => ?_, fun k1 k2 h1 h2 e => ?_,
    fun k1 k2 h1 h2 h12 => ?_⟩
  · obtain ⟨a, b, c⟩ := hI u hu
    obtain ⟨t, et⟩ := a.head
    refine ⟨a.frame (fun k hk => ?_) (recAgree_of ea (fun v hv => ?_)) es, b, c⟩
    · have hu' : (u.toUInt64).toNat = u := by simp; omega
      show bget h' _ = bget h _
      exact ea _ (by rw [recK _ k (by omega) (by omega)]; omega) (by rw [recK _ k (by omega) (by omega)]; omega)
    · have := c v (List.mem_of_mem_tail hv); omega
  · simp only [op (vals.length - 1 - k) (by omega)]; exact hR k hk
  · rw [op _ (by omega), op _ (by omega)] at e; exact hD k1 k2 h1 h2 e
  · rw [op _ (by omega), op _ (by omega)]; exact hX k1 k2 h1 h2 h12

theorem out_frame {h h' ts : Buf} {out : List UInt64} (r : OutRep h ts out) (e : h'.drop 184384 = h.drop 184384) :
    OutRep h' ts out := by
  obtain ⟨rl, rk⟩ := r
  have l1 : h'.length = h.length := by
    have := congrArg List.length e; simp at this; omega
  refine ⟨by rw [l1]; exact rl, ?_⟩
  have d1 : ∀ l : Buf, l.drop (184384 + ts.length + 1) = (l.drop 184384).drop (ts.length + 1) := by
    intro l; rw [List.drop_drop, Nat.add_assoc]
  rw [d1, e, ← d1]; exact rk

/-- a write below the token region leaves the high part of the heap as a list -/
theorem drop_bset (h : Buf) (i v : UInt64) (hi : i.toNat < 184384) : (bset h i v).drop 184384 = h.drop 184384 := by
  simp only [bset]; exact List.drop_set_of_lt hi

theorem tokensAt_frameN {h h' ts : Buf} (r : TokensAt h ts) (et : TokAgreeN h h') (hts : ts.length < 2 ^ 24) : TokensAt h' ts := by
  obtain ⟨a, b, c, d⟩ := r
  have d' : (bget h 7).toNat = ts.length := by rw [d]; simp; omega
  refine ⟨fun i hi => ?_, ?_, ?_, by rw [et.1]; exact d⟩
  · rw [et.2 _ (by rw [d11a _ (by simp; omega)]; omega) (by rw [d11a _ (by simp; omega)]; simp; omega)]; exact a i hi
  · rw [et.2 _ (by rw [d11a _ (by simp; omega)]; omega) (by rw [d11a _ (by simp; omega)]; simp; omega)]; exact b
  · rw [et.2 _ (by rw [d11a1 _ (by simp; omega)]; omega) (by rw [d11a1 _ (by simp; omega)]; simp; omega)]; exact c

theorem tokensAt_frame {h h' ts : Buf} (r : TokensAt h ts) (et : TokAgree h h') (hts : ts.length < 2 ^ 24) : TokensAt h' ts :=
  tokensAt_frameN r et.n hts

/-! ## Rep when only the task stack changed -/
theorem rep_tasks {h h' ts : Buf} {st : St} {fs fs' : List Frame} (r : Rep h ts st fs) (hl : h'.length = h.length)
    (e : ∀ i : UInt64, i.toNat ≠ 5 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) → bget h' i = bget h i)
    (ed : h'.drop 184384 = h.drop 184384) (hT : TasksRep h' st.arena fs') (hd : inDefF fs' = inDefF fs) : Rep h' ts st fs' := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, _⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have et : TokAgree h h' := ⟨e 7 (by decide) (Or.inl (by decide)), fun i hi => e i (by omega) (Or.inr (by omega))⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (Or.inr (by omega))
  have c : ∀ n : UInt64, n.toNat < 64 → n.toNat ≠ 5 → bget h' n = bget h n := fun n hn h5 => e _ h5 (Or.inl hn)
  refine ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide)]; exact r0, by rw [c 3 (by decide) (by decide)]; exact tokAt_frame et hn r3,
    by rw [c 11 (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide)) (fun i a _ => e i (by omega) (Or.inr (by omega))) et hn es,
    by rw [hd]; exact defs_frame rD (c 12 (by decide) (by decide)) (c 27 (by decide) (by decide)) (c 26 (by decide) (by decide)) (fun i a _ => e i (by omega) (Or.inr (by omega))) et hn es,
    arena_frame rA (c 8 (by decide) (by decide)) (c 9 (by decide) (by decide)) (fun i a _ => e i (by omega) (Or.inr (by omega))) es,
    fun s hs => by rw [c 25 (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx => by rw [c 29 (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [c 30 (by decide) (by decide)]; exact r30, by rw [c 32 (by decide) (by decide)]; exact r32, out_frame rO ed, hT⟩

/-- the status stays 0 through a push -/
theorem v1_zero (h : Buf) (c a b : UInt64) (h0 : bget h 0 = 0) : bget (v1 h c a b) 0 = 0 := by
  unfold v1
  split
  · rename_i hg
    have hgN := UInt64.lt_iff_toNat_lt.mp hg
    simp only [show d12.toNat = 4096 from rfl] at hgN
    have c0 := taskCell (bget h 5).toNat hgN 0 (by decide); have c1 := taskCell (bget h 5).toNat hgN 1 (by decide)
    have c2 := taskCell (bget h 5).toNat hgN 2 (by decide)
    simp only [UInt64.add_zero, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl,
      show (2 : UInt64).toNat = 2 from rfl, UInt64.ofNat_toNat] at c0 c1 c2
    rw [bget_bset' _ _ _ _ (by simp), bget_bset' _ _ _ _ (by rw [c2]; simp), bget_bset' _ _ _ _ (by rw [c1]; simp),
      bget_bset' _ _ _ _ (by rw [c0]; simp)]; exact h0
  · rw [bget_bset]; split <;> simp_all

/-- a push that leaves the status nonzero succeeded (h[5] was below the capacity) -/
theorem v1_ok (h : Buf) (c a b : UInt64) (hs : bget (v1 h c a b) 0 ≠ 0) : (bget h 5).toNat < 4096 := by
  by_cases hc0 : (bget h 5).toNat < 4096
  · exact hc0
  exfalso
  have hc := hc0
  have : ¬ bget h 5 < d12 := fun x => hc (by have := UInt64.lt_iff_toNat_lt.mp x; simpa using this)
  apply hs; unfold v1; simp only [this, if_false]; rw [bget_bset]; split <;> simp_all [bget, List.getD]

/-! ## tokens at the cursor -/
/-- a keyword cell (not 0 / 5 / 14) at the cursor is the spec token `.k t` -/
theorem tok_kw {h ts : Buf} {p t : UInt64} {toks : List Tok} (r : TokAt h p toks) (hT : TokensAt h ts) (hts : ts.length < 2 ^ 24)
    (hc : bget h (d11 + p) = t) (t0 : t ≠ 0) (t5 : t ≠ 5) (t14 : t ≠ 14) : ∃ rest, toks = .k t.toNat :: rest ∧ TokAt h (p + 1) rest := by
  cases r with
  | nil e =>
    exfalso; apply t0; rw [← hc, e, hT.2.2.2]; exact hT.2.1
  | kw t' _ b _ _ _ x => rw [b] at hc; subst hc; exact ⟨_, rfl, x⟩
  | num _ _ b => rw [b] at hc; exact absurd hc.symm t5
  | id _ a _ => rw [a.1] at hc; exact absurd hc.symm t14

/-- Rep when only the cursor h[3], h[5] and task records changed (the cursor now represents `toks'`) -/
theorem rep_tok {h h' ts : Buf} {st : St} {fs fs' : List Frame} {toks' : List Tok} (r : Rep h ts st fs) (hl : h'.length = h.length)
    (e : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 3 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) → bget h' i = bget h i)
    (ed : h'.drop 184384 = h.drop 184384) (hK : TokAt h' (bget h' 3) toks') (hT : TasksRep h' st.arena fs')
    (hd : inDefF fs' = inDefF fs) : Rep h' ts { st with toks := toks' } fs' := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, _⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have et : TokAgree h h' := ⟨e 7 (by decide) (by decide) (Or.inl (by decide)), fun i hi => e i (by omega) (by omega) (Or.inr (by omega))⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (by omega) (Or.inr (by omega))
  have c : ∀ n : UInt64, n.toNat < 64 → n.toNat ≠ 5 → n.toNat ≠ 3 → bget h' n = bget h n := fun n hn h5 h3 => e _ h5 h3 (Or.inl hn)
  refine ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide) (by decide)]; exact r0, hK,
    by rw [c 11 (by decide) (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega) (Or.inr (by omega))) et hn es,
    (by rw [hd]; exact defs_frame rD (c 12 (by decide) (by decide) (by decide)) (c 27 (by decide) (by decide) (by decide)) (c 26 (by decide) (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega) (Or.inr (by omega))) et hn es),
    arena_frame rA (c 8 (by decide) (by decide) (by decide)) (c 9 (by decide) (by decide) (by decide))
      (fun i a _ => e i (by omega) (by omega) (Or.inr (by omega))) es,
    fun s hs => by rw [c 25 (by decide) (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx => by rw [c 29 (by decide) (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [c 30 (by decide) (by decide) (by decide)]; exact r30, by rw [c 32 (by decide) (by decide) (by decide)]; exact r32,
    out_frame rO ed, hT⟩

end ParInv
