/- Nano/Parser/ParInvBuild: Layer-3 node building at the level of `Rep` (box C).
* `v5_guards` : a `v5` that leaves the status nonzero passed its three capacity / depth guards;
* `tasks_arena_ext` / `rep_arena` : Rep after the operand stack and the arena changed (arena extended);
* `rep_v5` : B's `mkNode` is `v5` on `Rep` (no flatten frame pending: flatten frames read sibling chains);
* handlers: `h_mkBin` (task 5). -/
import Nano.Parser.ParInvCall
namespace ParInv
open C BufL ParSpec ParRun

def _root_.ParRun.Frame.isFlat : Frame → Bool
  | .flat _ => true
  | .flatL _ => true
  | _ => false

theorem v5_guards (h : Buf) (c a b w t n : UInt64) (hl : 0 < h.length) (hs : bget (v5 h c a b w t n) 0 ≠ 0) :
    bget h 9 < d13 ∧ n < bget h 8 + 1 ∧ bget h 8 - n < d4 := by
  unfold v5 at hs
  by_cases g1 : bget h 9 < d13
  · by_cases g2 : n < bget h 8 + 1
    · by_cases g3 : bget h 8 - n < d4
      · exact ⟨g1, g2, g3⟩
      · simp only [g1, g2, g3, if_true, if_false] at hs; exact absurd (stat0 _ hl) hs
    · simp only [g1, g2, if_true, if_false] at hs; exact absurd (stat0 _ hl) hs
  · simp only [g1, if_false] at hs; exact absurd (stat0 _ hl) hs

/-- the frame arguments survive an arena extension (no flatten frames: those read sibling chains) -/
theorem tasks_arena_ext {h : Buf} {arena arena' : List RN} {fs : List Frame} (r : TasksRep h arena fs)
    (hp : ∃ l, arena' = arena ++ l) : TasksRep h arena' fs := by
  obtain ⟨l, rfl⟩ := hp
  obtain ⟨r5, rl, rk⟩ := r
  refine ⟨r5, rl, fun k hk => ⟨(rk k hk).1, ?_⟩⟩
  have := (rk k hk).2
  generalize fs[k] = f at this ⊢
  cases f <;> simp only [FrameArgs] at this ⊢
  all_goals first
    | exact this
    | (obtain ⟨ids, k1, kb⟩ := this
       exact ⟨ids, k1, fun v hv => by have := kb v hv; simp; omega⟩)
    | (obtain ⟨b1, ids, k1, kb⟩ := this
       exact ⟨b1, ids, k1, fun v hv => by have := kb v hv; simp; omega⟩)

/-- Rep when only h[5], the task records, h[8], h[9], the operand stack and the arena changed -/
theorem rep_arena {h h' ts : Buf} {st : St} {fs fs' : List Frame} {arena' vals' : List RN} (r : Rep h ts st fs)
    (hl : h'.length = h.length)
    (e : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 8 → i.toNat ≠ 9 → (i.toNat < 64 ∨ 147520 ≤ i.toNat) → bget h' i = bget h i)
    (ed : h'.drop 184384 = h.drop 184384) (hA : ArenaRep h' arena' vals') (hT : TasksRep h' arena' fs')
    (hd : inDefF fs' = inDefF fs) : Rep h' ts { st with vals := vals', arena := arena' } fs' := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, _⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have et : TokAgree h h' := ⟨e 7 (by decide) (by decide) (by decide) (Or.inl (by decide)),
    fun i hi => e i (by omega) (by omega) (by omega) (Or.inr (by omega))⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (by omega) (by omega) (Or.inr (by omega))
  have c : ∀ n : UInt64, n.toNat < 64 → n.toNat ≠ 5 → n.toNat ≠ 8 → n.toNat ≠ 9 → bget h' n = bget h n :=
    fun n hn h5 h8 h9 => e _ h5 h8 h9 (Or.inl hn)
  refine ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide) (by decide) (by decide)]; exact r0,
    by rw [c 3 (by decide) (by decide) (by decide) (by decide)]; exact tokAt_frame et hn r3,
    by rw [c 11 (by decide) (by decide) (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide) (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega) (by omega) (Or.inr (by omega))) et hn es,
    (by rw [hd]; exact defs_frame rD (c 12 (by decide) (by decide) (by decide) (by decide)) (c 27 (by decide) (by decide) (by decide) (by decide)) (c 26 (by decide) (by decide) (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega) (by omega) (Or.inr (by omega))) et hn es),
    hA, fun s hs => by rw [c 25 (by decide) (by decide) (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx => by rw [c 29 (by decide) (by decide) (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [c 30 (by decide) (by decide) (by decide) (by decide)]; exact r30,
    by rw [c 32 (by decide) (by decide) (by decide) (by decide)]; exact r32, out_frame rO ed, hT⟩

/-- frame arguments of non-flatten frames do not read the arena records -/
theorem frameArgs_frame_nf {h h' : Buf} {arena : List RN} (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32)
    (es : ShTabAgree h h') : ∀ (f : Frame), f.isFlat = false → ∀ (a b : UInt64), FrameArgs h arena f a b → FrameArgs h' arena f a b := by
  have hn' : (bget h 7).toNat < 2 ^ 40 := by omega
  intro f hf a b r
  cases f <;> simp only [FrameArgs, Frame.isFlat] at r hf ⊢
  all_goals first
    | exact r
    | exact ⟨nameAt_frame et hn' r.1, r.2⟩
    | exact nameAt_frame et hn' r
    | exact ShapeCode.frame r es
    | cases hf

theorem tasks_frame_nf {h h' : Buf} {arena : List RN} {fs : List Frame} (r : TasksRep h arena fs) (hnf : fs.all (fun f => !f.isFlat))
    (e5 : bget h' 5 = bget h 5) (er : ∀ i : UInt64, 64 ≤ i.toNat → i.toNat < 64 + 3 * fs.length → bget h' i = bget h i)
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') : TasksRep h' arena fs := by
  obtain ⟨r5, rl, rk⟩ := r
  refine ⟨by rw [e5]; exact r5, rl, fun k hk => ?_⟩
  have tk : taskAt h' (fs.length - 1 - k) = taskAt h (fs.length - 1 - k) :=
    taskAt_frame _ (by omega) (fun c hc => er _ (by rw [taskCell _ (by omega) c hc]; omega) (by rw [taskCell _ (by omega) c hc]; omega))
  have nf : (fs[k]'hk).isFlat = false := by
    have := List.all_eq_true.mp hnf _ (List.getElem_mem hk); simpa using this
  simp only [tk]
  exact ⟨(rk k hk).1, frameArgs_frame_nf et hn es _ nf _ _ (rk k hk).2⟩

/-- **node builder on Rep**: a `v5` that leaves the status nonzero is B's `mkNode` (no flatten frame on the stack) -/
theorem rep_v5g {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (hnf : fs.all (fun f => !f.isFlat))
    (n t A B : Nat) (sh : Option Sh) (p : Bool) (w : UInt64) (hw : ShOpt h w sh) (ht : t < 2 ^ 64)
    (hab : t ≠ 2 → t ≠ 5 → A < 2 ^ 64 ∧ B < 2 ^ 64) (hn : n ≤ 4096)
    (hs : bget (v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (b01 p) n.toUInt64) 0 ≠ 0) :
    ∃ st', mkNode st t A B sh p n = some st' ∧ Rep (v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (b01 p) n.toUInt64) ts st' fs := by
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
  obtain ⟨L, ES, AR, LO, HI, DR⟩ := arena_v5g h st.arena st.vals n t A B sh p w rA hle (by omega) (by omega) (by omega) hw ht hab
  simp only [b01] at hs ⊢
  refine ⟨{ st with vals := RN.mk t A B sh p (st.vals.take n).reverse :: st.vals.drop n, arena := st.arena ++ [RN.mk t A B sh p (st.vals.take n).reverse] },
    by simp [mkNode, hle], ?_⟩
  have rT := r.2.2.2.2.2.2.2.2.2.2.2.2.2
  have e : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 8 → i.toNat ≠ 9 → (i.toNat < 64 ∨ 147520 ≤ i.toNat) →
      bget (v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (if p = true then 1 else 0) n.toUInt64) i = bget h i := by
    intro i a5 a8 a9 hi
    rcases hi with hi | hi
    · exact LO i (by omega) a8 a9
    · exact HI i hi
  have et : TokAgree h (v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (if p = true then 1 else 0) n.toUInt64) :=
    ⟨LO 7 (by decide) (by decide) (by decide), fun i hi => HI i (by omega)⟩
  refine rep_arena r L e DR AR (tasks_arena_ext (tasks_frame_nf rT hnf (LO 5 (by decide) (by decide) (by decide))
    (fun i a b => LO i (by have := rT.2.1; omega) (by omega) (by omega)) et hn7 ES) ⟨_, rfl⟩) rfl

theorem rep_v5 {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (hnf : fs.all (fun f => !f.isFlat))
    (n t A B : Nat) (sh : Option Sh) (p : Bool) (w : UInt64) (hw : ShOpt h w sh) (ht : t < 2 ^ 64) (hA : A < 2 ^ 64)
    (hB : B < 2 ^ 64) (hn : n ≤ 4096) (hs : bget (v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (b01 p) n.toUInt64) 0 ≠ 0) :
    ∃ st', mkNode st t A B sh p n = some st' ∧ Rep (v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (b01 p) n.toUInt64) ts st' fs :=
  rep_v5g r hnf n t A B sh p w hw ht (fun _ _ => ⟨hA, hB⟩) hn hs

/-! ## reading operands -/
theorem ShapeCode.one {h : Buf} {s : Sh} (r : ShapeCode h 1 s) : s = .uw := by
  cases r with
  | uw => rfl
  | pr h1 => simp at h1

theorem shOpt_one {h : Buf} {o : Option Sh} (r : ShOpt h 1 o) : o = some .uw := by
  cases o with
  | none => simp [ShOpt] at r
  | some s => rw [ShapeCode.one r]

/-- operand k (TOP = 0) is represented by the record its stack cell names -/
theorem val_rep {h : Buf} {arena vals : List RN} (r : ArenaRep h arena vals) (k : Nat) (hk : k < vals.length) :
    ∃ ids, RNRep h (opAt h (vals.length - 1 - k)) (vals[k]'hk) ids := by
  obtain ⟨_, _, _, _, I, hI, hR, _, _⟩ := r
  obtain ⟨hr, ea, _⟩ := hR k hk
  have := (hI _ hr).1
  simp only [UInt64.ofNat_toNat, ea] at this
  exact ⟨_, this⟩

/-- the machine's operand cell `d3 + h[8] - (k + 1)` is stack position |vals| - 1 - k -/
theorem opCell {h : Buf} {n : Nat} (h8 : (bget h 8).toNat = n) (hn : n ≤ 4096) (k : Nat) (hk : k < n) :
    bget h (d3 + bget h 8 - (k + 1).toUInt64) = opAt h (n - 1 - k) := by
  simp only [opAt]; congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [tn_add _ _ (by simp [d3v]; omega)]; simp [d3v]; omega)),
    tn_add _ _ (by simp [d3v]; omega), d3k _ (by omega)]
  simp [d3v]; omega

/-- the fields of a represented node -/
theorem RNRep.fields {h : Buf} {u : UInt64} {n : RN} {ids : List UInt64} (r : RNRep h u n ids) :
    fld h u 0 = n.tag.toUInt64 ∧ fld h u 1 = n.a.toUInt64 ∧ fld h u 2 = n.b.toUInt64 ∧ ShOpt h (fld h u 3) n.sh ∧
    fld h u 4 = b01 n.pend := by
  cases r with
  | mk a0 a1 a2 a3 a4 => exact ⟨a0, a1, a2, a3, by rw [a4]; rfl⟩

/-! ## task 5: `mkBin op` (v103) -/
theorem h_mkBin {h ts : Buf} {st : St} {op : Nat} {fs : List Frame} (r : Rep h ts st (.mkBin op :: fs))
    (hnf : fs.all (fun f => !f.isFlat)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.mkBin op) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ea, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [FrameArgs] at ea
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  have ev : step h = (if bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 3) == 1 then
      if bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 2) + 3) == 1 then v5 h1 3 a 0 1 0 2 else bset h1 0 0 else bset h1 0 0) := by
    rw [E]; simp [Frame.code, v96, v103]
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  rw [ev] at hs ⊢
  by_cases c1 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 3) = 1
  · by_cases c2 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 2) + 3) = 1
    · simp only [c1, c2, beq_self_eq_true, if_true] at hs ⊢
      have rA := R1.2.2.2.2.2.2.2.1
      obtain ⟨_, g2, _⟩ := v5_guards _ _ _ _ _ _ _ (by omega) hs
      have g2' := UInt64.lt_iff_toNat_lt.mp g2
      have h8le : (bget h1 8).toNat ≤ 4096 := by rw [rA.2.2.1]; exact rA.2.2.2.1
      rw [tn_add _ _ (by simp; omega)] at g2'
      simp only [show (2 : UInt64).toNat = 2 from rfl, show (1 : UInt64).toNat = 1 from rfl, rA.2.2.1] at g2'
      obtain ⟨y, x, rest, ev2⟩ : ∃ y x rest, st.vals = y :: x :: rest := by
        match hv : st.vals with
        | y :: x :: rest => exact ⟨y, x, rest, rfl⟩
        | [] => simp [hv] at g2'
        | [_] => simp [hv] at g2'
      have h8 := rA.2.2.1
      have o0 := opCell h8 rA.2.2.2.1 0 (by rw [ev2]; simp)
      have o1 := opCell h8 rA.2.2.2.1 1 (by rw [ev2]; simp)
      simp only [show ((0 : Nat) + 1).toUInt64 = 1 from rfl, show ((1 : Nat) + 1).toUInt64 = 2 from rfl] at o0 o1
      have l0 : 0 < st.vals.length := by rw [ev2]; simp
      have l1 : 1 < st.vals.length := by rw [ev2]; simp
      obtain ⟨_, ry⟩ := val_rep rA 0 l0
      obtain ⟨_, rx⟩ := val_rep rA 1 l1
      rw [o0] at c1; rw [o1] at c2
      have fy : ShOpt h1 (bget h1 (d5 + 8 * opAt h1 (st.vals.length - 1 - 0) + 3)) (st.vals[0]'l0).sh := ry.fields.2.2.2.1
      have fx : ShOpt h1 (bget h1 (d5 + 8 * opAt h1 (st.vals.length - 1 - 1) + 3)) (st.vals[1]'l1).sh := rx.fields.2.2.2.1
      rw [c1] at fy; rw [c2] at fx
      have sy := shOpt_one fy; have sx := shOpt_one fx
      simp only [ev2, List.getElem_cons_zero, List.getElem_cons_succ] at sy sx
      have hop : op < 2 ^ 64 := by rw [← ea]; exact a.toNat_lt
      have ea' : a = op.toUInt64 := by rw [← ea]; simp
      subst ea'
      obtain ⟨st', em, R2⟩ := rep_v5 R1 hnf 2 3 op 0 (some .uw) false 1 .uw (by decide) (by omega) (by decide) (by decide)
        (by simpa [b01] using hs)
      refine ⟨[], st', ?_, by simpa [b01] using R2⟩
      simp only [stepF, ev2, sx, sy, and_self, if_true]
      rw [em]; rfl
    · have : (bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 2) + 3) == 1) = false := by simpa using c2
      simp only [c1, this, beq_self_eq_true, if_true] at hs; exact absurd (stat0 _ (by omega)) hs
  · have : (bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 3) == 1) = false := by simpa using c1
    simp only [this] at hs; exact absurd (stat0 _ (by omega)) hs

/-! ## the cursor -/
/-- the token at the cursor, by its first cell -/
theorem tok_cases {h ts : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) (hT : TokensAt h ts) :
    (toks = [] ∧ bget h (d11 + p) = 0) ∨ (∃ v rest, toks = .num v :: rest ∧ bget h (d11 + p) = 5) ∨
    (∃ x rest, toks = .id x :: rest ∧ bget h (d11 + p) = 14) ∨
    (∃ t rest, toks = .k t.toNat :: rest ∧ bget h (d11 + p) = t ∧ t ≠ 0 ∧ t ≠ 5 ∧ t ≠ 14 ∧ TokAt h (p + 1) rest) := by
  cases r with
  | nil e => left; exact ⟨rfl, by rw [e, hT.2.2.2]; exact hT.2.1⟩
  | kw t _ b c d f x =>
    right; right; right
    refine ⟨t, _, rfl, b, fun e => ?_, c, d, x⟩
    subst e; simp [okTag] at f
  | num bs _ b => right; left; exact ⟨_, _, rfl, b⟩
  | id nm a _ => right; right; left; exact ⟨_, _, rfl, a.1⟩

/-- moving the cursor (h[3]) to a position that represents `toks'` -/
theorem rep_set3 {h ts : Buf} {st : St} {fs : List Frame} {q : UInt64} {toks' : List Tok} (r : Rep h ts st fs)
    (hq : TokAt h q toks') : Rep (bset h 3 q) ts { st with toks := toks' } fs := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  have u3 : (3 : UInt64).toNat = 3 := rfl
  have c : ∀ i : UInt64, i.toNat ≠ 3 → bget (bset h 3 q) i = bget h i := fun i hi => bget_bset' _ _ _ _ (by rw [u3]; omega)
  have et : TokAgree h (bset h 3 q) := ⟨c 7 (by decide), fun i hi => c i (by omega)⟩
  refine rep_tok r (length_bset _ _ _) (fun i _ h3 _ => c i h3) (drop_bset _ _ _ (by decide))
    (by rw [bget_bset_eq _ _ _ _ rfl (by rw [u3]; omega)]; exact tokAt_frame et hn hq) ?_ rfl
  exact tasks_frame r.2.2.2.2.2.2.2.2.2.2.2.2.2 (c 5 (by decide)) (fun i a _ => c i (by omega)) et hn
    (fun i a _ => c i (by omega)) (fun i a _ => c i (by omega)) har

/-! ## operator tables: `y8` / `y10` = `opInfo` -/
theorem op_corr (t : UInt64) :
    (y8 t = 0 ∧ opInfo t.toNat = none) ∨
    ∃ op p, opInfo t.toNat = some (op, p) ∧ y8 t = op.toUInt64 ∧ y10 t = p.toUInt64 ∧ 1 ≤ op ∧ op ≤ 7 ∧ p ≤ 75 ∧
      ((op = 6 ∨ op = 7) ↔ (t = 28 ∨ t = 29)) := by
  by_cases e27 : t = 27; · subst e27; right; exact ⟨5, 55, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  by_cases e26 : t = 26; · subst e26; right; exact ⟨4, 60, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  by_cases e10 : t = 10; · subst e10; right; exact ⟨1, 65, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  by_cases e11 : t = 11; · subst e11; right; exact ⟨2, 65, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  by_cases e12 : t = 12; · subst e12; right; exact ⟨3, 70, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  by_cases e28 : t = 28; · subst e28; right; exact ⟨6, 75, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  by_cases e29 : t = 29; · subst e29; right; exact ⟨7, 75, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  left
  have tn : ∀ c : UInt64, ¬ t = c → t.toNat ≠ c.toNat := fun c h e => h (UInt64.toNat_inj.mp e)
  have n27 := tn 27 e27; have n26 := tn 26 e26; have n10 := tn 10 e10; have n11 := tn 11 e11; have n12 := tn 12 e12
  have n28 := tn 28 e28; have n29 := tn 29 e29
  simp only [show (27 : UInt64).toNat = 27 from rfl, show (26 : UInt64).toNat = 26 from rfl, show (10 : UInt64).toNat = 10 from rfl,
    show (11 : UInt64).toNat = 11 from rfl, show (12 : UInt64).toNat = 12 from rfl, show (28 : UInt64).toNat = 28 from rfl,
    show (29 : UInt64).toNat = 29 from rfl] at n27 n26 n10 n11 n12 n28 n29
  refine ⟨by simp [y8, e27, e26, e10, e11, e12, e28, e29], ?_⟩
  unfold opInfo
  split <;> first | rfl | omega

/-! ## task 2: `binLoop m` (v101) -/
theorem v101_eq (h : Buf) (a b : UInt64) : v101 h a b =
    (if y8 (bget h (d11 + bget h 3)) == 0 then h else if y10 (bget h (d11 + bget h 3)) < a then h else
      if bget h (d5 + 8 * bget h (d3 + bget h 8 - 1) + 4) == 0 then
        (if y8 (bget h (d11 + bget h 3)) == 6 ∨ y8 (bget h (d11 + bget h 3)) == 7 then
          v1 (v1 (bset h 3 (bget h 3 + 1)) 2 a 0) 49 (y8 (bget h (d11 + bget h 3))) 0
        else v1 (v1 (v1 (bset h 3 (bget h 3 + 1)) 2 a 0) 5 (y8 (bget h (d11 + bget h 3))) 0) 1 (y10 (bget h (d11 + bget h 3)) + 1) 2)
      else bset h 0 0) := by
  simp only [v101, UInt64.add_zero]
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> (try rfl)
  rename_i h6
  by_cases e6 : y8 (bget h (d11 + bget h 3)) = 6
  · simp [e6]
  · by_cases e7 : y8 (bget h (d11 + bget h 3)) = 7
    · simp [e7]
    · simp [e6, e7]

/-- the remaining (unfold-free) part of binLoop: no operator / weaker operator ⇒ nothing happens -/
theorem h_binLoop {h ts : Buf} {st : St} {m : Nat} {fs : List Frame} (r : Rep h ts st (.binLoop m :: fs))
    (hv : st.vals ≠ []) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.binLoop m) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ea, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  simp only [FrameArgs] at ea
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  have ev : step h = v101 h1 a b := by rw [E]; simp [Frame.code, v96]
  rw [ev, v101_eq] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have p3 := R1.2.2.2.1
  -- the "nothing to do" outcome
  have idle : ∀ (hst : stepF (.binLoop m) st = some ([], st)), ∃ k st', stepF (.binLoop m) st = some (k, st') ∧ Rep h1 ts st' (k ++ fs) :=
    fun hst => ⟨[], st, hst, R1⟩
  rcases tok_cases p3 R1.1 with ⟨et, hc⟩ | ⟨v, rest, et, hc⟩ | ⟨x, rest, et, hc⟩ | ⟨t, rest, et, hc, t0, t5, t14, tr⟩
  · rw [hc] at hs ⊢; simp only [show y8 0 = 0 from rfl, beq_self_eq_true, if_true]
    exact idle (by simp [stepF, et])
  · rw [hc] at hs ⊢; simp only [show y8 5 = 0 from rfl, beq_self_eq_true, if_true]
    exact idle (by simp [stepF, et])
  · rw [hc] at hs ⊢; simp only [show y8 14 = 0 from rfl, beq_self_eq_true, if_true]
    exact idle (by simp [stepF, et])
  · rw [hc] at hs ⊢
    rcases op_corr t with ⟨y0, oi⟩ | ⟨op, pr, oi, yo, yp, o1, o7, p75, osh⟩
    · simp only [y0, beq_self_eq_true, if_true]
      exact idle (by simp [stepF, et, oi])
    · have yn : (y8 t == 0) = false := by
        rw [yo]; apply beq_false_of_ne; intro e; have := congrArg UInt64.toNat e
        rw [show (0 : UInt64).toNat = 0 from rfl] at this; simp at this; omega
      simp only [yn, if_false] at hs ⊢
      rw [yp] at hs ⊢
      by_cases lt : pr.toUInt64 < a
      · simp only [lt, if_true]
        have pe : pr.toUInt64.toNat = pr := by simp; omega
        have : pr < m := by have := UInt64.lt_iff_toNat_lt.mp lt; rw [pe] at this; omega
        exact idle (by simp [stepF, et, oi, this])
      · simp only [lt, if_false] at hs ⊢
        have pe : pr.toUInt64.toNat = pr := by simp; omega
        have nlt : ¬ pr < m := by
          intro c; apply lt; apply UInt64.lt_iff_toNat_lt.mpr; rw [pe]; omega
        obtain ⟨top, vs, evs⟩ : ∃ top vs, st.vals = top :: vs := by
          match hq : st.vals with
          | [] => exact absurd hq hv
          | top :: vs => exact ⟨top, vs, rfl⟩
        have rA := R1.2.2.2.2.2.2.2.1
        have l0 : 0 < st.vals.length := by rw [evs]; simp
        have o0 := opCell rA.2.2.1 rA.2.2.2.1 0 l0
        simp only [show ((0 : Nat) + 1).toUInt64 = 1 from rfl] at o0
        obtain ⟨_, rt⟩ := val_rep rA 0 l0
        have fp : bget h1 (d5 + 8 * opAt h1 (st.vals.length - 1 - 0) + 4) = b01 (st.vals[0]'l0).pend := rt.fields.2.2.2.2
        rw [o0, fp] at hs ⊢
        simp only [evs, List.getElem_cons_zero] at hs ⊢
        cases hp : top.pend with
        | true => simp only [hp, b01] at hs; simp at hs; exact absurd (stat0 _ (by omega)) hs
        | false =>
          simp only [hp, b01, Bool.false_eq_true, if_false, beq_self_eq_true, if_true] at hs ⊢
          have R2 := rep_set3 R1 tr
          have p0 : ¬ (pr < m) := nlt
          rw [yo] at hs ⊢
          by_cases sh : op = 6 ∨ op = 7
          · have c : (op.toUInt64 == 6 ∨ op.toUInt64 == 7) := by rcases sh with e | e <;> subst e <;> simp
            simp only [c, if_true] at hs ⊢
            have tsh := osh.mp sh
            have tsh' : t.toNat = 28 ∨ t.toNat = 29 := by rcases tsh with e | e <;> subst e <;> simp
            have R3 : Rep (v1 (bset h1 3 (bget h1 3 + 1)) 2 a 0) ts { st with toks := rest } (.binLoop m :: fs) :=
              rep_push (.binLoop m) a 0 R2 (by simp [inDefF, Frame.isDefs]) ea (fun z => hs (v1_zero _ _ _ _ z))
            have R4 : Rep (v1 (v1 (bset h1 3 (bget h1 3 + 1)) 2 a 0) 49 op.toUInt64 0) ts { st with toks := rest }
                (.shiftNum op :: .binLoop m :: fs) :=
              rep_push (.shiftNum op) op.toUInt64 0 R3 (by simp [inDefF, Frame.isDefs]) (by simp [FrameArgs]; omega) hs
            refine ⟨[.shiftNum op, .binLoop m], _, ?_, R4⟩
            simp [stepF, et, oi, p0, evs, hp, tsh']
          · have c : ¬ (op.toUInt64 == 6 ∨ op.toUInt64 == 7) := by
              intro e; apply sh
              rcases e with e | e
              · left; have := congrArg UInt64.toNat (eq_of_beq e); simp at this; omega
              · right; have := congrArg UInt64.toNat (eq_of_beq e); simp at this; omega
            simp only [c, if_false] at hs ⊢
            have tsh' : ¬ (t.toNat = 28 ∨ t.toNat = 29) := by
              intro e; apply sh; apply osh.mpr
              rcases e with e | e
              · left; exact UInt64.toNat_inj.mp (by simpa using e)
              · right; exact UInt64.toNat_inj.mp (by simpa using e)
            have R3 : Rep (v1 (bset h1 3 (bget h1 3 + 1)) 2 a 0) ts { st with toks := rest } (.binLoop m :: fs) :=
              rep_push (.binLoop m) a 0 R2 (by simp [inDefF, Frame.isDefs]) ea (fun z => hs (v1_zero _ _ _ _ (v1_zero _ _ _ _ z)))
            have R4 : Rep (v1 (v1 (bset h1 3 (bget h1 3 + 1)) 2 a 0) 5 op.toUInt64 0) ts { st with toks := rest }
                (.mkBin op :: .binLoop m :: fs) :=
              rep_push (.mkBin op) op.toUInt64 0 R3 (by simp [inDefF, Frame.isDefs]) (by simp [FrameArgs]; omega)
                (fun z => hs (v1_zero _ _ _ _ z))
            have R5 : Rep (v1 (v1 (v1 (bset h1 3 (bget h1 3 + 1)) 2 a 0) 5 op.toUInt64 0) 1 (pr.toUInt64 + 1) 2) ts
                { st with toks := rest } (.expr (pr + 1) 2 :: .mkBin op :: .binLoop m :: fs) :=
              rep_push (.expr (pr + 1) 2) (pr.toUInt64 + 1) 2 R4 (by simp [inDefF, Frame.isDefs])
                (by simp only [FrameArgs]; refine ⟨?_, rfl⟩; rw [tn_add _ _ (by simp; omega)]; simp; omega) hs
            refine ⟨[.expr (pr + 1) 2, .mkBin op, .binLoop m], _, ?_, R5⟩
            simp [stepF, et, oi, p0, evs, hp, tsh']

end ParInv
