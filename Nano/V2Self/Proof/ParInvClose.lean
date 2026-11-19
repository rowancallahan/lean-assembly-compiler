/- Nano/V2Self/Proof/ParInvClose: task 83 (`v144`, close a def) on box C's Rep (parser lead).  The open row becomes the last finished
row (h[12] + 1), `.defs` is pushed, `21` appended. -/
import Nano.V2Self.Proof.ParInvHdr
import Nano.V2Self.Proof.ParInvAssign
namespace ParInv
open C BufL ParSpec ParRun

theorem shRows_frame {g g1 : Buf} (r : ShRows g) (e26 : bget g1 26 = bget g 26)
    (e : ∀ i : UInt64, 155712 ≤ i.toNat → bget g1 i = bget g i) : ShRows g1 := by
  have es : ShTabAgree g g1 := fun i a _ => e i a
  obtain ⟨r1, r2, r3⟩ := r
  have ek : ∀ k : Nat, k < 8192 → ∀ q : UInt64, q.toNat < 3 →
      bget g1 (d7 + 8192 + 3 * k.toUInt64 + q) = bget g (d7 + 8192 + 3 * k.toUInt64 + q) := fun k hk q hq =>
    e _ (by
      rw [UInt64.toNat_add, pairCell0 k hk, Nat.mod_eq_of_lt (by omega)]; omega)
  refine ⟨by rw [e26]; exact r1, fun k h1 h2 => ?_, fun k hk => ?_⟩
  · rw [e26] at h1; have := ek k h2 0 (by decide); simp only [UInt64.add_zero] at this; rw [this]; exact r2 k h1 h2
  · rw [e26] at hk
    obtain ⟨l, r, a1, a2, a3, a4, a5⟩ := r3 k hk
    have hk' : k < 8192 := by omega
    have e0 := ek k hk' 0 (by decide); simp only [UInt64.add_zero] at e0
    exact ⟨l, r, by rw [e0]; exact a1.frame es, by rw [ek k hk' 1 (by decide)]; exact a2.frame es,
      by rw [ek k hk' 2 (by decide)]; exact a3, a4, a5⟩

/-- **closing the open row**: with h[12] incremented, the open row is the last finished one -/
theorem defsRep_close {g g1 : Buf} {st : St} (rD : DefsRep g st true) (e12 : bget g1 12 = bget g 12 + 1)
    (e : ∀ i : UInt64, i.toNat ≠ 12 → bget g1 i = bget g i) (et : TokAgree g g1) (hn : (bget g 7).toNat < 2 ^ 32) :
    DefsRep g1 { st with defs := st.defs ++ [st.cur] } false := by
  obtain ⟨d12, dle, d27, drows, dcur, dz, d0, dsr⟩ := rD
  simp only [if_true] at dcur
  obtain ⟨⟨crow, cs⟩, clt⟩ := dcur
  have es : ShTabAgree g g1 := fun i a _ => e i (by omega)
  have c27 : bget g1 27 = bget g 27 := e 27 (by decide)
  have rowF : ∀ j (hj : j < 512) (d : DefR), RowRep g j d → RowRep g1 j d := fun j hj d r =>
    rowRep_frame'' hj r (fun k hk => e _ (by rw [defCell j hj k hk]; omega))
      (fun i hi => e _ (by
        have := r.2.2.2.2.2.2.1
        rw [parCell _ i (by omega)]; omega)) et hn es
  refine ⟨?_, by simp; omega, by rw [c27]; exact d27, fun j hj => ?_, ?_, fun j h1 h2 => ?_, fun i h1 h2 => ?_, ?_⟩
  · rw [e12]; simp only [List.length_append, List.length_singleton]
    rw [UInt64.toNat_add]; simp; omega
  · have hj' : j < st.defs.length + 1 := by simpa using hj
    by_cases hjl : j < st.defs.length
    · obtain ⟨rr, rs⟩ := drows j hjl
      have eg : ({ st with defs := st.defs ++ [st.cur] }.defs[j]'hj) = st.defs[j]'hjl := List.getElem_append_left hjl
      rw [eg, c27, e _ (by rw [defCell j (by omega) 5 (by decide)]; simp; omega)]
      exact ⟨rowF j (by omega) _ rr, rs⟩
    · have hje : j = st.defs.length := by omega
      subst hje
      have eg : ({ st with defs := st.defs ++ [st.cur] }.defs[st.defs.length]'hj) = st.cur := by simp
      rw [eg, c27, e _ (by rw [defCell _ (by omega) 5 (by decide)]; simp; omega)]
      exact ⟨rowF _ (by omega) _ crow, by omega⟩
  · simp only [Bool.false_eq_true, if_false, List.length_append, List.length_singleton]
    intro hlt k hk
    rw [e _ (by rw [defCell _ (by omega) k hk]; omega)]
    exact dz _ (by omega) (by omega) k hk
  · simp only [List.length_append, List.length_singleton] at h1
    intro k hk
    rw [e _ (by rw [defCell _ (by omega) k hk]; omega)]
    exact dz j (by omega) h2 k hk
  · rw [c27] at h1
    rw [e _ (by rw [parCell0 i (by omega)]; omega)]
    exact d0 i h1 h2
  · exact shRows_frame dsr (e 26 (by decide)) (fun i hi => e i (by omega))


/-- the between-defs representation ignores h[5] and the task region -/
theorem repZ_frameT {h h' ts : Buf} {st : St} (r : RepZ h ts st)
    (e : ∀ i : UInt64, i.toNat ≠ 5 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) → bget h' i = bget h i)
    (ed : h'.drop 184384 = h.drop 184384) : RepZ h' ts st := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have c : ∀ n : UInt64, n.toNat < 64 → n.toNat ≠ 5 → bget h' n = bget h n := fun n a b => e n b (Or.inl a)
  have et : TokAgree h h' := ⟨c 7 (by decide) (by decide), fun i hi => e i (by omega) (Or.inr (by omega))⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (Or.inr (by omega))
  exact ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide)]; exact r0,
    by rw [c 3 (by decide) (by decide)]; exact tokAt_frame et hn r3, by rw [c 11 (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide)) (fun i a _ => e i (by omega) (Or.inr (by omega))) et hn es,
    defs_frame rD (c 12 (by decide) (by decide)) (c 27 (by decide) (by decide)) (c 26 (by decide) (by decide))
      (fun i a _ => e i (by omega) (Or.inr (by omega))) et hn es,
    arena_frame rA (c 8 (by decide) (by decide)) (c 9 (by decide) (by decide)) (fun i a _ => e i (by omega) (Or.inr (by omega))) es,
    fun s hs => by rw [c 25 (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx => by rw [c 29 (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [c 30 (by decide) (by decide)]; exact r30, by rw [c 32 (by decide) (by decide)]; exact r32, out_frame rO ed⟩

theorem rep_of_repZ {h ts : Buf} {st : St} (R : RepZ h ts st) (T : TasksRep h st.arena [.defs]) : Rep h ts st [.defs] :=
  ⟨R.1, R.2.1, R.2.2.1, R.2.2.2.1, R.2.2.2.2.1, R.2.2.2.2.2.1, R.2.2.2.2.2.2.1, R.2.2.2.2.2.2.2.1, R.2.2.2.2.2.2.2.2.1,
    R.2.2.2.2.2.2.2.2.2.1, R.2.2.2.2.2.2.2.2.2.2.1, R.2.2.2.2.2.2.2.2.2.2.2.1, R.2.2.2.2.2.2.2.2.2.2.2.2, T⟩

/-- **task 83** (close a def): the open row is finished, `.defs` pushed, `21` emitted -/
theorem h_defClose {h ts : Buf} {st : St} (r : Rep h ts st [.defClose]) :
    ∃ k st', stepF .defClose st = some (k, st') ∧ Rep (step h) ts st' k := by
  obtain ⟨E, _, R1⟩ := rep_pop (fs := []) r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h ([] : List Frame).length).a = a at E
  generalize (taskAt h ([] : List Frame).length).b = b at E
  generalize bset h 5 ([] : List Frame).length.toUInt64 = g at E R1
  obtain ⟨hn, hlen, har⟩ := rep_bounds R1
  have ev : step h = v144 g a b := by rw [E]; rfl
  rw [v144_eq g a b (by omega)] at ev
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := R1
  have rD' : DefsRep g st true := rD
  have d512 : st.defs.length < 512 := by
    have := rD'.2.2.2.2.1; simp only [if_true] at this; exact this.2
  generalize hg1 : bset g 12 (bget g 12 + 1) = g1 at ev
  have e : ∀ i : UInt64, i.toNat ≠ 12 → bget g1 i = bget g i := fun i hi => by rw [← hg1]; exact bget_bset' _ _ _ _ (by simp; omega)
  have e12 : bget g1 12 = bget g 12 + 1 := by rw [← hg1]; exact bget_bset_eq _ _ _ _ rfl (by simp; omega)
  have l1 : g1.length = g.length := by rw [← hg1, length_bset]
  have et : TokAgree g g1 := ⟨e 7 (by decide), fun i hi => e i (by omega)⟩
  have es : ShTabAgree g g1 := fun i a _ => e i (by omega)
  have RZ : RepZ g1 ts { st with defs := st.defs ++ [st.cur] } :=
    ⟨tokensAt_frame rT et rts, rts, by rw [e 0 (by decide)]; exact r0, by rw [e 3 (by decide)]; exact tokAt_frame et hn r3,
      by rw [e 11 (by decide)]; exact r11,
      binds_frame rB (e 4 (by decide)) (fun i a _ => e i (by omega)) et hn es,
      defsRep_close rD' e12 e et hn,
      arena_frame rA (e 8 (by decide)) (e 9 (by decide)) (fun i a _ => e i (by omega)) es,
      fun s hs => by rw [e 25 (by decide)]; exact (r25 s hs).frame es,
      fun x hx => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
      by rw [e 30 (by decide)]; exact r30, by rw [e 32 (by decide)]; exact r32,
      out_frame rO (by rw [← hg1]; exact drop_bset _ _ _ (by decide))⟩
  have T1 : TasksRep g1 st.arena [] := tasks_frame rK (e 5 (by decide)) (fun i a b => by simp at b; omega) et hn es
    (fun i a b => e i (by omega)) har
  have T2 := tasks_push .defs 0 0 T1 (by decide) (by omega) (by rw [e 7 (by decide)]; exact hn) har trivial
  have hg5 : (bget g1 5).toNat = 0 := by rw [T1.1]; rfl
  have hg : (bget g1 5).toNat < 4096 := by omega
  obtain ⟨L, _, _, U⟩ := v1_eff g1 (Frame.defs).code.toUInt64 0 0 hg (by omega)
  have RZ2 := repZ_frameT RZ (fun i a b => U i a (by rw [hg5]; rcases b with b | b <;> omega))
    (drop_v1 _ _ _ _ (by omega))
  have R2 := rep_of_repZ RZ2 T2
  exact ⟨[.defs], _, rfl, by rw [ev]; exact rep_append R2 [21]⟩


/-- the popped heap agrees with the old one off cell 5, so frame arguments transfer -/
theorem frameArgs_pop {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (v : UInt64) {f : Frame} {a b : UInt64}
    (hf : FrameArgs h st.arena f a b) : FrameArgs (bset h 5 v) st.arena f a b := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  have e : ∀ i : UInt64, i.toNat ≠ 5 → bget (bset h 5 v) i = bget h i := fun i hi => bget_bset' _ _ _ _ (by simp; omega)
  exact frameArgs_frame ⟨e 7 (by decide), fun i hi => e i (by omega)⟩ hn (fun i a _ => e i (by omega)) (fun i a _ => e i (by omega))
    har f a b hf

/-- **task 82** (flatten a sibling chain): an input local is skipped, any other node is flattened (task 81) before the rest -/
theorem h_flatL {h ts : Buf} {st : St} {ns : List RN} {fs : List Frame} (r : Rep h ts st (.flatL ns :: fs))
    (hfs : inDefF fs = true) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.flatL ns) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, FA, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  have FA' := frameArgs_pop r fs.length.toUInt64 FA
  generalize (taskAt h fs.length).a = a at E FA'
  generalize (taskAt h fs.length).b = b at E FA'
  generalize bset h 5 fs.length.toUInt64 = g at E R1 FA'
  have ev : step h = v143 g a b := by rw [E]; rfl
  rw [ev, v143_eq] at hs ⊢
  obtain ⟨hb, ids, hK, hids⟩ := FA'
  cases ns with
  | nil =>
    have : b = 0 := UInt64.toNat_inj.mp (by simpa using hb)
    subst this
    exact ⟨[], st, rfl, by simpa using R1⟩
  | cons n rest =>
    have hb0 : b ≠ 0 := fun e => by subst e; simp at hb
    simp only [hb0, if_false] at hs ⊢
    cases hK with
    | cons hn hrest =>
      rename_i i1 ids'
      have hb1 : (b - 1).toNat = rest.length := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp at hb ⊢; omega))]; simp at hb ⊢; omega
      have FAr : FrameArgs g st.arena (.flatL rest) (fld g a 7) (b - 1) :=
        ⟨hb1, ids', hrest, fun v hv => hids v (List.mem_append_right _ hv)⟩
      rw [inpC_isInp isInpW hn] at hs ⊢
      by_cases hi : n.isInp
      · simp only [hi, if_true] at hs ⊢
        exact ⟨[.flatL rest], st, by simp [stepF, hi], rep_push (.flatL rest) _ _ R1 (by simp [inDefF, Frame.isDefs, hfs]) FAr hs⟩
      · simp only [hi, Bool.false_eq_true, if_false, show ((0 : UInt64) = 1) = False from by decide] at hs ⊢
        have hs1 : bget (v1 g 82 (fld g a 7) (b - 1)) 0 ≠ 0 := fun e => hs (v1_zero _ _ _ _ e)
        have R2 := rep_push (.flatL rest) _ _ R1 (by simp [inDefF, Frame.isDefs, hfs]) FAr hs1
        obtain ⟨hn7, hlg, har⟩ := rep_bounds R1
        have hg := v1_ok _ _ _ _ hs1
        obtain ⟨et, es, ea⟩ := v1_agree g 82 (fld g a 7) (b - 1) hg (by omega)
        have FAn : FrameArgs g st.arena (.flat n) a 0 := ⟨i1, hn, fun v hv => hids v (List.mem_append_left _ hv)⟩
        have R3 := rep_push (.flat n) a 0 R2 (by simp [inDefF, Frame.isDefs])
          (frameArgs_frame et hn7 es ea har _ _ _ FAn) hs
        exact ⟨[.flat n, .flatL rest], st, by simp [stepF, hi], R3⟩

end ParInv
