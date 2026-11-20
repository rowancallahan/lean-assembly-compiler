/- Nano/V2Self/Proof/Parser/ParInvShP: frame rules under SHAPE-CODE PRESERVATION (box G).  `v10`'s allocation writes a new pair row, so the
whole-table agreement `ShTabAgree` fails across it; what survives is `ShPres h h'` (every shape code of `h` decodes to the same shape
in `h'`).  This file restates the component frame rules of ParInvRep / ParInvStep for `ShPres` (same proofs), and proves
`shPres_alloc`: rows below h[26] unchanged ⇒ `ShPres` (an unallocated row has left code 0, so no code refers to it). -/
import Nano.V2Self.Proof.Parser.ParInvAssign
namespace ParInv
open C BufL ParSpec ParRun

/-- every shape code keeps its meaning -/
def ShPres (h h' : Buf) : Prop := ∀ (c : UInt64) (s : Sh), ShapeCode h c s → ShapeCode h' c s

theorem ShOpt.pres {h h' : Buf} {c : UInt64} {o : Option Sh} (r : ShOpt h c o) (e : ShPres h h') : ShOpt h' c o := by
  cases o with
  | none => exact r
  | some s => exact e _ _ r

mutual
theorem RNRep.frameP {h h' : Buf} {u : UInt64} {n : ParRun.RN} {ids : List UInt64} (r : RNRep h u n ids)
    (e0 : ∀ k : UInt64, k.toNat < 7 → fld h' u k = fld h u k) (e : RecAgree h h' ids.tail) (es : ShPres h h') :
    RNRep h' u n ids := by
  have g : ∀ k : UInt64, k.toNat < 7 → fld h u k = fld h' u k := fun k hk => (e0 k hk).symm
  match r with
  | .mk a0 a1 a2 a3 a4 a6 x y k =>
    exact .mk (by rw [← g 0 (by decide)]; exact a0) (by rw [← g 1 (by decide)]; exact a1) (by rw [← g 2 (by decide)]; exact a2)
      (by rw [← g 3 (by decide)]; exact a3.pres es) (by rw [← g 4 (by decide)]; exact a4) (by rw [← g 6 (by decide)]; exact a6) x y
      (by rw [← g 5 (by decide)]; exact k.frameP e es)

theorem KidsR.frameP {h h' : Buf} {f : UInt64} {ns : List ParRun.RN} {ids : List UInt64} (r : KidsR h f ns ids)
    (e : RecAgree h h' ids) (es : ShPres h h') : KidsR h' f ns ids := by
  match r with
  | .nil => exact .nil
  | .cons (i1 := i1) nr k =>
    have hm : f ∈ i1 := nr.mem
    have g : ∀ k : UInt64, k.toNat < 8 → fld h' f k = fld h f k := e f (List.mem_append_left _ hm)
    exact .cons (nr.frameP (fun k hk => g k (by omega)) (fun v hv => e v (List.mem_append_left _ (List.mem_of_mem_tail hv))) es)
      (by rw [g 7 (by decide)]; exact k.frameP (fun v hv => e v (List.mem_append_right _ hv)) es)
end

theorem arena_frameP {h h' : Buf} {arena vals : List RN} (r : ArenaRep h arena vals) (e8 : bget h' 8 = bget h 8)
    (e9 : bget h' 9 = bget h 9) (er : RegAgree h h' 12352 147520) (es : ShPres h h') : ArenaRep h' arena vals := by
  obtain ⟨r9, ral, r8, rvl, I, hI, hR, hD, hX⟩ := r
  have ea : ArenaAgree h h' := fun i a b => er i (by omega) b
  have op : ∀ k, k < 4096 → opAt h' k = opAt h k := fun k hk => er _ (by rw [d3k k hk]; omega) (by rw [d3k k hk]; omega)
  refine ⟨by rw [e9]; exact r9, ral, by rw [e8]; exact r8, rvl, I, fun u hu => ?_, fun k hk => ?_, fun k1 k2 h1 h2 e => ?_,
    fun k1 k2 h1 h2 h12 => ?_⟩
  · obtain ⟨a, b, c⟩ := hI u hu
    obtain ⟨t, et⟩ := a.head
    refine ⟨a.frameP (fun k hk => ?_) (recAgree_of ea (fun v hv => ?_)) es, b, c⟩
    · have hu' : (u.toUInt64).toNat = u := by simp; omega
      show bget h' _ = bget h _
      exact ea _ (by rw [recK _ k (by omega) (by omega)]; omega) (by rw [recK _ k (by omega) (by omega)]; omega)
    · have := c v (List.mem_of_mem_tail hv); omega
  · simp only [op (vals.length - 1 - k) (by omega)]; exact hR k hk
  · rw [op _ (by omega), op _ (by omega)] at e; exact hD k1 k2 h1 h2 e
  · rw [op _ (by omega), op _ (by omega)]; exact hX k1 k2 h1 h2 h12

theorem frameArgs_frameP {h h' : Buf} {arena : List RN} (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32)
    (es : ShPres h h') (ea : ArenaAgree h h') (har : arena.length ≤ 16384) :
    ∀ (f : Frame) (a b : UInt64), FrameArgs h arena f a b → FrameArgs h' arena f a b := by
  have hn' : (bget h 7).toNat < 2 ^ 40 := by omega
  intro f a b r
  cases f <;> simp only [FrameArgs] at r ⊢
  all_goals first
    | exact r
    | exact ⟨nameAt_frame et hn' r.1, r.2⟩
    | exact nameAt_frame et hn' r
    | exact es _ _ r
    | (obtain ⟨r1, ids, k, kb⟩ := r
       exact ⟨r1, ids, k.frameP (recAgree_of ea (fun v hv => by have := kb v hv; omega)) es, kb⟩)
    | (obtain ⟨ids, k, kb⟩ := r
       have hb : ∀ v ∈ ids, v.toNat < 16384 := fun v hv => by have := kb v hv; omega
       exact ⟨ids, k.frameP (fun q hq => recAgree_of ea hb _ k.mem q (by omega))
         (fun v hv q hq => recAgree_of ea hb v (List.mem_of_mem_tail hv) q hq) es, kb⟩)

theorem tasks_frameP {h h' : Buf} {arena : List RN} {fs : List Frame} (r : TasksRep h arena fs) (e5 : bget h' 5 = bget h 5)
    (er : ∀ i : UInt64, 64 ≤ i.toNat → i.toNat < 64 + 3 * fs.length → bget h' i = bget h i)
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShPres h h') (ea : ArenaAgree h h') (har : arena.length ≤ 16384) :
    TasksRep h' arena fs := by
  obtain ⟨r5, rl, rk⟩ := r
  refine ⟨by rw [e5]; exact r5, rl, fun k hk => ?_⟩
  have tk : taskAt h' (fs.length - 1 - k) = taskAt h (fs.length - 1 - k) :=
    taskAt_frame _ (by omega) (fun c hc => er _ (by rw [taskCell _ (by omega) c hc]; omega) (by rw [taskCell _ (by omega) c hc]; omega))
  simp only [tk]
  exact ⟨(rk k hk).1, frameArgs_frameP et hn es ea har _ _ _ (rk k hk).2⟩

theorem binds_frameP {h h' : Buf} {bs : List Bd} (r : BindsRep h bs) (e4 : bget h' 4 = bget h 4) (er : RegAgree h h' 180288 184384)
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShPres h h') : BindsRep h' bs := by
  obtain ⟨r4, rl, rk⟩ := r
  refine ⟨by rw [e4]; exact r4, rl, fun i hi => ?_⟩
  have c : ∀ k : UInt64, k.toNat < 4 → bget h' (d9 + 4 * i.toUInt64 + k) = bget h (d9 + 4 * i.toUInt64 + k) :=
    fun k hk => er _ (by rw [rowCell i (by omega) k hk]; omega) (by rw [rowCell i (by omega) k hk]; omega)
  have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
  obtain ⟨a0, a1, a2, a3⟩ := rk i hi
  exact ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1, by rw [c 2 (by decide)]; exact a2.pres es,
    by rw [c 3 (by decide)]; exact a3⟩

theorem row_frameP {h h' : Buf} {j : Nat} {d : DefR} (hj : j < 512) (r : RowRep h j d) (er : RegAgree h h' 147520 155712)
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShPres h h') : RowRep h' j d := by
  have c : ∀ k : UInt64, k.toNat < 8 → bget h' (d7 + 8 * j.toUInt64 + k) = bget h (d7 + 8 * j.toUInt64 + k) :=
    fun k hk => er _ (by rw [defCell j hj k hk]; omega) (by rw [defCell j hj k hk]; omega)
  have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
  obtain ⟨a0, a1, a2, a3, a4, a6, a5, ap⟩ := r
  refine ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1, by rw [c 2 (by decide)]; exact a2,
    by rw [c 3 (by decide)]; exact a3.pres es, by rw [c 4 (by decide)]; exact a4, by rw [c 6 (by decide)]; exact a6,
    by rw [c 5 (by decide)]; exact a5, fun i hi => ?_⟩
  rw [c 5 (by decide), er _ (by rw [parCell _ _ (by omega)]; omega) (by rw [parCell _ _ (by omega)]; omega)]
  exact es _ _ (ap i hi)

/-- the def table (all but the pair-table part) under shape-code preservation -/
theorem defs_frameP {h h' : Buf} {st : St} {b : Bool} (r : DefsRep h st b) (e12 : bget h' 12 = bget h 12) (e27 : bget h' 27 = bget h 27)
    (er : RegAgree h h' 147520 155712) (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShPres h h') (hsr : ShRows h') :
    DefsRep h' st b := by
  have hlen := r.len
  obtain ⟨r12, rl, r27, rd, rc, rz, r0, _, rH⟩ := r
  have c5 : ∀ j, j < 512 → bget h' (d7 + 8 * j.toUInt64 + 5) = bget h (d7 + 8 * j.toUInt64 + 5) :=
    fun j hj => er _ (by rw [defCell j hj 5 (by decide), show (5 : UInt64).toNat = 5 from rfl]; omega)
      (by rw [defCell j hj 5 (by decide), show (5 : UInt64).toNat = 5 from rfl]; omega)
  have zr : ∀ j, j < 512 → RowZero h j → RowZero h' j := fun j hj z k hk => by
    rw [er _ (by rw [defCell j hj k hk]; omega) (by rw [defCell j hj k hk]; omega)]; exact z k hk
  refine ⟨by rw [e12]; exact r12, rl, by rw [e27]; exact r27, fun j hj => ⟨row_frameP (by omega) (rd j hj).1 er et hn es,
    by rw [c5 j (by omega), e27]; exact (rd j hj).2⟩, ?_, fun j h1 h2 => zr j h2 (rz j h1 h2),
    fun i h1 h2 => by rw [er _ (by rw [parCell0 i h2]; omega) (by rw [parCell0 i h2]; omega)]; exact r0 i (by rw [← e27]; exact h1) h2,
    hsr, hashRep_frame hlen rH (fun i a _ => et.2 i a)
      (fun i hi => er _ (by rw [slot7Cell i hi]; omega) (by rw [slot7Cell i hi]; omega))⟩
  cases b with
  | true =>
    simp only [if_true] at rc ⊢
    have hl := rc.2
    exact ⟨⟨row_frameP hl rc.1.1 er et hn es, by rw [c5 _ hl, e27]; exact rc.1.2⟩, hl⟩
  | false => simp only [Bool.false_eq_true, if_false] at rc ⊢; exact fun hl => zr _ hl (rc hl)

/-- **allocation frame**: if the pair rows below `n` are unchanged and every row from `n` on had a zero left cell, all shape codes
keep their meaning (no code can refer to a row ≥ n: its left component would be code 0) -/
theorem shPres_alloc {g G : Buf} (n : Nat) (hz : ∀ k : Nat, n ≤ k → k < 8192 → bget g (d7 + 8192 + 3 * k.toUInt64) = 0)
    (hag : ∀ i : UInt64, 155712 ≤ i.toNat → i.toNat < 155712 + 3 * n → bget G i = bget g i) : ShPres g G := by
  intro c s r
  induction r with
  | uw => exact .uw
  | bf => exact .bf
  | ls => exact .ls
  | nt => exact .nt
  | @pr c l r a b h5 hlt el er ew sa sb iha ihb =>
    have ck : c - 5 = (c.toNat - 5).toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hk : c.toNat - 5 < n := by
      rcases Nat.lt_or_ge (c.toNat - 5) n with h | h
      · exact h
      · exfalso
        have z := hz (c.toNat - 5) h (by omega)
        rw [← ck, el] at z
        exact sa.ne0 z
    have cc : ∀ q : UInt64, q.toNat < 3 → bget G (d7 + 8192 + 3 * (c - 5) + q) = bget g (d7 + 8192 + 3 * (c - 5) + q) :=
      fun q hq => hag _ (by rw [shapeRow c h5 hlt q hq]; omega) (by rw [shapeRow c h5 hlt q hq]; omega)
    have c0 := cc 0 (by decide); simp only [UInt64.add_zero] at c0
    exact .pr h5 hlt (by rw [c0]; exact el) (by rw [cc 1 (by decide)]; exact er) (by rw [cc 2 (by decide)]; exact ew) iha ihb

end ParInv
