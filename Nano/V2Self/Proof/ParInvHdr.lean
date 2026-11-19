/- Nano/V2Self/Proof/ParInvHdr: def-header tasks 70 / 73 / 74 / 75 on box C's Rep (parser lead).  Generic `rep_cur`: the current
def row's fields +1..+4, +6 and `k` parameter codes appended at h[27] represent a new current row `cur'`. -/
import Nano.V2Self.Proof.ParInvFinish
namespace ParInv
open C BufL ParSpec ParRun

/-- `rowRep_frame'` with agreement only on the row's own parameter cells -/
theorem rowRep_frame'' {h h' : Buf} {j : Nat} {d : DefR} (hj : j < 512) (r : RowRep h j d)
    (c : ∀ k : UInt64, k.toNat < 8 → bget h' (d7 + 8 * j.toUInt64 + k) = bget h (d7 + 8 * j.toUInt64 + k))
    (cc : ∀ i : Nat, i < d.params.length → bget h' (d7 + 4096 + bget h (d7 + 8 * j.toUInt64 + 5) + i.toUInt64) =
      bget h (d7 + 4096 + bget h (d7 + 8 * j.toUInt64 + 5) + i.toUInt64))
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') : RowRep h' j d := by
  have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
  obtain ⟨a0, a1, a2, a3, a4, a6, a5, ap⟩ := r
  refine ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1, by rw [c 2 (by decide)]; exact a2,
    by rw [c 3 (by decide)]; exact a3.frame es, by rw [c 4 (by decide)]; exact a4, by rw [c 6 (by decide)]; exact a6,
    by rw [c 5 (by decide)]; exact a5, fun i hi => ?_⟩
  rw [c 5 (by decide), cc i hi]
  exact (ap i hi).frame es

/-- **current-row update**: Rep is kept when only the current row's fields +1..+4, +6, the parameter-code cells
[h27, h27 + k) and h[27] change and they represent `cur'` (same name and start, `k` more parameters) -/
theorem rep_cur {h h' ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (hD : inDefF fs = true) (cur' : DefR) (k : Nat)
    (hname : cur'.name = st.cur.name) (hpre : ∀ i (hi : i < st.cur.params.length), ∃ hi' : i < cur'.params.length, cur'.params[i] = st.cur.params[i])
    (hk : cur'.params.length = st.cur.params.length + k) (hJ : (bget h 27).toNat + k ≤ 4096) (hl : h'.length = h.length)
    (ed : h'.drop 184384 = h.drop 184384)
    (e : ∀ i : UInt64, i.toNat ≠ 27 →
      (i.toNat < 147520 + 8 * st.defs.length + 1 ∨ 147520 + 8 * st.defs.length + 7 ≤ i.toNat ∨ i.toNat = 147520 + 8 * st.defs.length + 5) →
      (i.toNat < 151616 + (bget h 27).toNat ∨ 151616 + (bget h 27).toNat + k ≤ i.toNat) → bget h' i = bget h i)
    (e27 : (bget h' 27).toNat = (bget h 27).toNat + k)
    (r1 : bget h' (d7 + 8 * st.defs.length.toUInt64 + 1) = cur'.npw.toUInt64)
    (r2 : (bget h' (d7 + 8 * st.defs.length.toUInt64 + 2)).toNat = cur'.nni)
    (r3 : ShOpt h' (bget h' (d7 + 8 * st.defs.length.toUInt64 + 3)) cur'.res)
    (r4 : bget h' (d7 + 8 * st.defs.length.toUInt64 + 4) = b01 cur'.loop)
    (r6 : (bget h' (d7 + 8 * st.defs.length.toUInt64 + 6)).toNat = cur'.params.length)
    (hc : ∀ i (hi : i < k), ShapeCode h' (bget h' (d7 + 4096 + (bget h 27) + i.toUInt64)) (cur'.params[st.cur.params.length + i]'(by omega))) :
    Rep h' ts { st with cur := cur' } fs := by
  obtain ⟨hn, hlen, har⟩ := rep_bounds r
  obtain ⟨rT, rts, r0, r3', r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  rw [hD] at rD
  obtain ⟨d12, dlt, d27, drows, dcur, dz, d0, dsr⟩ := rD
  simp only [if_true] at dcur
  obtain ⟨⟨c0, c1, c2, c3, c4, c6, c5, cc⟩, cs⟩ := dcur
  have big : ∀ i : UInt64, 155712 ≤ i.toNat → bget h' i = bget h i := fun i hi => e i (by omega) (by omega) (by omega)
  have low : ∀ i : UInt64, i.toNat < 147520 → i.toNat ≠ 27 → bget h' i = bget h i := fun i hi a => e i a (by omega) (by omega)
  have et : TokAgree h h' := ⟨low 7 (by decide) (by decide), fun i hi => big i (by omega)⟩
  have es : ShTabAgree h h' := fun i a _ => big i a
  have rowc : ∀ k' : UInt64, k'.toNat < 8 → (d7 + 8 * st.defs.length.toUInt64 + k').toNat = 147520 + 8 * st.defs.length + k'.toNat :=
    fun k' hk' => defCell _ dlt k' hk'
  have rc5 : (d7 + 8 * st.defs.length.toUInt64 + 5).toNat = 147520 + 8 * st.defs.length + 5 := rowc 5 (by decide)
  have rc0 : (d7 + 8 * st.defs.length.toUInt64 + 0).toNat = 147520 + 8 * st.defs.length := rowc 0 (by decide)
  have c5' : bget h' (d7 + 8 * st.defs.length.toUInt64 + 5) = bget h (d7 + 8 * st.defs.length.toUInt64 + 5) :=
    e _ (by rw [rc5]; omega) (Or.inr (Or.inr rc5)) (Or.inl (by rw [rc5]; omega))
  have c0' : bget h' (d7 + 8 * st.defs.length.toUInt64) = bget h (d7 + 8 * st.defs.length.toUInt64) := by
    have := e (d7 + 8 * st.defs.length.toUInt64 + 0) (by rw [rc0]; omega) (Or.inl (by rw [rc0]; omega))
      (Or.inl (by rw [rc0]; omega))
    simpa using this
  refine ⟨tokensAt_frame rT et rts, rts, by rw [low 0 (by decide) (by decide)]; exact r0,
    by rw [low 3 (by decide) (by decide)]; exact tokAt_frame et hn r3', by rw [low 11 (by decide) (by decide)]; exact r11,
    binds_frame rB (low 4 (by decide) (by decide)) (fun i a _ => big i (by omega)) et hn es, ?_,
    arena_frame rA (low 8 (by decide) (by decide)) (low 9 (by decide) (by decide)) (fun i a b => low i b (by omega)) es,
    fun s hs => by rw [low 25 (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx hne => by rw [low 29 (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
    by rw [low 30 (by decide) (by decide)]; exact r30, by rw [low 32 (by decide) (by decide)]; exact r32, out_frame rO ed,
    tasks_frame rK (low 5 (by decide) (by decide)) (fun i a b => low i (by have := rK.2.1; omega) (by omega)) et hn es
      (fun i a b => low i b (by omega)) har⟩
  show DefsRep h' { st with cur := cur' } (inDefF fs)
  rw [hD]
  refine ⟨by rw [low 12 (by decide) (by decide)]; exact d12, dlt, by rw [e27]; omega, fun j hj => ?_, ?_, fun j h1 h2 => ?_, ?_, ?_⟩
  · have hj : j < st.defs.length := hj
    obtain ⟨rr, rs⟩ := drows j hj
    have a5 := rr.2.2.2.2.2.2.1
    refine ⟨rowRep_frame'' (by omega) rr (fun k' hk' => e _ (by rw [defCell j (by omega) k' hk']; omega)
        (Or.inl (by rw [defCell j (by omega) k' hk']; omega)) (Or.inl (by rw [defCell j (by omega) k' hk']; omega)))
        (fun i (hi : i < (st.defs[j]'hj).params.length) => by
          have pc := parCell (bget h (d7 + 8 * j.toUInt64 + 5)) i (by omega)
          exact e _ (by rw [pc]; omega) (Or.inr (Or.inl (by rw [pc]; omega))) (Or.inl (by rw [pc]; omega))) et hn es, ?_⟩
    rw [e _ (by rw [defCell j (by omega) 5 (by decide)]; simp; omega) (Or.inl (by rw [defCell j (by omega) 5 (by decide)]; simp; omega))
      (Or.inl (by rw [defCell j (by omega) 5 (by decide)]; simp; omega)), e27]
    exact Nat.le_trans rs (Nat.le_add_right _ _)
  · simp only [if_true]
    refine ⟨⟨by rw [c0', hname]; exact nameAt_frame et (by omega) c0, r1, r2, r3, r4, r6, by rw [c5', hk]; omega, fun i hi => ?_⟩, ?_⟩
    · have hi : i < cur'.params.length := hi
      rw [c5']
      by_cases hio : i < st.cur.params.length
      · obtain ⟨hi', heq⟩ := hpre i hio
        have pc := parCell (bget h (d7 + 8 * st.defs.length.toUInt64 + 5)) i (by omega)
        rw [heq, e _ (by rw [pc]; omega) (Or.inr (Or.inl (by rw [pc]; omega))) (Or.inl (by rw [pc]; omega))]
        exact (cc i hio).frame es
      · have hi2 : i - st.cur.params.length < k := by omega
        have := hc (i - st.cur.params.length) hi2
        have ea : d7 + 4096 + bget h (d7 + 8 * st.defs.length.toUInt64 + 5) + i.toUInt64 =
            d7 + 4096 + bget h 27 + (i - st.cur.params.length).toUInt64 := by
          apply UInt64.toNat_inj.mp
          rw [parCell _ _ (by omega), parCell _ _ (by omega)]; omega
        rw [ea]
        have ei : st.cur.params.length + (i - st.cur.params.length) = i := by omega
        simp only [ei] at this
        exact this
    · rw [c5', hk, e27]; omega
  · have h1 : st.defs.length < j := h1
    exact fun k' hk' => by
      rw [e _ (by rw [defCell j h2 k' hk']; omega) (Or.inr (Or.inl (by rw [defCell j h2 k' hk']; omega)))
        (Or.inl (by rw [defCell j h2 k' hk']; omega))]
      exact dz j h1 h2 k' hk'
  · intro i hi1 hi2
    rw [e27] at hi1
    have eidx : (d7 + 4096 + i.toUInt64).toNat = 151616 + i := by
      rw [UInt64.toNat_add]; simp [Nat.toUInt64, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; omega
    rw [e _ (by rw [eidx]; omega) (Or.inr (Or.inl (by rw [eidx]; omega))) (Or.inr (by rw [eidx]; omega))]
    exact d0 i (by omega) hi2

  · refine ⟨by rw [low 26 (by decide) (by decide)]; exact dsr.1, fun k' h1 h2 => ?_, fun k' hk' => ?_⟩
    · rw [low 26 (by decide) (by decide)] at h1
      have ek : (d7 + 8192 + 3 * k'.toUInt64).toNat = 155712 + 3 * k' := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, show (d7 + 8192 : UInt64).toNat = 155712 from rfl]; simp; omega
      rw [big _ (by omega)]; exact dsr.2.1 k' h1 h2
    · rw [low 26 (by decide) (by decide)] at hk'
      obtain ⟨l, r, sa, sb, sw⟩ := dsr.2.2 k' hk'
      have cq : ∀ q : UInt64, q.toNat < 3 → bget h' (d7 + 8192 + 3 * k'.toUInt64 + q) = bget h (d7 + 8192 + 3 * k'.toUInt64 + q) :=
        fun q hq => big _ (by have := dsr.1; rw [shRowK k' (by omega) q hq]; omega)
      have cq0 := cq 0 (by decide); simp only [UInt64.add_zero] at cq0
      exact ⟨l, r, by rw [cq0]; exact sa.frame es, by rw [cq 1 (by decide)]; exact sb.frame es, by rw [cq 2 (by decide)]; exact sw⟩

theorem ShapeCode.nt_eq {h : Buf} {c : UInt64} (r : ShapeCode h c .nt) : c = 4 := by cases r; rfl

/-- core of task 70 on the popped heap -/
theorem plain_core {g ts : Buf} {st : St} {fs : List Frame} (R1 : Rep g ts st fs) (hfs : inDefF fs = true)
    {w : Sh} (hty : st.ty = some w) (a b : UInt64) (hs : bget (v134 g a b) 0 ≠ 0) :
    ∃ st', stepF .plainBody st = some ([.expr 0 0, .defEnd], st') ∧ Rep (v134 g a b) ts st' ([.expr 0 0, .defEnd] ++ fs) := by
  obtain ⟨hn, hlen, har⟩ := rep_bounds R1
  have rD := R1.2.2.2.2.2.2.1
  rw [hfs] at rD
  obtain ⟨d12, dlt, d27, _, dcur, _, _, _⟩ := rD
  simp only [if_true] at dcur
  obtain ⟨⟨_, _, c2, _, _, c6, _, _⟩, _⟩ := dcur
  have hj : bget g 12 = st.defs.length.toUInt64 := by apply UInt64.toNat_inj.mp; rw [d12]; simp [Nat.toUInt64]; omega
  have r11 : bget g 11 = st.nx.toUInt64 := R1.2.2.2.2.1
  have sw : ShapeCode g (bget g 25) w := R1.2.2.2.2.2.2.2.2.1 w hty
  unfold v134 at hs ⊢
  by_cases h4 : bget g 25 = 4
  · simp only [h4, beq_self_eq_true, if_true] at hs; exact absurd (status_bset0 g) hs
  have hw : w ≠ .nt := fun e => by subst e; exact h4 sw.nt_eq
  simp only [show (bget g 25 == 4) = false from by simpa using h4, Bool.false_eq_true, if_false] at hs ⊢
  have rk : ∀ k : UInt64, k.toNat < 8 → (d7 + 8 * st.defs.length.toUInt64 + k).toNat = 147520 + 8 * st.defs.length + k.toNat :=
    fun k hk => defCell _ dlt k hk
  have f1 : ∀ (b : Buf) (v i : UInt64), i.toNat < 147520 → bget (bset b (d7 + 8 * st.defs.length.toUInt64 + 1) v) i = bget b i :=
    fun b v i hi => bget_bset' _ _ _ _ (by rw [rk 1 (by decide)]; simp; omega)
  have f3 : ∀ (b : Buf) (v i : UInt64), i.toNat < 147520 → bget (bset b (d7 + 8 * st.defs.length.toUInt64 + 3) v) i = bget b i :=
    fun b v i hi => bget_bset' _ _ _ _ (by rw [rk 3 (by decide)]; simp; omega)
  have f4 : ∀ (b : Buf) (v i : UInt64), i.toNat < 147520 → bget (bset b (d7 + 8 * st.defs.length.toUInt64 + 4) v) i = bget b i :=
    fun b v i hi => bget_bset' _ _ _ _ (by rw [rk 4 (by decide)]; simp; omega)
  rw [hj] at hs ⊢
  simp (disch := decide) only [f1, f3, f4, hj, r11] at hs ⊢
  generalize hH : bset (bset (bset g (d7 + 8 * st.defs.length.toUInt64 + 1) st.nx.toUInt64)
    (d7 + 8 * st.defs.length.toUInt64 + 3) (bget g 25)) (d7 + 8 * st.defs.length.toUInt64 + 4) 0 = H at hs ⊢
  have eH : ∀ i : UInt64, i.toNat ≠ 147520 + 8 * st.defs.length + 1 → i.toNat ≠ 147520 + 8 * st.defs.length + 3 →
      i.toNat ≠ 147520 + 8 * st.defs.length + 4 → bget H i = bget g i := by
    intro i a1 a3 a4; rw [← hH]
    rw [bget_bset' _ _ _ _ (by rw [rk 4 (by decide)]; simp; omega), bget_bset' _ _ _ _ (by rw [rk 3 (by decide)]; simp; omega),
      bget_bset' _ _ _ _ (by rw [rk 1 (by decide)]; simp; omega)]
  have lH : H.length = g.length := by rw [← hH]; simp [length_bset]
  have g1 : bget H (d7 + 8 * st.defs.length.toUInt64 + 1) = st.nx.toUInt64 := by
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 4 (by decide), rk 1 (by decide)]; simp), bget_bset' _ _ _ _ (by rw [rk 3 (by decide), rk 1 (by decide)]; simp),
      bget_bset_eq _ _ _ _ rfl (by rw [rk 1 (by decide)]; simp; omega)]
  have g3 : bget H (d7 + 8 * st.defs.length.toUInt64 + 3) = bget g 25 := by
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 4 (by decide), rk 3 (by decide)]; simp),
      bget_bset_eq _ _ _ _ rfl (by rw [rk 3 (by decide)]; simp [length_bset]; omega)]
  have g4 : bget H (d7 + 8 * st.defs.length.toUInt64 + 4) = 0 := by
    rw [← hH, bget_bset_eq _ _ _ _ rfl (by rw [rk 4 (by decide)]; simp [length_bset]; omega)]
  have k2 : bget H (d7 + 8 * st.defs.length.toUInt64 + 2) = bget g (d7 + 8 * st.defs.length.toUInt64 + 2) :=
    eH _ (by rw [rk 2 (by decide)]; simp) (by rw [rk 2 (by decide)]; simp) (by rw [rk 2 (by decide)]; simp)
  have k6 : bget H (d7 + 8 * st.defs.length.toUInt64 + 6) = bget g (d7 + 8 * st.defs.length.toUInt64 + 6) :=
    eH _ (by rw [rk 6 (by decide)]; simp) (by rw [rk 6 (by decide)]; simp) (by rw [rk 6 (by decide)]; simp)
  have es : ShTabAgree g H := fun i a _ => eH i (by omega) (by omega) (by omega)
  have RH := rep_cur (h' := H) R1 hfs { st.cur with npw := st.nx, res := some w, loop := false } 0 rfl (fun i hi => ⟨hi, rfl⟩) rfl
    (by omega) lH (by rw [← hH]; simp only [drop_bset _ _ _ (by rw [rk 4 (by decide)]; simp; omega), drop_bset _ _ _ (by rw [rk 3 (by decide)]; simp; omega),
      drop_bset _ _ _ (by rw [rk 1 (by decide)]; simp; omega)])
    (fun i _ c _ => eH i (by omega) (by omega) (by omega)) (by rw [eH 27 (by (try simp) <;> omega) (by (try simp) <;> omega) (by (try simp) <;> omega)]; rfl) g1
    (by rw [k2]; exact c2) (by rw [g3]; exact sw.frame es) (by rw [g4]; rfl) (by rw [k6]; exact c6) (fun i hi => absurd hi (Nat.not_lt_zero _))
  have p3 : bget H 3 = bget g 3 := eH 3 (by (try simp) <;> omega) (by (try simp) <;> omega) (by (try simp) <;> omega)
  have hK : TokAt H (bget g 3) st.toks := by rw [← p3]; exact RH.2.2.2.1
  have hT := RH.1
  rw [UInt64.add_zero] at hs ⊢
  by_cases ht : bget H (d11 + bget g 3) = 9
  · obtain ⟨rest, et, kr⟩ := tok_kw hK hT RH.2.1 ht (by decide) (by decide) (by decide)
    simp only [ht, beq_self_eq_true, if_true] at hs ⊢
    have R2 := rep_cursor RH (bget g 3 + 1) kr
    have hs1 : bget (v1 (bset H 3 (bget g 3 + 1)) 80 0 0) 0 ≠ 0 := fun e => hs (v1_zero _ _ _ _ e)
    have R3 := rep_push .defEnd 0 0 R2 (by simp [inDefF, Frame.isDefs]) trivial (fun e => hs1 e)
    have R4 := rep_push (.expr 0 0) 0 0 R3 (by simp [inDefF, Frame.isDefs]) ⟨rfl, rfl⟩ hs
    refine ⟨_, ?_, R4⟩
    simp [stepF, hty, hw, et]
  · simp only [show (bget H (d11 + bget g 3) == 9) = false from by simpa using ht, Bool.false_eq_true, if_false] at hs
    exact absurd (status_bset0 H) hs

/-- **task 70** (plain body `:= e`): the current row gets npw = nx, res = ty, loop = false; push defEnd, expr -/
theorem h_plainBody {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.plainBody :: fs)) (hfs : inDefF fs = true)
    {w : Sh} (hty : st.ty = some w) (hs : bget (step h) 0 ≠ 0) :
    ∃ st', stepF .plainBody st = some ([.expr 0 0, .defEnd], st') ∧ Rep (step h) ts st' ([.expr 0 0, .defEnd] ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  have ev : step h = v134 (bset h 5 fs.length.toUInt64) (taskAt h fs.length).a (taskAt h fs.length).b := by rw [E]; rfl
  rw [ev] at hs ⊢
  exact plain_core R1 hfs hty _ _ hs


/-- **task 73** (after the header colon): `:=` is the plain body; `Nat →` (prev token `Nat`, ty = Nat) opens a loop header: npw = 1,
loop, the fuel parameter code 4 appended; push stateTy, tyAtom.  `hprev`: the cell before the cursor is the previous token's
last word (the previous token is a keyword here) -/
theorem h_afterColon {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.afterColon :: fs)) (hfs : inDefF fs = true)
    {w : Sh} (hty : st.ty = some w) (hnni : st.cur.nni < 2 ^ 63)
    (hprev : bget h (d11 + bget h 3 - 1) = 35 → prevTok st = some (.k 35)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF .afterColon st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  have ev : step h = v135 (bset h 5 fs.length.toUInt64) (taskAt h fs.length).a (taskAt h fs.length).b := by rw [E]; rfl
  have hp : (bget h 3).toNat ≤ (bget h 7).toNat := r.2.2.2.1.le
  have hn7 := (rep_bounds r).1
  have ip : (d11 + bget h 3 - 1).toNat = 184383 + (bget h 3).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_add]; simp [show d11.toNat = 184384 from rfl]; omega)),
      UInt64.toNat_add]; simp [show d11.toNat = 184384 from rfl]; omega
  have hprev' : bget (bset h 5 fs.length.toUInt64) (d11 + bget (bset h 5 fs.length.toUInt64) 3 - 1) = 35 → prevTok st = some (.k 35) := by
    intro e; apply hprev
    rw [show bget (bset h 5 fs.length.toUInt64) 3 = bget h 3 from bget_bset' _ _ _ _ (by decide)] at e
    rw [bget_bset' _ _ _ _ (by rw [ip]; (try simp) <;> omega)] at e; exact e
  clear hprev
  rw [ev] at hs ⊢
  generalize (taskAt h fs.length).a = a at hs ⊢
  generalize (taskAt h fs.length).b = b at hs ⊢
  generalize bset h 5 fs.length.toUInt64 = g at R1 hs hprev' ⊢
  obtain ⟨hn, hlen, har⟩ := rep_bounds R1
  have hK : TokAt g (bget g 3) st.toks := R1.2.2.2.1
  have hT := R1.1
  have sw : ShapeCode g (bget g 25) w := R1.2.2.2.2.2.2.2.2.1 w hty
  unfold v135 at hs ⊢
  simp only [] at hs ⊢
  by_cases t9 : bget g (d11 + bget g 3) = 9
  · simp only [t9, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, _⟩ := tok_kw hK hT R1.2.1 t9 (by decide) (by decide) (by decide)
    simp only [show (9 : UInt64).toNat = 9 from rfl] at et
    obtain ⟨st', e1, e2⟩ := plain_core R1 hfs hty 0 0 hs
    refine ⟨_, st', ?_, e2⟩
    rw [← e1]; simp only [stepF, et, hty]
  simp only [show (bget g (d11 + bget g 3) == 9) = false from by simpa using t9, Bool.false_eq_true, if_false] at hs ⊢
  by_cases w4 : ¬ bget g 25 = 4
  · simp only [show (bget g 25 == 4) = false from by simpa using w4, Bool.false_eq_true, if_false] at hs
    exact absurd (status_bset0 g) hs
  have w4 : bget g 25 = 4 := Decidable.of_not_not w4
  by_cases t17 : ¬ bget g (d11 + bget g 3) = 17
  · simp only [w4, beq_self_eq_true, if_true, show (bget g (d11 + bget g 3) == k42) = false from by simpa [k42] using t17,
      Bool.false_eq_true, if_false] at hs
    exact absurd (status_bset0 g) hs
  have t17 : bget g (d11 + bget g 3) = 17 := Decidable.of_not_not t17
  by_cases t35 : ¬ bget g (d11 + bget g 3 - 1) = 35
  · simp only [w4, beq_self_eq_true, if_true, show (bget g (d11 + bget g 3) == k42) = true from by simpa [k42] using t17,
      show (bget g (d11 + bget g 3 - 1) == 35) = false from by simpa using t35, Bool.false_eq_true, if_false] at hs
    exact absurd (status_bset0 g) hs
  have t35 : bget g (d11 + bget g 3 - 1) = 35 := Decidable.of_not_not t35
  simp only [w4, beq_self_eq_true, if_true, show (bget g (d11 + bget g 3) == k42) = true from by simpa [k42] using t17, t35] at hs ⊢
  have wnt : w = .nt := by rw [w4] at sw; exact ShapeCode.det sw .nt
  subst wnt
  obtain ⟨rest, et, kr⟩ := tok_kw hK hT R1.2.1 t17 (by decide) (by decide) (by decide)
  have R2 := rep_cursor R1 (bget g 3 + 1) kr
  have rD := R1.2.2.2.2.2.2.1
  rw [hfs] at rD
  obtain ⟨d12, dlt, d27, _, dcur, _, _, _⟩ := rD
  simp only [if_true] at dcur
  obtain ⟨⟨_, _, c2, c3, _, c6, c5, _⟩, cs⟩ := dcur
  have hj : bget g 12 = st.defs.length.toUInt64 := by apply UInt64.toNat_inj.mp; rw [d12]; simp [Nat.toUInt64]; omega
  have rk : ∀ k : UInt64, k.toNat < 8 → (d7 + 8 * st.defs.length.toUInt64 + k).toNat = 147520 + 8 * st.defs.length + k.toNat :=
    fun k hk => defCell _ dlt k hk
  rw [hj] at hs ⊢
  generalize hG1 : bset g 3 (bget g 3 + 1) = G1 at R2 hs ⊢
  have e1 : ∀ i : UInt64, i.toNat ≠ 3 → bget G1 i = bget g i := fun i hi => by rw [← hG1]; exact bget_bset' _ _ _ _ (by simp; omega)
  have l1 : G1.length = g.length := by rw [← hG1, length_bset]
  generalize hH0 : bset (bset G1 (d7 + 8 * st.defs.length.toUInt64 + 1) 1) (d7 + 8 * st.defs.length.toUInt64 + 4) 1 = H0 at hs ⊢
  have e0 : ∀ i : UInt64, i.toNat ≠ 147520 + 8 * st.defs.length + 1 → i.toNat ≠ 147520 + 8 * st.defs.length + 4 → bget H0 i = bget G1 i := by
    intro i a1 a4; rw [← hH0, bget_bset' _ _ _ _ (by rw [rk 4 (by decide)]; (try (try simp) <;> omega) <;> omega), bget_bset' _ _ _ _ (by rw [rk 1 (by decide)]; (try (try simp) <;> omega) <;> omega)]
  have r12 : bget H0 12 = st.defs.length.toUInt64 := by rw [e0 12 (by (try (try simp) <;> omega) <;> omega) (by (try (try simp) <;> omega) <;> omega), e1 12 (by decide), hj]
  have r27 : bget H0 27 = bget g 27 := by rw [e0 27 (by (try (try simp) <;> omega) <;> omega) (by (try (try simp) <;> omega) <;> omega), e1 27 (by decide)]
  have r2 : bget H0 (d7 + 8 * st.defs.length.toUInt64 + 2) = bget g (d7 + 8 * st.defs.length.toUInt64 + 2) := by
    rw [e0 _ (by rw [rk 2 (by decide)]; (try simp) <;> omega) (by rw [rk 2 (by decide)]; (try simp) <;> omega), e1 _ (by rw [rk 2 (by decide)]; (try (try simp) <;> omega) <;> omega)]
  have r6 : bget H0 (d7 + 8 * st.defs.length.toUInt64 + 6) = bget g (d7 + 8 * st.defs.length.toUInt64 + 6) := by
    rw [e0 _ (by rw [rk 6 (by decide)]; (try simp) <;> omega) (by rw [rk 6 (by decide)]; (try simp) <;> omega), e1 _ (by rw [rk 6 (by decide)]; (try (try simp) <;> omega) <;> omega)]
  unfold v200 at hs ⊢
  simp only [r12, r27, r2, r6] at hs ⊢
  by_cases hJ : ¬ bget g 27 < 4096
  · simp only [hJ, if_false] at hs; exact absurd (v1_zero _ _ _ _ (v1_zero _ _ _ _ (status_bset0 _))) hs
  have hJ : bget g 27 < 4096 := Decidable.of_not_not hJ
  simp only [hJ, if_true] at hs ⊢
  have hJn : (bget g 27).toNat < 4096 := UInt64.lt_iff_toNat_lt.mp hJ
  have g27 : bget G1 27 = bget g 27 := e1 27 (by decide)
  have g5 : bget G1 (d7 + 8 * st.defs.length.toUInt64 + 5) = bget g (d7 + 8 * st.defs.length.toUInt64 + 5) := e1 _ (by rw [rk 5 (by decide)]; (try simp) <;> omega)
  have ip : (d7 + 4096 + bget g 27).toNat = 151616 + (bget g 27).toNat := by
    rw [UInt64.toNat_add, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; omega
  generalize hH : bset (bset (bset (bset H0 (d7 + 4096 + bget g 27) 4) 27 (bget g 27 + 1))
      (d7 + 8 * st.defs.length.toUInt64 + 2) (bget g (d7 + 8 * st.defs.length.toUInt64 + 2) + 1 - k0))
      (d7 + 8 * st.defs.length.toUInt64 + 6) (bget g (d7 + 8 * st.defs.length.toUInt64 + 6) + 1) = H at hs ⊢
  have lH : H.length = G1.length := by rw [← hH, ← hH0]; simp [length_bset]
  have eH : ∀ i : UInt64, i.toNat ≠ 147520 + 8 * st.defs.length + 2 → i.toNat ≠ 147520 + 8 * st.defs.length + 6 → i.toNat ≠ 27 →
      i.toNat ≠ 151616 + (bget g 27).toNat → bget H i = bget H0 i := by
    intro i a2 a6 a27 ap
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 6 (by decide)]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [rk 2 (by decide)]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [ip]; omega)]
  have cH : ∀ i : UInt64, i.toNat ≠ 147520 + 8 * st.defs.length + 1 → i.toNat ≠ 147520 + 8 * st.defs.length + 4 →
      i.toNat ≠ 147520 + 8 * st.defs.length + 2 → i.toNat ≠ 147520 + 8 * st.defs.length + 6 → i.toNat ≠ 27 →
      i.toNat ≠ 151616 + (bget g 27).toNat → bget H i = bget G1 i := fun i a1 a4 a2 a6 a27 ap => by
    rw [eH i a2 a6 a27 ap, e0 i a1 a4]
  have es : ShTabAgree G1 H := fun i a _ => cH i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have es' : ShTabAgree g G1 := fun i a _ => e1 i (by omega)
  have q6 : bget H (d7 + 8 * st.defs.length.toUInt64 + 6) = bget g (d7 + 8 * st.defs.length.toUInt64 + 6) + 1 := by
    rw [← hH, bget_bset_eq _ _ _ _ rfl (by rw [rk 6 (by decide)]; simp [length_bset, ← hH0, ← hG1]; omega)]
  have q2 : bget H (d7 + 8 * st.defs.length.toUInt64 + 2) = bget g (d7 + 8 * st.defs.length.toUInt64 + 2) + 1 := by
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 6 (by decide), rk 2 (by decide)]; (try simp) <;> omega),
      bget_bset_eq _ _ _ _ rfl (by rw [rk 2 (by decide)]; simp [length_bset, ← hH0, ← hG1]; omega)]; simp [k0]
  have q27 : bget H 27 = bget g 27 + 1 := by
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 6 (by decide)]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [rk 2 (by decide)]; (try simp) <;> omega),
      bget_bset_eq _ _ _ _ rfl (by simp [length_bset, ← hH0, ← hG1]; omega)]
  have qP : bget H (d7 + 4096 + bget g 27) = 4 := by
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 6 (by decide), ip]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [rk 2 (by decide), ip]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by rw [ip]; (try simp) <;> omega), bget_bset_eq _ _ _ _ rfl (by rw [ip]; simp [length_bset, ← hH0, ← hG1]; omega)]
  have q1 : bget H (d7 + 8 * st.defs.length.toUInt64 + 1) = 1 := by
    rw [eH _ (by rw [rk 1 (by decide)]; (try simp) <;> omega) (by rw [rk 1 (by decide)]; (try simp) <;> omega) (by rw [rk 1 (by decide)]; (try simp) <;> omega) (by rw [rk 1 (by decide)]; (try simp) <;> omega),
      ← hH0, bget_bset' _ _ _ _ (by rw [rk 4 (by decide), rk 1 (by decide)]; (try simp) <;> omega),
      bget_bset_eq _ _ _ _ rfl (by rw [rk 1 (by decide)]; simp [length_bset, ← hG1]; omega)]
  have q4 : bget H (d7 + 8 * st.defs.length.toUInt64 + 4) = 1 := by
    rw [eH _ (by rw [rk 4 (by decide)]; (try simp) <;> omega) (by rw [rk 4 (by decide)]; (try simp) <;> omega) (by rw [rk 4 (by decide)]; (try simp) <;> omega) (by rw [rk 4 (by decide)]; (try simp) <;> omega),
      ← hH0, bget_bset_eq _ _ _ _ rfl (by rw [rk 4 (by decide)]; simp [length_bset, ← hG1]; omega)]
  have q3 : bget H (d7 + 8 * st.defs.length.toUInt64 + 3) = bget g (d7 + 8 * st.defs.length.toUInt64 + 3) := by
    rw [cH _ (by rw [rk 3 (by decide)]; (try simp) <;> omega) (by rw [rk 3 (by decide)]; (try simp) <;> omega) (by rw [rk 3 (by decide)]; (try simp) <;> omega)
      (by rw [rk 3 (by decide)]; (try simp) <;> omega) (by rw [rk 3 (by decide)]; (try simp) <;> omega) (by rw [rk 3 (by decide)]; (try simp) <;> omega), e1 _ (by rw [rk 3 (by decide)]; (try simp) <;> omega)]
  have ed : H.drop 184384 = G1.drop 184384 := by
    rw [← hH, ← hH0, drop_bset _ _ _ (by rw [rk 6 (by decide)]; (try simp) <;> omega), drop_bset _ _ _ (by rw [rk 2 (by decide)]; (try simp) <;> omega),
      drop_bset _ _ _ (by decide), drop_bset _ _ _ (by rw [ip]; (try simp) <;> omega), drop_bset _ _ _ (by rw [rk 4 (by decide)]; (try simp) <;> omega),
      drop_bset _ _ _ (by rw [rk 1 (by decide)]; (try simp) <;> omega)]
  have RC := rep_cur (h := G1) (h' := H) R2 hfs
    { st.cur with npw := 1, loop := true, params := st.cur.params ++ [.nt], nni := st.cur.nni + 1 } 1 rfl
    (fun i hi => by dsimp only at hi; exact ⟨by simp; omega, by simp [List.getElem_append_left hi]⟩) (by simp) (by rw [g27]; omega) lH ed
    (fun i a b c => by
      dsimp only at b c
      rw [g27] at c
      exact cH i (by omega) (by omega) (by omega) (by omega) a (by omega))
    (by rw [q27, g27]; simp; omega) (by rw [q1]; rfl)
    (by rw [q2]; simp only []; rw [UInt64.toNat_add]; simp only [show (1 : UInt64).toNat = 1 from rfl]; rw [c2]; omega)
    (by rw [q3]; exact (c3.frame es').frame es) (by rw [q4]; rfl)
    (by rw [q6]; simp only []; rw [UInt64.toNat_add]; simp only [show (1 : UInt64).toNat = 1 from rfl]; rw [c6]; simp; omega)
    (fun i hi => by
      have i0 : i = 0 := by omega
      subst i0
      simp only [g27, show (0 : Nat).toUInt64 = 0 from rfl, UInt64.add_zero, qP, Nat.add_zero, List.getElem_append_right]
      simp
      exact .nt)
  have hs1 : bget (v1 H 74 0 0) 0 ≠ 0 := fun e => hs (v1_zero _ _ _ _ e)
  have R3 := rep_push .stateTy 0 0 RC (by simp [inDefF, Frame.isDefs]) trivial hs1
  have R4 := rep_push .tyAtom 0 0 R3 (by simp [inDefF, Frame.isDefs]) trivial hs
  refine ⟨[.tyAtom, .stateTy], _, ?_, R4⟩
  simp only [show (17 : UInt64).toNat = 17 from rfl] at et
  simp [stepF, et, hty, hprev' t35]


theorem ShapeCode.ls_iff {h : Buf} {c : UInt64} {s : Sh} (r : ShapeCode h c s) : c = 3 ↔ s = .ls := by
  cases r with
  | uw => decide
  | bf => decide
  | ls => decide
  | nt => decide
  | pr h5 _ _ _ _ _ _ => constructor
                         · intro e; subst e; simp at h5
                         · intro e; cases e

/-- `v203` = "some parameter cell among the first `c` holds the List code 3" -/
theorem v203_eq (h : Buf) (s1 : UInt64) (ps : List Sh) (hs : s1.toNat + ps.length ≤ 4096)
    (hc : ∀ i (hi : i < ps.length), ShapeCode h (bget h (d7 + 4096 + s1 + i.toUInt64)) (ps[i]'hi)) :
    ∀ c n, c ≤ ps.length → c ≤ n → v203 n h s1 c.toUInt64 = if hasLs ((ps.take c).map some) then 1 else 0 := by
  intro c
  induction c with
  | zero => intro n _ _; cases n <;> simp [v203, hasLs]
  | succ c ih =>
    intro n hc1 hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ne : ((c + 1).toUInt64 == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e
      have := congrArg UInt64.toNat e; simp at this; omega
    have ec : (c + 1).toUInt64 - 1 = c.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have ei : d7 + 4096 + s1 + (c + 1).toUInt64 - 1 = d7 + 4096 + s1 + c.toUInt64 := by
      rw [← ec]; generalize (c + 1).toUInt64 = x; simp only [UInt64.sub_eq_add_neg, UInt64.add_assoc]
    have ht : (ps.take (c + 1)).map some = (ps.take c).map some ++ [some (ps[c]'(by omega))] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.map_append]; rfl
    have hl := (hc c (by omega)).ls_iff
    simp only [v203, ne, Bool.false_eq_true, if_false, ei, ht, hasLs, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    by_cases e3 : bget h (d7 + 4096 + s1 + c.toUInt64) = 3
    · have := hl.mp e3; simp [e3, this]
    · have : ps[c]'(by omega) ≠ .ls := fun e => e3 (hl.mpr e)
      rw [if_neg (by simpa using e3), ec, ih n (by omega) (by omega)]
      simp [hasLs, this]


/-- **task 74** (loop-header state types `T₁ → T₂ → …`): on `→` the type `w` is appended as a parameter (the first List is the
input: no slot, not counted); otherwise go to the arms (at least one state type) -/
theorem h_stateTy {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.stateTy :: fs)) (hfs : inDefF fs = true)
    {w : Sh} (hty : st.ty = some w) (hnni : st.cur.nni < 2 ^ 63) (hnpw : st.cur.npw + w.width < 2 ^ 64)
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF .stateTy st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  have ev : step h = v136 (bset h 5 fs.length.toUInt64) (taskAt h fs.length).a (taskAt h fs.length).b := by rw [E]; rfl
  rw [ev] at hs ⊢
  generalize (taskAt h fs.length).a = a at hs ⊢
  generalize (taskAt h fs.length).b = b at hs ⊢
  generalize bset h 5 fs.length.toUInt64 = g at R1 hs ⊢
  obtain ⟨hn, hlen, har⟩ := rep_bounds R1
  have hK : TokAt g (bget g 3) st.toks := R1.2.2.2.1
  have hT := R1.1
  have sw : ShapeCode g (bget g 25) w := R1.2.2.2.2.2.2.2.2.1 w hty
  have rD := R1.2.2.2.2.2.2.1
  rw [hfs] at rD
  obtain ⟨d12, dlt, d27, _, dcur, _, _, _⟩ := rD
  simp only [if_true] at dcur
  obtain ⟨⟨_, c1, c2, c3, c4, c6, c5, cp⟩, cs⟩ := dcur
  have hj : bget g 12 = st.defs.length.toUInt64 := by apply UInt64.toNat_inj.mp; rw [d12]; simp [Nat.toUInt64]; omega
  have rk : ∀ k : UInt64, k.toNat < 8 → (d7 + 8 * st.defs.length.toUInt64 + k).toNat = 147520 + 8 * st.defs.length + k.toNat :=
    fun k hk => defCell _ dlt k hk
  unfold v136 at hs ⊢
  simp only [hj] at hs ⊢
  by_cases t17 : ¬ bget g (d11 + bget g 3) = 17
  · simp only [show (bget g (d11 + bget g 3) == k42) = false from by simpa [k42] using t17, Bool.false_eq_true, if_false] at hs ⊢
    by_cases p1 : bget g (d7 + 8 * st.defs.length.toUInt64 + 6) = 1
    · simp only [p1, beq_self_eq_true, if_true] at hs; exact absurd (status_bset0 g) hs
    simp only [show (bget g (d7 + 8 * st.defs.length.toUInt64 + 6) == 1) = false from by simpa using p1, Bool.false_eq_true,
      if_false] at hs ⊢
    have R2 := rep_push .armsStart 0 0 R1 (by simp [inDefF, Frame.isDefs]) trivial hs
    refine ⟨[.armsStart], st, ?_, R2⟩
    have hl1 : st.cur.params.length ≠ 1 := fun e => p1 (by apply UInt64.toNat_inj.mp; rw [c6, e]; rfl)
    have nk : ∀ rest, st.toks ≠ .k 17 :: rest := fun rest e => t17 (by
      have := tok_cell_k hK e; apply UInt64.toNat_inj.mp; rw [this]; rfl)
    simp only [stepF, hty]
    split
    all_goals first
      | rfl
      | exact absurd ‹st.cur.params.length = 1› hl1
      | (rename_i heq; exact absurd heq (nk _))
  have t17 : bget g (d11 + bget g 3) = 17 := Decidable.of_not_not t17
  simp only [show (bget g (d11 + bget g 3) == k42) = true from by simpa [k42] using t17, if_true] at hs ⊢
  by_cases w4 : bget g 25 = 4
  · simp only [w4, beq_self_eq_true, if_true] at hs; exact absurd (status_bset0 g) hs
  simp only [show (bget g 25 == 4) = false from by simpa using w4, Bool.false_eq_true, if_false] at hs ⊢
  have hw : w ≠ .nt := fun e => by subst e; exact w4 sw.nt_eq
  -- the input flag
  have hc1 : bget g 27 - bget g (d7 + 8 * st.defs.length.toUInt64 + 5) = st.cur.params.length.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)),
      show st.cur.params.length.toUInt64.toNat = st.cur.params.length from by simp; omega]; omega
  have hn1 : (if ((if (bget g 25 == 3) = true then v203 16777216 g (bget g (d7 + 8 * st.defs.length.toUInt64 + 5))
        (bget g 27 - bget g (d7 + 8 * st.defs.length.toUInt64 + 5)) else 1) == 0) = true then k1 else k0) =
      b01 (w == .ls && !(hasLs (st.cur.params.map some))) := by
    rw [hc1, v203_eq g _ st.cur.params (by omega) cp _ _ (Nat.le_refl _) (by omega), List.take_length]
    by_cases wl : w = .ls
    · have := sw.ls_iff.mpr wl
      subst wl
      cases hl : hasLs (st.cur.params.map some) <;> simp [this, b01, k0, k1]
    · have : ¬ bget g 25 = 3 := fun e => wl (sw.ls_iff.mp e)
      have wb : (w == .ls) = false := by simpa using wl
      simp [this, wb, b01, k0, k1]
  generalize hn1' : (w == .ls && !(hasLs (st.cur.params.map some))) = n1 at hn1
  simp only [hn1] at hs ⊢
  have e9 : v9 g (bget g 25) = bset g 31 w.width.toUInt64 := by unfold v9; rw [v9_cw (o := some w) sw]; rfl
  rw [e9] at hs ⊢
  have rz : bget (bset g 31 w.width.toUInt64) 31 = w.width.toUInt64 := bget_bset_eq _ _ _ _ rfl (by simp; omega)
  rw [rz] at hs ⊢
  generalize hG1 : bset g 31 w.width.toUInt64 = G1 at hs ⊢
  have e1 : ∀ i : UInt64, i.toNat ≠ 31 → bget G1 i = bget g i := fun i hi => by rw [← hG1]; exact bget_bset' _ _ _ _ (by simp; omega)
  have l1 : G1.length = g.length := by rw [← hG1, length_bset]
  have R2 := rep_scratch (h' := G1) R1 (fun i _ a => e1 i a) (by rw [← hG1]; exact drop_bset _ _ _ (by decide))
  generalize hQ : bget g (d7 + 8 * st.defs.length.toUInt64 + 1) + w.width.toUInt64 - w.width.toUInt64 * b01 n1 = Q at hs ⊢
  generalize hH0 : bset G1 (d7 + 8 * st.defs.length.toUInt64 + 1) Q = H0 at hs ⊢
  have e0 : ∀ i : UInt64, i.toNat ≠ 147520 + 8 * st.defs.length + 1 → bget H0 i = bget G1 i := by
    intro i a1; rw [← hH0, bget_bset' _ _ _ _ (by rw [rk 1 (by decide)]; (try simp) <;> omega)]
  have r12 : bget H0 12 = st.defs.length.toUInt64 := by rw [e0 12 (by (try simp) <;> omega), e1 12 (by decide), hj]
  have r27 : bget H0 27 = bget g 27 := by rw [e0 27 (by (try simp) <;> omega), e1 27 (by decide)]
  have r2 : bget H0 (d7 + 8 * st.defs.length.toUInt64 + 2) = bget g (d7 + 8 * st.defs.length.toUInt64 + 2) := by
    rw [e0 _ (by rw [rk 2 (by decide)]; (try simp) <;> omega), e1 _ (by rw [rk 2 (by decide)]; (try simp) <;> omega)]
  have r6 : bget H0 (d7 + 8 * st.defs.length.toUInt64 + 6) = bget g (d7 + 8 * st.defs.length.toUInt64 + 6) := by
    rw [e0 _ (by rw [rk 6 (by decide)]; (try simp) <;> omega), e1 _ (by rw [rk 6 (by decide)]; (try simp) <;> omega)]
  unfold v200 at hs ⊢
  simp only [r12, r27, r2, r6] at hs ⊢
  by_cases hJ : ¬ bget g 27 < 4096
  · simp only [hJ, if_false] at hs; exact absurd (v1_zero _ _ _ _ (v1_zero _ _ _ _ (by rw [bget_bset' _ _ _ _ (by decide)]; exact status_bset0 _))) hs
  have hJ : bget g 27 < 4096 := Decidable.of_not_not hJ
  simp only [hJ, if_true] at hs ⊢
  have hJn : (bget g 27).toNat < 4096 := UInt64.lt_iff_toNat_lt.mp hJ
  have ip : (d7 + 4096 + bget g 27).toNat = 151616 + (bget g 27).toNat := by
    rw [UInt64.toNat_add, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; omega
  have g27 : bget G1 27 = bget g 27 := e1 27 (by decide)
  generalize hH : bset (bset (bset (bset H0 (d7 + 4096 + bget g 27) (bget g 25)) 27 (bget g 27 + 1))
      (d7 + 8 * st.defs.length.toUInt64 + 2) (bget g (d7 + 8 * st.defs.length.toUInt64 + 2) + 1 - b01 n1))
      (d7 + 8 * st.defs.length.toUInt64 + 6) (bget g (d7 + 8 * st.defs.length.toUInt64 + 6) + 1) = H at hs ⊢
  have lH : H.length = G1.length := by rw [← hH, ← hH0]; simp [length_bset]
  have eH : ∀ i : UInt64, i.toNat ≠ 147520 + 8 * st.defs.length + 2 → i.toNat ≠ 147520 + 8 * st.defs.length + 6 → i.toNat ≠ 27 →
      i.toNat ≠ 151616 + (bget g 27).toNat → bget H i = bget H0 i := by
    intro i a2 a6 a27 ap
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 6 (by decide)]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [rk 2 (by decide)]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [ip]; omega)]
  have cH : ∀ i : UInt64, i.toNat ≠ 147520 + 8 * st.defs.length + 1 →
      i.toNat ≠ 147520 + 8 * st.defs.length + 2 → i.toNat ≠ 147520 + 8 * st.defs.length + 6 → i.toNat ≠ 27 →
      i.toNat ≠ 151616 + (bget g 27).toNat → bget H i = bget G1 i := fun i a1 a2 a6 a27 ap => by
    rw [eH i a2 a6 a27 ap, e0 i a1]
  have es : ShTabAgree G1 H := fun i a _ => cH i (by omega) (by omega) (by omega) (by omega) (by omega)
  have es' : ShTabAgree g G1 := fun i a _ => e1 i (by omega)
  have q6 : bget H (d7 + 8 * st.defs.length.toUInt64 + 6) = bget g (d7 + 8 * st.defs.length.toUInt64 + 6) + 1 := by
    rw [← hH, bget_bset_eq _ _ _ _ rfl (by rw [rk 6 (by decide)]; simp [length_bset, ← hH0, ← hG1]; omega)]
  have q2 : bget H (d7 + 8 * st.defs.length.toUInt64 + 2) = bget g (d7 + 8 * st.defs.length.toUInt64 + 2) + 1 - b01 n1 := by
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 6 (by decide), rk 2 (by decide)]; (try simp) <;> omega),
      bget_bset_eq _ _ _ _ rfl (by rw [rk 2 (by decide)]; simp [length_bset, ← hH0, ← hG1]; omega)]
  have q27 : bget H 27 = bget g 27 + 1 := by
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 6 (by decide)]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [rk 2 (by decide)]; (try simp) <;> omega),
      bget_bset_eq _ _ _ _ rfl (by simp [length_bset, ← hH0, ← hG1]; omega)]
  have qP : bget H (d7 + 4096 + bget g 27) = bget g 25 := by
    rw [← hH, bget_bset' _ _ _ _ (by rw [rk 6 (by decide), ip]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [rk 2 (by decide), ip]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by rw [ip]; (try simp) <;> omega), bget_bset_eq _ _ _ _ rfl (by rw [ip]; simp [length_bset, ← hH0, ← hG1]; omega)]
  have q1 : bget H (d7 + 8 * st.defs.length.toUInt64 + 1) = Q := by
    rw [eH _ (by rw [rk 1 (by decide)]; (try simp) <;> omega) (by rw [rk 1 (by decide)]; (try simp) <;> omega) (by rw [rk 1 (by decide)]; (try simp) <;> omega) (by rw [rk 1 (by decide)]; (try simp) <;> omega),
      ← hH0, bget_bset_eq _ _ _ _ rfl (by rw [rk 1 (by decide)]; simp [length_bset, ← hG1]; omega)]
  have q3 : bget H (d7 + 8 * st.defs.length.toUInt64 + 3) = bget g (d7 + 8 * st.defs.length.toUInt64 + 3) := by
    rw [cH _ (by rw [rk 3 (by decide)]; (try simp) <;> omega) (by rw [rk 3 (by decide)]; (try simp) <;> omega) (by rw [rk 3 (by decide)]; (try simp) <;> omega)
      (by rw [rk 3 (by decide)]; (try simp) <;> omega) (by rw [rk 3 (by decide)]; (try simp) <;> omega), e1 _ (by rw [rk 3 (by decide)]; (try simp) <;> omega)]
  have q4 : bget H (d7 + 8 * st.defs.length.toUInt64 + 4) = bget g (d7 + 8 * st.defs.length.toUInt64 + 4) := by
    rw [cH _ (by rw [rk 4 (by decide)]; (try simp) <;> omega) (by rw [rk 4 (by decide)]; (try simp) <;> omega) (by rw [rk 4 (by decide)]; (try simp) <;> omega)
      (by rw [rk 4 (by decide)]; (try simp) <;> omega) (by rw [rk 4 (by decide)]; (try simp) <;> omega), e1 _ (by rw [rk 4 (by decide)]; (try simp) <;> omega)]
  have ed : H.drop 184384 = G1.drop 184384 := by
    rw [← hH, ← hH0, drop_bset _ _ _ (by rw [rk 6 (by decide)]; (try simp) <;> omega), drop_bset _ _ _ (by rw [rk 2 (by decide)]; (try simp) <;> omega),
      drop_bset _ _ _ (by decide), drop_bset _ _ _ (by rw [ip]; (try simp) <;> omega), drop_bset _ _ _ (by rw [rk 1 (by decide)]; (try simp) <;> omega)]
  have wl : w.width < 2 ^ 64 := by omega
  have RC := rep_cur (h := G1) (h' := H) R2 hfs
    { st.cur with npw := if n1 then st.cur.npw else st.cur.npw + w.width, params := st.cur.params ++ [w],
                  nni := if n1 then st.cur.nni else st.cur.nni + 1 } 1 rfl
    (fun i hi => by exact ⟨by simp; omega, by simp [List.getElem_append_left hi]⟩) (by simp) (by rw [g27]; omega) lH ed
    (fun i a b c => by
      rw [g27] at c
      exact cH i (by omega) (by omega) (by omega) a (by omega))
    (by rw [q27, g27]; simp; omega)
    (by
      rw [q1, ← hQ, c1]
      apply UInt64.toNat_inj.mp
      cases n1 <;> simp [b01] <;> omega)
    (by
      rw [q2]; simp only []
      cases n1
      · simp only [b01, Bool.false_eq_true, if_false, UInt64.sub_zero]
        rw [UInt64.toNat_add, c2]; simp only [show (1 : UInt64).toNat = 1 from rfl]; omega
      · simp only [b01, if_true, UInt64.add_sub_cancel]; exact c2)
    (by rw [q3]; exact (c3.frame es').frame es) (by rw [q4]; exact c4)
    (by rw [q6]; simp only []; rw [UInt64.toNat_add]; simp only [show (1 : UInt64).toNat = 1 from rfl]; rw [c6]; simp; omega)
    (fun i hi => by
      have i0 : i = 0 := by omega
      subst i0
      simp only [g27, show (0 : Nat).toUInt64 = 0 from rfl, UInt64.add_zero, qP, Nat.add_zero]
      simp
      exact (sw.frame es').frame es)
  have hp7 : (bget g 3).toNat ≤ (bget g 7).toNat := hK.le
  have it : (d11 + bget g 3).toNat = 184384 + (bget g 3).toNat := by
    rw [UInt64.toNat_add, show d11.toNat = 184384 from rfl]; omega
  have p3 : bget H 3 = bget g 3 := by
    rw [cH 3 (by (try simp) <;> omega) (by (try simp) <;> omega) (by (try simp) <;> omega) (by decide) (by (try simp) <;> omega),
      e1 3 (by decide)]
  have pt : bget H (d11 + bget g 3) = 17 := by
    rw [cH _ (by rw [it]; omega) (by rw [it]; omega) (by rw [it]; omega) (by rw [it]; omega) (by rw [it]; omega),
      e1 _ (by rw [it]; omega), t17]
  have hKH : TokAt H (bget g 3) st.toks := by rw [← p3]; exact RC.2.2.2.1
  obtain ⟨rest, et, kr⟩ := tok_kw hKH RC.1 RC.2.1 pt (by decide) (by decide) (by decide)
  have R3 := rep_cursor RC (bget g 3 + 1) kr
  have hs1 : bget (v1 (bset H 3 (bget g 3 + 1)) 74 0 0) 0 ≠ 0 := fun e => hs (v1_zero _ _ _ _ e)
  have R4 := rep_push .stateTy 0 0 R3 (by simp [inDefF, Frame.isDefs]) trivial hs1
  have R5 := rep_push .tyAtom 0 0 R4 (by simp [inDefF, Frame.isDefs]) trivial hs
  refine ⟨[.tyAtom, .stateTy], _, ?_, R5⟩
  simp only [show (17 : UInt64).toNat = 17 from rfl] at et
  rw [← hn1']
  simp [stepF, et, hty, hw]

end ParInv
