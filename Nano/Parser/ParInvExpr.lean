/- Nano/Parser/ParInvExpr: Layer-3 handler preservation, EXPRESSION core (box C).
Shape of every lemma: `Rep h ts st (f :: fs) → st.acc = false → bget (step h) 0 ≠ 0 →
  ∃ k st', stepF f st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs)`. -/
import Nano.Parser.ParInvStep
namespace ParInv
open C BufL ParSpec ParRun

theorem rep_bounds {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) :
    (bget h 7).toNat < 2 ^ 32 ∧ 184384 ≤ h.length ∧ st.arena.length ≤ 16384 := by
  obtain ⟨rT, rts, _, _, _, _, _, rA, _, _, _, _, rO, _⟩ := r
  exact ⟨by rw [rT.2.2.2]; simp; omega, by rw [rO.1]; omega, rA.2.1⟩

/-- two pushes on top of a popped stack: the cells outside h[5] and the two new records are unchanged -/
theorem push2_cells (h : Buf) (c1 a1 b1 c2 a2 b2 : UInt64) (hg : (bget h 5).toNat + 1 < 4096) (hl : 12352 ≤ h.length) :
    let h' := v1 (v1 h c1 a1 b1) c2 a2 b2
    h'.length = h.length ∧ (∀ i : UInt64, i.toNat ≠ 5 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) → bget h' i = bget h i) := by
  intro h'
  obtain ⟨L1, _, E1, U1⟩ := v1_eff h c1 a1 b1 (by omega) hl
  have e1 : (bget (v1 h c1 a1 b1) 5).toNat = (bget h 5).toNat + 1 := by rw [E1, tn_add _ _ (by simp; omega)]; simp
  obtain ⟨L2, _, _, U2⟩ := v1_eff (v1 h c1 a1 b1) c2 a2 b2 (by omega) (by rw [L1]; exact hl)
  refine ⟨by rw [L2, L1], fun i h5 hi => ?_⟩
  have q1 : i.toNat < 64 + 3 * (bget (v1 h c1 a1 b1) 5).toNat ∨ 64 + 3 * (bget (v1 h c1 a1 b1) 5).toNat + 3 ≤ i.toNat := by
    rcases hi with hi | hi
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have q2 : i.toNat < 64 + 3 * (bget h 5).toNat ∨ 64 + 3 * (bget h 5).toNat + 3 ≤ i.toNat := by
    rcases hi with hi | hi
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [U2 i h5 q1, U1 i h5 q2]

theorem drop_v1 (h : Buf) (c a b : UInt64) (hl : 184384 ≤ h.length) : (v1 h c a b).drop 184384 = h.drop 184384 := by
  unfold v1
  split
  · rename_i hg
    have hgN := UInt64.lt_iff_toNat_lt.mp hg
    simp only [show d12.toNat = 4096 from rfl] at hgN
    have c0 := taskCell (bget h 5).toNat hgN 0 (by decide); have c1 := taskCell (bget h 5).toNat hgN 1 (by decide)
    have c2 := taskCell (bget h 5).toNat hgN 2 (by decide)
    simp only [UInt64.add_zero, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl,
      show (2 : UInt64).toNat = 2 from rfl, UInt64.ofNat_toNat] at c0 c1 c2
    rw [drop_bset _ _ _ (by simp), drop_bset _ _ _ (by rw [c2]; omega), drop_bset _ _ _ (by rw [c1]; omega),
      drop_bset _ _ _ (by rw [c0]; omega)]
  · exact drop_bset _ _ _ (by simp)

/-! ## task 1: `expr m md` (v100 pushes binLoop m, then prim md) -/
theorem h_expr {h ts : Buf} {st : St} {m md : Nat} {fs : List Frame} (r : Rep h ts st (.expr m md :: fs))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.expr m md) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  have rT := r.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨E, ⟨ea, eb⟩, T1⟩ := step_top (ts := ts) rT (by omega) hn har
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  have ev : step h = v1 (v1 (bset h 5 fs.length.toUInt64) 2 a 0) 3 0 b := by rw [E]; simp [v96, v100]
  rw [ev] at hs ⊢
  have l1 : 12352 ≤ (bset h 5 fs.length.toUInt64).length := by simp [length_bset]; omega
  have o2 := v1_ok _ _ _ _ hs
  have o1 : (bget (bset h 5 fs.length.toUInt64) 5).toNat < 4096 :=
    v1_ok _ 2 a 0 (fun z => hs (v1_zero _ _ _ _ z))
  have fl := T1.2.1
  have n5 : (bget (bset h 5 fs.length.toUInt64) 5).toNat = fs.length := by
    rw [bget_bset_eq _ _ _ _ rfl (by simp; omega)]; simp; omega
  refine ⟨[.prim md, .binLoop m], st, rfl, ?_⟩
  have hn1 : (bget (bset h 5 fs.length.toUInt64) 7).toNat < 2 ^ 32 := by rw [bget_bset' _ _ _ _ (by decide)]; exact hn
  have T2 := tasks_push (.binLoop m) a 0 T1 (by omega) l1 hn1 har ea
  simp only [show (Frame.binLoop m).code.toUInt64 = 2 from rfl] at T2
  have T3 := tasks_push (.prim md) 0 b T2 (by rw [T2.1] at o2; simpa using o2)
    (by obtain ⟨L, _⟩ := v1_eff _ 2 a 0 o1 l1; rw [L]; exact l1)
    (by obtain ⟨_, _, _, U⟩ := v1_eff _ 2 a 0 o1 l1
        rw [U 7 (by decide) (Or.inl (by rw [n5, show (7 : UInt64).toNat = 7 from rfl]; omega))]; exact hn1) har eb
  simp only [show (Frame.prim md).code.toUInt64 = 3 from rfl] at T3
  have fl2 : fs.length + 1 < 4096 := by have := T2.1; rw [List.length_cons] at this; omega
  obtain ⟨PL, PU⟩ := push2_cells (bset h 5 fs.length.toUInt64) 2 a 0 3 0 b (by omega) l1
  refine rep_tasks r (by rw [PL]; simp [length_bset]) (fun i h5 hi => by rw [PU i h5 hi, bget_bset' _ _ _ _ (by simp; omega)]) ?_ T3
    (by simp [inDefF, Frame.isDefs])
  rw [drop_v1 _ _ _ _ (by obtain ⟨L, _⟩ := v1_eff _ 2 a 0 o1 l1; rw [L]; simp [length_bset]; omega),
    drop_v1 _ _ _ _ (by simp [length_bset]; omega), drop_bset _ _ _ (by simp)]

/-! ## tasks 4 / 8: expect `)` / `else` -/
theorem stat0 (h : Buf) (hl : 0 < h.length) : bget (bset h 0 0) 0 = 0 := bget_bset_eq _ _ _ _ rfl (by simpa using hl)

/-- the common shape of v106 / v110: the token at the cursor must be `T`, then the cursor advances -/
theorem expect_tok {h ts : Buf} {st : St} {f : Frame} {fs : List Frame} (T : UInt64) (r : Rep h ts st (f :: fs))
    (T0 : T ≠ 0) (T5 : T ≠ 5) (T14 : T ≠ 14) (hf : f.isDefs = false)
    (ev : ∀ a b, v96 (bset h 5 fs.length.toUInt64) f.code.toUInt64 a b =
      let h1 := bset h 5 fs.length.toUInt64
      if bget h1 (d11 + bget h1 3 + 0) == T then bset h1 3 (bget h1 3 + 1) else bset h1 0 0)
    (hs : bget (step h) 0 ≠ 0) :
    ∃ rest, st.toks = .k T.toNat :: rest ∧ Rep (step h) ts { st with toks := rest } fs := by
  obtain ⟨hn, hl, har⟩ := rep_bounds r
  have rT := r.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨E, _, T1⟩ := step_top (ts := ts) rT (by omega) hn har
  rw [E, ev] at hs ⊢
  simp only [] at hs ⊢
  have fl := T1.2.1
  have g3 : bget (bset h 5 fs.length.toUInt64) 3 = bget h 3 := bget_bset' _ _ _ _ (by decide)
  have p3 := r.2.2.2.1
  have hK : (bget h 3).toNat ≤ (bget h 7).toNat := p3.le
  have gc : bget (bset h 5 fs.length.toUInt64) (d11 + bget h 3 + 0) = bget h (d11 + bget h 3) := by
    rw [UInt64.add_zero]; exact bget_bset' _ _ _ _ (by rw [d11a _ (by omega), show (5 : UInt64).toNat = 5 from rfl]; omega)
  rw [g3, gc] at hs ⊢
  by_cases hc : bget h (d11 + bget h 3) = T
  · simp only [hc, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, tr⟩ := tok_kw p3 r.1 r.2.1 hc T0 T5 T14
    refine ⟨rest, et, ?_⟩
    have l1 : (bset h 5 fs.length.toUInt64).length = h.length := length_bset _ _ _
    have u3 : (3 : UInt64).toNat = 3 := rfl
    have u5 : (5 : UInt64).toNat = 5 := rfl
    have cells : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 3 → bget (bset (bset h 5 fs.length.toUInt64) 3 (bget h 3 + 1)) i = bget h i :=
      fun i a b => by rw [bget_bset' _ _ _ _ (by rw [u3]; omega), bget_bset' _ _ _ _ (by rw [u5]; omega)]
    have et' : TokAgree h (bset (bset h 5 fs.length.toUInt64) 3 (bget h 3 + 1)) :=
      ⟨cells 7 (by decide) (by decide), fun i hi => cells i (by omega) (by omega)⟩
    refine rep_tok r (by simp [length_bset]) (fun i a b _ => cells i a b) (by rw [drop_bset _ _ _ (by decide), drop_bset _ _ _ (by decide)])
      (by rw [bget_bset_eq _ _ _ _ rfl (by rw [l1, u3]; omega)]; exact tokAt_frame et' hn tr) ?_ (by simp [inDefF, hf])
    refine tasks_frame T1 (by rw [bget_bset' _ _ _ _ (by decide)]) (fun i a b => bget_bset' _ _ _ _ (by rw [u3]; omega))
      ⟨by rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide)], fun i hi => bget_bset' _ _ _ _ (by rw [u3]; omega)⟩
      (by rw [bget_bset' _ _ _ _ (by decide)]; exact hn) (fun i a _ => bget_bset' _ _ _ _ (by rw [u3]; omega))
      (fun i a _ => bget_bset' _ _ _ _ (by rw [u3]; omega)) har
  · have : (bget h (d11 + bget h 3) == T) = false := by simpa using hc
    simp only [this] at hs
    exact absurd (stat0 _ (by simp [length_bset]; omega)) hs

theorem h_rparen {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.rparen :: fs)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF .rparen st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨rest, et, rr⟩ := expect_tok 7 r (by decide) (by decide) (by decide) rfl (fun a b => by simp [Frame.code, v96, v106]) hs
  exact ⟨[], _, by simp [stepF, et], rr⟩

theorem h_ifElse {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.ifElse :: fs)) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF .ifElse st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨rest, et, rr⟩ := expect_tok 34 r (by decide) (by decide) (by decide) rfl (fun a b => by simp [Frame.code, v96, v110]) hs
  exact ⟨[], _, by simp [stepF, et], rr⟩

end ParInv
