/- Nano/V2Self/Proof/Parser/ParInvGroup: Layer 3, binding append `v6` on `Rep` (box G; for task 67 `group`, also usable for let binders).
`v6_eff`: the cells `v6` writes.  `rep_v6`: a `v6` that did not fail appends one (non-input) binding. -/
import Nano.V2Self.Proof.Parser.ParInvAtom
namespace ParInv
open C BufL ParSpec ParRun

theorem v6_eff (g : Buf) (x s w : UInt64) (n : Nat) (hn : bget g 4 = n.toUInt64) (hn2 : n < 1024) (hl : 184384 ≤ g.length) :
    let g' := v6 g x s w
    g'.length = g.length ∧ bget g' 4 = (n + 1).toUInt64 ∧
    bget g' (d9 + 4 * n.toUInt64) = x ∧ bget g' (d9 + 4 * n.toUInt64 + 1) = s ∧ bget g' (d9 + 4 * n.toUInt64 + 2) = w ∧
    bget g' (d9 + 4 * n.toUInt64 + 3) = 0 ∧
    (∀ i : UInt64, i.toNat ≠ 4 → (i.toNat < 180288 + 4 * n ∨ 180288 + 4 * n + 4 ≤ i.toNat) → bget g' i = bget g i) ∧
    g'.drop 184384 = g.drop 184384 := by
  intro g'
  have c0 := rowCell n hn2 0 (by decide); have c1 := rowCell n hn2 1 (by decide)
  have c2 := rowCell n hn2 2 (by decide); have c3 := rowCell n hn2 3 (by decide)
  simp only [UInt64.add_zero, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl,
    show (2 : UInt64).toNat = 2 from rfl, show (3 : UInt64).toNat = 3 from rfl, Nat.add_zero] at c0 c1 c2 c3
  have hlt : bget g 4 < d14 := by rw [hn, UInt64.lt_iff_toNat_lt]; simp [show d14.toNat = 1024 from rfl]; omega
  have u4 : (4 : UInt64).toNat = 4 := rfl
  have eg : g' = bset (bset (bset (bset (bset g (d9 + 4 * n.toUInt64) x) (d9 + 4 * n.toUInt64 + 1) s) (d9 + 4 * n.toUInt64 + 2) w)
      (d9 + 4 * n.toUInt64 + 3) 0) 4 (n.toUInt64 + 1) := by
    show v6 g x s w = _
    unfold v6
    simp only [hlt, if_true]
    rw [bget_bset' _ _ 4 _ (by rw [hn, c3, u4]; omega), bget_bset' _ _ 4 _ (by rw [hn, c2, u4]; omega),
      bget_bset' _ _ 4 _ (by rw [hn, c1, u4]; omega), bget_bset' _ _ 4 _ (by rw [hn, c0, u4]; omega), hn]
  rw [eg]
  refine ⟨by simp [length_bset], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bget_bset_eq _ _ _ _ rfl (by simp [length_bset]; omega)]; simp
  · rw [bget_bset' _ _ _ _ (by rw [c0, u4]; omega), bget_bset' _ _ _ _ (by rw [c3, c0]; omega),
      bget_bset' _ _ _ _ (by rw [c2, c0]; omega), bget_bset' _ _ _ _ (by rw [c1, c0]; omega),
      bget_bset_eq _ _ _ _ rfl (by rw [c0]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [c1, u4]; omega), bget_bset' _ _ _ _ (by rw [c3, c1]; omega),
      bget_bset' _ _ _ _ (by rw [c2, c1]; omega), bget_bset_eq _ _ _ _ rfl (by simp only [length_bset]; rw [c1]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [c2, u4]; omega), bget_bset' _ _ _ _ (by rw [c3, c2]; omega),
      bget_bset_eq _ _ _ _ rfl (by simp only [length_bset]; rw [c2]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [c3, u4]; omega), bget_bset_eq _ _ _ _ rfl (by simp only [length_bset]; rw [c3]; omega)]
  · intro i i4 hi
    rw [bget_bset' _ _ _ _ (by rw [u4]; omega), bget_bset' _ _ _ _ (by rw [c3]; omega), bget_bset' _ _ _ _ (by rw [c2]; omega),
      bget_bset' _ _ _ _ (by rw [c1]; omega), bget_bset' _ _ _ _ (by rw [c0]; omega)]
  · rw [drop_bset0 _ _ _ (by decide), drop_bset0 _ _ _ (by rw [c3]; omega), drop_bset0 _ _ _ (by rw [c2]; omega),
      drop_bset0 _ _ _ (by rw [c1]; omega), drop_bset0 _ _ _ (by rw [c0]; omega)]

theorem v6_ok (g : Buf) (x s w : UInt64) (hl : 0 < g.length) (hs : bget (v6 g x s w) 0 ≠ 0) : (bget g 4).toNat < 1024 := by
  by_cases hc : bget g 4 < d14
  · exact UInt64.lt_iff_toNat_lt.mp hc
  · exfalso; apply hs; unfold v6; simp only [hc, if_false]; exact stat0 _ hl

/-- **binding append**: a `v6` that leaves the status nonzero adds one non-input binding row -/
theorem rep_v6 {g ts : Buf} {st : St} {fs : List Frame} (R : Rep g ts st fs) (x s w : UInt64) (name : List Nat) (slot : Nat)
    (sh : Option Sh) (hx : NameAt g x name) (hsl : s = slot.toUInt64) (hw : ShOpt g w sh) (hs : bget (v6 g x s w) 0 ≠ 0) :
    Rep (v6 g x s w) ts { st with binds := st.binds ++ [⟨name, slot, sh, false⟩] } fs := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds R
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := R
  obtain ⟨b4, bl, brows⟩ := rB
  have hlt := v6_ok g x s w (by omega) hs
  rw [b4] at hlt
  have hn : bget g 4 = st.binds.length.toUInt64 := by rw [← b4]; simp
  obtain ⟨L, e4, c0, c1, c2, c3, U, D⟩ := v6_eff g x s w st.binds.length hn hlt hl
  have e : ∀ i : UInt64, i.toNat ≠ 4 → (i.toNat < 180288 ∨ 184384 ≤ i.toNat) → bget (v6 g x s w) i = bget g i :=
    fun i a b => U i a (by omega)
  have et : TokAgree g (v6 g x s w) := ⟨e 7 (by decide) (Or.inl (by decide)), fun i hi => e i (by omega) (Or.inr hi)⟩
  have es : ShTabAgree g (v6 g x s w) := fun i a _ => e i (by omega) (Or.inl (by omega))
  have cc : ∀ n : UInt64, n.toNat < 64 → n.toNat ≠ 4 → bget (v6 g x s w) n = bget g n := fun n a b => e n b (Or.inl (by omega))
  refine ⟨tokensAt_frame rT et rts, rts, by rw [cc 0 (by decide) (by decide)]; exact r0,
    by rw [cc 3 (by decide) (by decide)]; exact tokAt_frame et hn7 r3, by rw [cc 11 (by decide) (by decide)]; exact r11,
    ⟨by rw [e4]; simp; omega, by simp; omega, fun i hi => ?_⟩,
    defs_frame rD (cc 12 (by decide) (by decide)) (cc 27 (by decide) (by decide)) (cc 26 (by decide) (by decide)) (fun i a b => e i (by omega) (Or.inl (by omega))) et hn7 es,
    arena_frame rA (cc 8 (by decide) (by decide)) (cc 9 (by decide) (by decide)) (fun i a b => e i (by omega) (Or.inl (by omega))) es,
    fun s' hs' => by rw [cc 25 (by decide) (by decide)]; exact (r25 s' hs').frame es,
    fun y hy => by rw [cc 29 (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 y hy),
    by rw [cc 30 (by decide) (by decide)]; exact r30, by rw [cc 32 (by decide) (by decide)]; exact r32, out_frame rO D,
    tasks_frame rK (cc 5 (by decide) (by decide)) (fun i a b => e i (by omega) (Or.inl (by have := rK.2.1; omega))) et hn7 es
      (fun i a b => e i (by omega) (Or.inl (by omega))) har⟩
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hin : i < st.binds.length
  · have c : ∀ k : UInt64, k.toNat < 4 → bget (v6 g x s w) (d9 + 4 * i.toUInt64 + k) = bget g (d9 + 4 * i.toUInt64 + k) :=
      fun k hk => U _ (by rw [rowCell i (by omega) k hk]; omega) (Or.inl (by rw [rowCell i (by omega) k hk]; omega))
    have c0' := c 0 (by decide); simp only [UInt64.add_zero] at c0'
    obtain ⟨a0, a1, a2, a3⟩ := brows i hin
    simp only [List.getElem_append_left hin]
    exact ⟨by rw [c0']; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1,
      by rw [c 2 (by decide)]; exact a2.frame es, by rw [c 3 (by decide)]; exact a3⟩
  · have : i = st.binds.length := by omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    exact ⟨by rw [c0]; exact nameAt_frame et (by omega) hx, by rw [c1]; exact hsl, by rw [c2]; exact hw.frame es, by rw [c3]; rfl⟩

/-! ## task 67: `group start` (v132) -/
theorem v1_cell4 (h : Buf) (c a b : UInt64) : bget (v1 h c a b) 4 = bget h 4 := by
  unfold v1
  split
  · rename_i hg
    have hgN := UInt64.lt_iff_toNat_lt.mp hg
    simp only [show d12.toNat = 4096 from rfl] at hgN
    have c0 := taskCell (bget h 5).toNat hgN 0 (by decide); have c1 := taskCell (bget h 5).toNat hgN 1 (by decide)
    have c2 := taskCell (bget h 5).toNat hgN 2 (by decide)
    simp only [UInt64.add_zero, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl,
      show (2 : UInt64).toNat = 2 from rfl, UInt64.ofNat_toNat] at c0 c1 c2
    have u4 : (4 : UInt64).toNat = 4 := rfl
    rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by rw [c2, u4]; omega), bget_bset' _ _ _ _ (by rw [c1, u4]; omega),
      bget_bset' _ _ _ _ (by rw [c0, u4]; omega)]
  · exact bget_bset' _ _ _ _ (by decide)

theorem h_group {h ts : Buf} {st : St} {start : Nat} {fs : List Frame} (r : Rep h ts st (.group start :: fs))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF (.group start) st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, ea, R1⟩ := rep_pop r rfl
  simp only [Frame.code, FrameArgs] at E ea
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rT := R1.1; have rts := R1.2.1; have r3 := R1.2.2.2.1
  have rB4 : (bget g 4).toNat = st.binds.length := R1.2.2.2.2.2.1.1
  have h7 : (bget g 7).toNat < 2 ^ 24 := by rw [rT.2.2.2]; simp; omega
  have p3 := r3.le
  by_cases c14 : bget g (d11 + bget g 3) = 14
  · obtain ⟨nm, rest, et, hNm, tr⟩ := tok_id r3 rT c14
    have ev : step h = v1 (v6 (v86 16777216 g (bget g 3 + 1)) (bget g 3) 0 0) 67 a 0 := by rw [E]; simp [v96, v132, c14]
    have hskip := v86_skip nm 16777216 g (bget g 3 + 1) hNm.2.1
      (by rw [tn_add _ _ (by simp; omega)]; have := hNm.2.2; simp; omega) (by have := hNm.2.2; omega)
    rw [ev, hskip] at hs ⊢
    have epos : bget g 3 + 1 + 2 * nm.length.toUInt64 + 1 = bget g 3 + 2 + 2 * nm.length.toUInt64 := by
      rw [show (2 : UInt64) = 1 + 1 from rfl]; ac_rfl
    have R2 := rep_cursor R1 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1) (by rw [epos]; exact tr)
    have et3 : TokAgree g (bset g 3 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1)) :=
      ⟨bget_bset' _ _ _ _ (by decide), fun i hi => bget_bset' _ _ _ _ (by simp; omega)⟩
    have hx : NameAt (bset g 3 (bget g 3 + 1 + 2 * nm.length.toUInt64 + 1)) (bget g 3) (nm.map UInt64.toNat) :=
      nameAt_frame et3 (by omega) ⟨nm, hNm, rfl⟩
    have R3 := rep_v6 R2 (bget g 3) 0 0 (nm.map UInt64.toNat) 0 none hx rfl rfl (fun z => hs (v1_zero _ _ _ _ z))
    have R4 := rep_push (.group start) a 0 R3 rfl ea hs
    exact ⟨[.group start], _, by simp [stepF, et], R4⟩
  by_cases c8 : bget g (d11 + bget g 3) = 8
  · have g4 : ∀ v, bget (bset g 3 v) 4 = bget g 4 := fun v => bget_bset' _ _ _ _ (by decide)
    have ev : step h = (if a < bget g 4 then
        v1 (v1 (v1 (v1 (bset g 3 (bget g 3 + 1)) 66 0 0) 68 a (bget g 4 - a)) 4 0 0) 61 0 0 else bset (bset g 3 (bget g 3 + 1)) 0 0) := by
      rw [E]; simp [v96, v132, c8, g4, v1_cell4]
    rw [ev] at hs ⊢
    by_cases ca : a < bget g 4
    · rw [if_pos ca] at hs ⊢
      have ca' := UInt64.lt_iff_toNat_lt.mp ca
      rw [ea, rB4] at ca'
      obtain ⟨rest, et, tr⟩ := tok_kw r3 rT rts c8 (by decide) (by decide) (by decide)
      have R2 := rep_cursor R1 (bget g 3 + 1) tr
      have esz : (bget g 4 - a).toNat = st.binds.length - start := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega
      have R3 := rep_push .binders 0 0 R2 rfl trivial (fun z => hs (v1_zero _ _ _ _ (v1_zero _ _ _ _ (v1_zero _ _ _ _ z))))
      have R4 := rep_push (.assign start (st.binds.length - start)) a (bget g 4 - a) R3 rfl ⟨ea, esz⟩
        (fun z => hs (v1_zero _ _ _ _ (v1_zero _ _ _ _ z)))
      have R5 := rep_push .rparen 0 0 R4 rfl trivial (fun z => hs (v1_zero _ _ _ _ z))
      have R6 := rep_push .tyAtom 0 0 R5 rfl trivial hs
      exact ⟨[.tyAtom, .rparen, .assign start (st.binds.length - start), .binders], { st with toks := rest },
        by simp [stepF, et, ca'], R6⟩
    · rw [if_neg ca] at hs; exact absurd (stat0 _ (by simp [length_bset]; omega)) hs
  · have ev : step h = bset g 0 0 := by rw [E]; simp [v96, v132, c14, c8]
    rw [ev] at hs; exact absurd (stat0 _ (by omega)) hs

end ParInv
