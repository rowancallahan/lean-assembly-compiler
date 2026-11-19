/- Nano/V2Self/Proof/ParInvPair: PAIR INTERNING `v10` on `Rep` (box G; task 63 `tyPair`, and `mkPair` 42 for box C).
`v10_alloc`: the allocation step as one heap (`allocHeap`), `v10_dead` its failures, `alloc_eff` its cells. -/
import Nano.V2Self.Proof.ParInvShP
import Nano.V2Self.Proof.ParInvIntern
namespace ParInv
open C BufL ParSpec ParRun

/-- v9's width word of code `s` read from `h` -/
def v9w (h : Buf) (s : UInt64) : UInt64 := if s < 5 then 1 else bget h ((d7 + 8192) + 3 * (s - 5) + 2)

/-- the heap after allocating pair row `n` = (x, y, zx + zy): scratch 31, the row, h[26] := n + 1, h[25] := n + 5 -/
def allocHeap (g : Buf) (x y zx zy : UInt64) (n : Nat) : Buf :=
  bset (bset (bset (bset (bset (bset (bset g 31 zx) 31 zy) (d7 + 8192 + 3 * n.toUInt64) x) (d7 + 8192 + 3 * n.toUInt64 + 1) y)
    (d7 + 8192 + 3 * n.toUInt64 + 2) (zx + zy)) 26 (n.toUInt64 + 1)) 25 (n.toUInt64 + 5)

theorem v10_alloc (g : Buf) (x y : UInt64) (n : Nat) (hn : bget g 26 = n.toUInt64) (hx4 : x ≠ 4) (hy4 : y ≠ 4) (hcap : n < 8192)
    (hl : 31 < g.length) (hw : ¬ (1048575 : UInt64) < v9w g x + v9w (bset g 31 (v9w g x)) y) :
    v10 1 g x y n.toUInt64 = allocHeap g x y (v9w g x) (v9w (bset g 31 (v9w g x)) y) n := by
  have hc : n.toUInt64 < d15 := by rw [UInt64.lt_iff_toNat_lt]; simp [show d15.toNat = 8192 from rfl]; omega
  have hw' := hw; simp only [v9w, bb31 g hl, bb31' g hl] at hw'
  rw [v10]
  simp only [hn, beq_self_eq_true, if_true, beq_iff_eq, hx4, hy4, if_false, hc, v9, allocHeap, v9w, bb31 g hl, bb31' g hl, hw']

/-- WIDTH CAP: a pair of width ≥ 2^20 is not allocated (status 0) -/
theorem v10_capdead (g : Buf) (x y : UInt64) (n : Nat) (hn : bget g 26 = n.toUInt64) (hx4 : x ≠ 4) (hy4 : y ≠ 4) (hcap : n < 8192)
    (hl : 31 < g.length) (hw : (1048575 : UInt64) < v9w g x + v9w (bset g 31 (v9w g x)) y) :
    bget (v10 1 g x y n.toUInt64) 0 = 0 := by
  have hc : n.toUInt64 < d15 := by rw [UInt64.lt_iff_toNat_lt]; simp [show d15.toNat = 8192 from rfl]; omega
  have hw' := hw; simp only [v9w, bb31 g hl, bb31' g hl] at hw'
  rw [v10]
  simp only [hn, beq_self_eq_true, if_true, beq_iff_eq, hx4, hy4, if_false, hc, v9, bb31 g hl, bb31' g hl, hw']
  exact stat0 _ (by simp [length_bset]; omega)

theorem v10_dead (g : Buf) (x y : UInt64) (n : Nat) (hn : bget g 26 = n.toUInt64) (hn2 : n < 2 ^ 32) (hl : 0 < g.length)
    (hf : x = 4 ∨ y = 4 ∨ ¬ n < 8192) : bget (v10 1 g x y n.toUInt64) 0 = 0 := by
  rw [v10]
  simp only [hn, beq_self_eq_true, if_true, beq_iff_eq]
  by_cases hx : x = 4
  · simp only [hx, if_true]; exact stat0 _ hl
  by_cases hy : y = 4
  · simp only [hx, hy, if_true, if_false]; exact stat0 _ hl
  have hc : ¬ n.toUInt64 < d15 := by
    rcases hf with h | h | h
    · exact absurd h hx
    · exact absurd h hy
    · rw [UInt64.lt_iff_toNat_lt]; intro q; apply h
      have e : n.toUInt64.toNat = n := by simp; omega
      rw [e, show d15.toNat = 8192 from rfl] at q
      exact q
  simp only [hx, hy, hc, if_false]; exact stat0 _ hl

theorem alloc_eff (g : Buf) (x y zx zy : UInt64) (n : Nat) (hcap : n < 8192) (hl : 184384 ≤ g.length) :
    ∀ G, G = allocHeap g x y zx zy n →
    G.length = g.length ∧ bget G 25 = n.toUInt64 + 5 ∧ bget G 26 = n.toUInt64 + 1 ∧
    bget G (d7 + 8192 + 3 * n.toUInt64) = x ∧ bget G (d7 + 8192 + 3 * n.toUInt64 + 1) = y ∧
    bget G (d7 + 8192 + 3 * n.toUInt64 + 2) = zx + zy ∧
    (∀ j : UInt64, j.toNat ≠ 25 → j.toNat ≠ 26 → j.toNat ≠ 31 → (j.toNat < 155712 + 3 * n ∨ 155712 + 3 * n + 3 ≤ j.toNat) →
      bget G j = bget g j) ∧
    G.drop 184384 = g.drop 184384 := by
  intro G hG
  subst hG
  have b0 := shRow0 n hcap
  have b1 := shRowK n hcap 1 (by decide); have b2 := shRowK n hcap 2 (by decide)
  simp only [show (1 : UInt64).toNat = 1 from rfl, show (2 : UInt64).toNat = 2 from rfl] at b1 b2
  have u25 : (25 : UInt64).toNat = 25 := rfl
  have u26 : (26 : UInt64).toNat = 26 := rfl
  have u31 : (31 : UInt64).toNat = 31 := rfl
  unfold allocHeap
  refine ⟨by simp only [length_bset], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [u25]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [u25, u26]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [u26]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [u25, b0]; omega), bget_bset' _ _ _ _ (by rw [u26, b0]; omega), bget_bset' _ _ _ _ (by rw [b2, b0]; omega), bget_bset' _ _ _ _ (by rw [b1, b0]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [b0]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [u25, b1]; omega), bget_bset' _ _ _ _ (by rw [u26, b1]; omega), bget_bset' _ _ _ _ (by rw [b2, b1]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [b1]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [u25, b2]; omega), bget_bset' _ _ _ _ (by rw [u26, b2]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [b2]; omega)]
  · intro j j25 j26 j31 jrow
    rw [bget_bset' _ _ _ _ (by rw [u25]; omega), bget_bset' _ _ _ _ (by rw [u26]; omega), bget_bset' _ _ _ _ (by rw [b2]; omega), bget_bset' _ _ _ _ (by rw [b1]; omega), bget_bset' _ _ _ _ (by rw [b0]; omega), bget_bset' _ _ _ _ (by rw [u31]; omega), bget_bset' _ _ _ _ (by rw [u31]; omega)]
  · rw [drop_bset _ _ _ (by decide), drop_bset _ _ _ (by decide), drop_bset _ _ _ (by rw [b2]; omega), drop_bset _ _ _ (by rw [b1]; omega),
      drop_bset _ _ _ (by rw [b0]; omega), drop_bset _ _ _ (by decide), drop_bset _ _ _ (by decide)]

theorem pairCode {h : Buf} {i : Nat} (hi : i < 8192) {x y : UInt64} {l r : Sh}
    (e0 : bget h (d7 + 8192 + 3 * i.toUInt64) = x) (e1 : bget h (d7 + 8192 + 3 * i.toUInt64 + 1) = y)
    (e2 : bget h (d7 + 8192 + 3 * i.toUInt64 + 2) = (l.width + r.width).toUInt64) (sa : ShapeCode h x l) (sb : ShapeCode h y r) :
    ShapeCode h (i.toUInt64 + 5) (.p l r) := by
  have t5 : (i.toUInt64 + 5).toNat = i + 5 := by rw [tn_add _ _ (by simp; omega)]; simp; omega
  have e5 : i.toUInt64 + 5 - 5 = i.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [t5]; simp))]; rw [t5]; simp; omega
  exact .pr (by rw [t5]; omega) (by rw [t5]; omega) (by rw [e5]; exact e0) (by rw [e5]; exact e1) (by rw [e5]; exact e2) sa sb

/-- **pair interning on Rep**: a `v10` that does not fail leaves h[25] = the code of `.p l r` (an existing row, or a new one);
neither component is Nat -/
theorem rep_intern {g ts : Buf} {st : St} {fs : List Frame} (R : Rep g ts st fs) (x y : UInt64) (l r : Sh)
    (hx : ShapeCode g x l) (hy : ShapeCode g y r) (hlw : l.width < 2 ^ 20) (hrw : r.width < 2 ^ 20)
    (hs : bget (v10 16777216 g x y 0) 0 ≠ 0) :
    l ≠ .nt ∧ r ≠ .nt ∧ l.width + r.width < 2 ^ 20 ∧ Rep (v10 16777216 g x y 0) ts { st with ty := some (.p l r) } fs := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds R
  obtain ⟨d12, dl, d27, drows, dcur, dzero, dz0, s26, sz, sd⟩ := R.2.2.2.2.2.2.1
  have hn : bget g 26 = (bget g 26).toNat.toUInt64 := by simp
  generalize hnn : (bget g 26).toNat = n at hn s26 sz sd
  have hsc := v10_scan g x y n hn (by omega) n 16777216 0 (by omega) (by omega)
  simp only [show (0 : Nat).toUInt64 = 0 from rfl] at hsc
  rcases hsc with ⟨i, _, hin, hrow, _, hv⟩ | ⟨_, hv⟩
  · rw [hv] at hs ⊢
    obtain ⟨l', r', sa, sb, sw, hl', hr'⟩ := sd i hin
    rw [hrow.1] at sa; rw [hrow.2] at sb
    have el := ShapeCode.det sa hx; have er := ShapeCode.det sb hy
    subst el er
    by_cases hw : (1048575 : UInt64) < bget g (d7 + 8192 + 3 * i.toUInt64 + 2)
    · rw [if_pos hw] at hs; exact absurd (stat0 _ (by omega)) hs
    rw [if_neg hw] at hs ⊢
    have hsum : l'.width + r'.width < 2 ^ 20 := by
      rw [sw, UInt64.lt_iff_toNat_lt, show (1048575 : UInt64).toNat = 1048575 from rfl, Nat.toUInt64, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega)] at hw
      omega
    exact ⟨hl', hr', hsum, rep_ty R _ _ (pairCode (by omega) hrow.1 hrow.2 sw sa sb)⟩
  · rw [hv] at hs ⊢
    by_cases hx4 : x = 4
    · exact absurd (v10_dead g x y n hn (by omega) (by omega) (Or.inl hx4)) hs
    by_cases hy4 : y = 4
    · exact absurd (v10_dead g x y n hn (by omega) (by omega) (Or.inr (Or.inl hy4))) hs
    have hcap : n < 8192 := by
      by_cases hcap : n < 8192
      · exact hcap
      · exact absurd (v10_dead g x y n hn (by omega) (by omega) (Or.inr (Or.inr hcap))) hs
    have hlnt : l ≠ .nt := fun e => hx4 (e ▸ hx).nt_code
    have hrnt : r ≠ .nt := fun e => hy4 (e ▸ hy).nt_code
    have ezx : v9w g x = l.width.toUInt64 := v9_cw (o := some l) hx
    have c31 : ∀ (z j : UInt64), j.toNat ≠ 31 → bget (bset g 31 z) j = bget g j := fun z j a => bget_bset' _ _ _ _ (by simp; omega)
    have ezy : v9w (bset g 31 (v9w g x)) y = r.width.toUInt64 :=
      v9_cw (o := some r) (hy.frame (fun j a _ => c31 _ j (by omega)))
    have ewid0 : l.width.toUInt64 + r.width.toUInt64 = (l.width + r.width).toUInt64 := by simp
    have hwc : ¬ (1048575 : UInt64) < v9w g x + v9w (bset g 31 (v9w g x)) y :=
      fun hw => absurd (v10_capdead g x y n hn hx4 hy4 hcap (by omega) hw) hs
    rw [v10_alloc g x y n hn hx4 hy4 hcap (by omega) hwc, ezy, ezx] at hs ⊢
    have hsum : l.width + r.width < 2 ^ 20 := by
      have q := hwc
      rw [ezy, ezx, ewid0, UInt64.lt_iff_toNat_lt] at q
      simp only [Nat.toUInt64, UInt64.toNat_ofNat', show (1048575 : UInt64).toNat = 1048575 from rfl,
        Nat.mod_eq_of_lt (show l.width + r.width < 2 ^ 64 by omega)] at q
      omega
    obtain ⟨L, e25, e26, eb0, eb1, eb2, U, Dr⟩ := alloc_eff g x y l.width.toUInt64 r.width.toUInt64 n hcap hl _ rfl
    generalize allocHeap g x y l.width.toUInt64 r.width.toUInt64 n = G at L e25 e26 eb0 eb1 eb2 U Dr ⊢
    obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := R
    have cS : ∀ j : UInt64, j.toNat < 64 → j.toNat ≠ 25 → j.toNat ≠ 26 → j.toNat ≠ 31 → bget G j = bget g j :=
      fun j a b c d => U j b c d (Or.inl (by omega))
    have cLo : ∀ j : UInt64, 64 ≤ j.toNat → j.toNat < 155712 → bget G j = bget g j :=
      fun j a b => U j (by omega) (by omega) (by omega) (Or.inl (by omega))
    have cHi : ∀ j : UInt64, 180288 ≤ j.toNat → bget G j = bget g j :=
      fun j a => U j (by omega) (by omega) (by omega) (Or.inr (by omega))
    have et : TokAgree g G := ⟨cS 7 (by decide) (by decide) (by decide) (by decide), fun j hj => cHi j (by omega)⟩
    have es : ShPres g G := shPres_alloc n sz (fun j a b => U j (by omega) (by omega) (by omega) (Or.inl b))
    have ewid : l.width.toUInt64 + r.width.toUInt64 = (l.width + r.width).toUInt64 := by simp
    have t26 : (bget G 26).toNat = n + 1 := by rw [e26, tn_add _ _ (by simp; omega)]; simp; omega
    have hsr : ShRows G := by
      refine ⟨by rw [t26]; omega, fun k h1 h2 => ?_, fun k hk => ?_⟩
      · rw [t26] at h1
        rw [U _ (by rw [shRow0 k h2]; omega) (by rw [shRow0 k h2]; omega) (by rw [shRow0 k h2]; omega)
          (Or.inr (by rw [shRow0 k h2]; omega))]
        exact sz k (by omega) h2
      · rw [t26] at hk
        by_cases hkn : k < n
        · obtain ⟨l', r', sa, sb, sw, hl', hr'⟩ := sd k hkn
          have cq : ∀ q : UInt64, q.toNat < 3 → bget G (d7 + 8192 + 3 * k.toUInt64 + q) = bget g (d7 + 8192 + 3 * k.toUInt64 + q) :=
            fun q hq => by
              have c := shRowK k (by omega) q hq
              exact U _ (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (Or.inl (by rw [c]; omega))
          have cq0 := cq 0 (by decide); simp only [UInt64.add_zero] at cq0
          exact ⟨l', r', by rw [cq0]; exact es _ _ sa, by rw [cq 1 (by decide)]; exact es _ _ sb, by rw [cq 2 (by decide)]; exact sw,
            hl', hr'⟩
        · have : k = n := by omega
          subst this
          exact ⟨l, r, by rw [eb0]; exact es _ _ hx, by rw [eb1]; exact es _ _ hy, by rw [eb2]; exact ewid, hlnt, hrnt⟩
    refine ⟨hlnt, hrnt, hsum, tokensAt_frame rT et rts, rts, by rw [cS 0 (by decide) (by decide) (by decide) (by decide)]; exact r0,
      by rw [cS 3 (by decide) (by decide) (by decide) (by decide)]; exact tokAt_frame et hn7 r3,
      by rw [cS 11 (by decide) (by decide) (by decide) (by decide)]; exact r11,
      binds_frameP rB (cS 4 (by decide) (by decide) (by decide) (by decide)) (fun j a _ => cHi j a) et hn7 es,
      defs_frameP rD (cS 12 (by decide) (by decide) (by decide) (by decide)) (cS 27 (by decide) (by decide) (by decide) (by decide))
        (fun j a b => cLo j (by omega) b) et hn7 es hsr,
      arena_frameP rA (cS 8 (by decide) (by decide) (by decide) (by decide)) (cS 9 (by decide) (by decide) (by decide) (by decide))
        (fun j a b => cLo j (by omega) (by omega)) es,
      fun s' hs' => ?_,
      fun z hz => by rw [cS 29 (by decide) (by decide) (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 z hz),
      by rw [cS 30 (by decide) (by decide) (by decide) (by decide)]; exact r30,
      by rw [cS 32 (by decide) (by decide) (by decide) (by decide)]; exact r32, out_frame rO Dr,
      tasks_frameP rK (cS 5 (by decide) (by decide) (by decide) (by decide)) (fun j a b => cLo j a (by have := rK.2.1; omega)) et hn7 es
        (fun j a b => cLo j (by omega) (by omega)) har⟩
    cases hs'
    rw [e25]
    exact pairCode hcap eb0 eb1 (by rw [eb2]; exact ewid) (es _ _ hx) (es _ _ hy)

/-! ## task 63: `tyPair l` (v130) -/
theorem h_tyPair {h ts : Buf} {st : St} {l : Sh} {fs : List Frame} (r : Rep h ts st (.tyPair l :: fs)) (hty : st.ty.isSome)
    (hl20 : l.width < 2 ^ 20) (hty20 : cw st.ty < 2 ^ 20) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF (.tyPair l) st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, ea, R1⟩ := rep_pop r rfl
  simp only [Frame.code, FrameArgs] at E ea
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E
  have ea' : ShapeCode (bset h 5 fs.length.toUInt64) a l := ea.frame (fun j a _ => bget_bset' _ _ _ _ (by simp; omega))
  generalize bset h 5 fs.length.toUInt64 = g at E R1 ea'
  obtain ⟨rr, hr⟩ := Option.isSome_iff_exists.mp hty
  have sc := R1.2.2.2.2.2.2.2.2.1 rr hr
  have ev : step h = v10 16777216 g a (bget g 25) 0 := by rw [E]; simp [v96, v130]
  rw [ev] at hs ⊢
  have hrw : rr.width < 2 ^ 20 := by rw [hr] at hty20; exact hty20
  obtain ⟨hl, hrn, hsum, R2⟩ := rep_intern R1 a (bget g 25) l rr ea' sc hl20 hrw hs
  refine ⟨[], _, ?_, R2⟩
  simp [stepF, hr, hl, hrn, show ¬ 2 ^ 20 ≤ l.width + rr.width by omega]

end ParInv
