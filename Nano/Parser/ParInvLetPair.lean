/- Nano/Parser/ParInvLetPair: Layer-3 handler `letPairSemi y tl` (task 53, v117), box C: `;` after a pair value, the two
binders (stashed name x at slot h[11] with the left shape, y right after it with the right shape), body in the tail mode, LET end.
Side conditions (Layer 2 / glue): `st.vals ≠ []`, `st.stash.isSome` (the `.stash` frame ran: it is pushed together with this frame). -/
import Nano.Parser.ParInvLetSemi
import Nano.Parser.ParInvMkPair
namespace ParInv
open C BufL ParSpec ParRun

/-- status 0 is absorbing for `v6` -/
theorem v6_stat (g : Buf) (x s w : UInt64) (hg : bget g 0 = 0) : bget (v6 g x s w) 0 = 0 := by
  unfold v6; split
  · rename_i hc
    have hcN := UInt64.lt_iff_toNat_lt.mp hc; simp only [show d14.toNat = 1024 from rfl] at hcN
    have rc := fun k (hk : k.toNat < 4) => rowCell (bget g 4).toNat hcN k hk
    rw [bget_bset' _ _ _ _ (by decide)]
    rw [bget_bset' _ _ _ _ (by have := rc 3 (by decide); simp at this ⊢; omega),
      bget_bset' _ _ _ _ (by have := rc 2 (by decide); simp at this ⊢; omega),
      bget_bset' _ _ _ _ (by have := rc 1 (by decide); simp at this ⊢; omega),
      bget_bset' _ _ _ _ (by have := rc 0 (by decide); simp at this ⊢; omega)]; exact hg
  · exact stat0' g

/-- `v6` writes the binding table, h[4] and (on overflow) the status: the shape table is untouched -/
theorem v6_shtab (g : Buf) (x s w : UInt64) : ShTabAgree g (v6 g x s w) := by
  intro i i1 i2
  unfold v6; split
  · rename_i hc
    have hcN := UInt64.lt_iff_toNat_lt.mp hc; simp only [show d14.toNat = 1024 from rfl] at hcN
    have rc := fun k (hk : k.toNat < 4) => rowCell (bget g 4).toNat hcN k hk
    simp only [UInt64.ofNat_toNat] at rc
    rw [bget_bset' _ _ _ _ (by simp; omega)]
    rw [bget_bset' _ _ _ _ (by have := rc 3 (by decide); simp at this ⊢; omega),
      bget_bset' _ _ _ _ (by have := rc 2 (by decide); simp at this ⊢; omega),
      bget_bset' _ _ _ _ (by have := rc 1 (by decide); simp at this ⊢; omega),
      bget_bset' _ _ _ _ (by have := rc 0 (by decide); simp at this ⊢; omega)]
  · exact bget_bset' _ _ _ _ (by simp; omega)

/-- a shape code above 4 is a pair row -/
theorem ShapeCode.pair_inv {h : Buf} {w : UInt64} {s : Sh} (r : ShapeCode h w s) (hw : 4 < w) :
    ∃ a b, s = .p a b ∧ ShapeCode h (bget h (d7 + 8192 + 3 * (w - 5))) a ∧ ShapeCode h (bget h (d7 + 8192 + 3 * (w - 5) + 1)) b := by
  have hw' := UInt64.lt_iff_toNat_lt.mp hw
  cases r with
  | uw => exact absurd hw' (by decide)
  | bf => exact absurd hw' (by decide)
  | ls => exact absurd hw' (by decide)
  | nt => exact absurd hw' (by decide)
  | pr _ _ e0 e1 _ sa sb => exact ⟨_, _, rfl, by rw [e0]; exact sa, by rw [e1]; exact sb⟩

/-! ## task 53: `letPairSemi y tl` (v117) -/
theorem h_letPairSemi {h ts : Buf} {st : St} {y : List Nat} {tl : Bool} {fs : List Frame}
    (r : Rep h ts st (.letPairSemi y tl :: fs)) (hv : st.vals ≠ []) (hst : st.stash.isSome) (hn20 : st.nx < 2 ^ 20)
    (hc20 : ∀ v ∈ st.vals, cw v.sh < 2 ^ 20) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF (.letPairSemi y tl) st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  subst eb
  have ea1 : NameAt (bset h 5 fs.length.toUInt64) a y := nameAt_ts r.1 R1.1 r.2.1 ea
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1 ea1
  have ev : step h = v117 h1 a (b01 tl) := by rw [E]; simp [Frame.code, v96]
  rw [ev] at hs ⊢
  simp only [v117, v9, UInt64.add_zero] at hs ⊢
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hst
  by_cases c13 : bget h1 (d11 + bget h1 3) = 13
  · simp only [c13, beq_self_eq_true, if_true] at hs ⊢
    obtain ⟨rest, et, R2⟩ := cur_tok R1 13 c13 (by decide) (by decide) (by decide)
    generalize hH2 : bset h1 3 (bget h1 3 + 1) = H2 at hs R2 ⊢
    have rA := R2.2.2.2.2.2.2.2.1
    obtain ⟨top, vs, evs⟩ : ∃ top vs, st.vals = top :: vs := by
      match hq : st.vals with
      | [] => exact absurd hq hv
      | top :: vs => exact ⟨top, vs, rfl⟩
    have l0 : 0 < st.vals.length := by rw [evs]; simp
    have o0 := opCell rA.2.2.1 rA.2.2.2.1 0 l0
    simp only [show ((0 : Nat) + 1).toUInt64 = 1 from rfl] at o0
    obtain ⟨_, rt⟩ := val_rep rA 0 l0
    have ft : ShOpt H2 (bget H2 (d5 + 8 * bget H2 (d3 + bget H2 8 - 1) + 3)) top.sh := by
      have := rt.fields.2.2.2.1; simp only [fld] at this; rw [o0]; simpa [evs] using this
    generalize ew : bget H2 (d5 + 8 * bget H2 (d3 + bget H2 8 - 1) + 3) = w at hs ft ⊢
    have s11 : bget H2 11 = st.nx.toUInt64 := R2.2.2.2.2.1
    have j4 : (bget H2 4).toNat = st.binds.length := R2.2.2.2.2.2.1.1
    rw [s11] at hs ⊢
    have hl2 := (rep_bounds R2).2.1
    have st4 : bget (v1 (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl)) 0 ≠ 0 := by
      intro z; apply hs
      have zb : ∀ (g : Buf) (k v : UInt64), k.toNat ≠ 0 → bget g 0 = 0 → bget (bset g k v) 0 = 0 :=
        fun g k v hk hg => by rw [bget_bset' _ _ _ _ (by simpa using hk)]; exact hg
      refine ite0 _ _ _ (stat0' _) ?_
      split
      · apply v6_stat; apply v6_stat; apply zb _ 31 _ (by decide); apply zb _ 11 _ (by decide); apply zb _ 31 _ (by decide); exact z
      · exact stat0' _
    have R3 := rep_push (.letEnd st.nx st.binds.length) st.nx.toUInt64 (bget H2 4) R2 (by simp [inDefF, Frame.isDefs])
      ⟨rfl, j4⟩ (pushOK st4)
    have R4 := rep_push (.expr 0 (bm tl)) 0 (b01 tl) R3 (by simp [inDefF, Frame.isDefs]) ⟨rfl, b01_toNat tl⟩ st4
    have o1 := v1_ok _ _ _ _ (pushOK st4)
    have o2 := v1_ok _ _ _ _ st4
    obtain ⟨_, a1, _⟩ := v1_agree H2 12 st.nx.toUInt64 (bget H2 4) o1 (by omega)
    obtain ⟨_, a2, _⟩ := v1_agree (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl) o2
      (by obtain ⟨L, _⟩ := v1_eff H2 12 st.nx.toUInt64 (bget H2 4) o1 (by omega); rw [L]; omega)
    have sh24 : ShTabAgree H2 (v1 (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl)) :=
      fun i x y => by rw [a2 i x y, a1 i x y]
    have R4' : Rep (v1 (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl)) ts { st with toks := rest }
        (.expr 0 (bm tl) :: .letEnd st.nx st.binds.length :: fs) := R4
    clear R4
    generalize hH4 : v1 (v1 H2 12 st.nx.toUInt64 (bget H2 4)) 1 0 (b01 tl) = H4 at hs R4' st4 sh24
    have R4 := R4'
    have l4 := (rep_bounds R4).2.1
    have ft4 : ShOpt H4 w top.sh := ft.frame sh24
    have eW := v9_cw ft4
    simp only [eW] at hs ⊢
    rw [bget_bset_eq _ _ _ _ rfl (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)] at hs ⊢
    have R5 := rep_31 R4 (cw top.sh).toUInt64
    have en : st.nx.toUInt64 + (cw top.sh).toUInt64 = (st.nx + cw top.sh).toUInt64 := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    rw [en] at hs ⊢
    by_cases ccap : (1048575 : UInt64) < (st.nx + cw top.sh).toUInt64
    · rw [if_pos ccap] at hs; exact absurd (stat0' _) hs
    rw [if_neg ccap] at hs ⊢
    have hcapN : ¬ 2 ^ 20 ≤ st.nx + cw top.sh := by
      have ht := hc20 top (by rw [evs]; simp)
      intro hle; apply ccap
      rw [UInt64.lt_iff_toNat_lt, show (1048575 : UInt64).toNat = 1048575 from rfl, Nat.toUInt64, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega)]
      omega
    have R6 := rep_set11 R5 (st.nx + cw top.sh)
    have sh6 : ShTabAgree H4 (bset (bset H4 31 (cw top.sh).toUInt64) 11 (st.nx + cw top.sh).toUInt64) :=
      fun i x y => by rw [bget_bset' _ _ _ _ (by rw [show (11 : UInt64).toNat = 11 from rfl]; omega),
        bget_bset' _ _ _ _ (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)]
    generalize hH6 : bset (bset H4 31 (cw top.sh).toUInt64) 11 (st.nx + cw top.sh).toUInt64 = H6 at hs R6 sh6 ⊢
    by_cases w4 : 4 < w
    · simp only [w4, if_true] at hs ⊢
      have ft6 : ShOpt H6 w top.sh := ft4.frame sh6
      cases hts : top.sh with
      | none => rw [hts] at ft6; simp only [ShOpt] at ft6; subst ft6; exact absurd w4 (by decide)
      | some sv =>
      rw [hts] at ft6
      obtain ⟨la, rb, epr, sl, sr⟩ := ShapeCode.pair_inv ft6 w4
      subst epr
      generalize cl : bget H6 (d7 + 8192 + 3 * (w - 5)) = L at sl hs ⊢
      generalize cr : bget H6 (d7 + 8192 + 3 * (w - 5) + 1) = Rr at sr hs ⊢
      have l6 := (rep_bounds R6).2.1
      have eWl := v9_cw (o := some la) sl
      rw [eWl] at hs ⊢
      rw [bget_bset_eq _ _ _ _ rfl (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)] at hs ⊢
      have R7 := rep_31 R6 (cw (some la)).toUInt64
      have sh7 : ShTabAgree H6 (bset H6 31 (cw (some la)).toUInt64) :=
        fun i x y => bget_bset' _ _ _ _ (by rw [show (31 : UInt64).toNat = 31 from rfl]; omega)
      have e29 : bget (bset H6 31 (cw (some la)).toUInt64) 29 = bget H6 29 :=
        bget_bset' _ _ _ _ (by decide)
      have hxN : NameAt (bset H6 31 (cw (some la)).toUInt64) (bget H6 29) x := by
        have := R7.2.2.2.2.2.2.2.2.2.1 x (by simpa using hx); rwa [e29] at this
      have slO : ShOpt (bset H6 31 (cw (some la)).toUInt64) L (some la) := ShapeCode.frame sl sh7
      have hs8 : bget (v6 (bset H6 31 (cw (some la)).toUInt64) (bget H6 29) st.nx.toUInt64 L) 0 ≠ 0 :=
        fun z => hs (v6_stat _ _ _ _ z)
      have R8 := rep_v6 R7 (bget H6 29) st.nx.toUInt64 L x st.nx (some la) hxN rfl slO hs8
      have srO : ShOpt (v6 (bset H6 31 (cw (some la)).toUInt64) (bget H6 29) st.nx.toUInt64 L) Rr (some rb) :=
        ShapeCode.frame (ShapeCode.frame sr sh7) (v6_shtab _ _ _ _)
      have ez : st.nx.toUInt64 + (cw (some la)).toUInt64 = (st.nx + la.width).toUInt64 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [cw]
      rw [ez] at hs ⊢
      have R9 := rep_v6 R8 a (st.nx + la.width).toUInt64 Rr y (st.nx + la.width) (some rb) (nameAt_ts R1.1 R8.1 R1.2.1 ea1) rfl
        srO hs
      refine ⟨[.expr 0 (bm tl), .letEnd st.nx st.binds.length], _, ?_, R9⟩
      rw [hts] at hcapN
      simp [stepF, et, evs, hx, hts, hcapN]
    · simp only [w4, if_false] at hs; exact absurd (stat0' _) hs
  · have n : (bget h1 (d11 + bget h1 3) == 13) = false := by simpa using c13
    simp only [n, if_false] at hs; exact absurd (stat0' _) hs

end ParInv
