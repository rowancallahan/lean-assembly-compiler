/- Machine bridge (E), part (B) continued: tail-mode cases (CT). -/
import Nano.Run.NdCGv
namespace Templates
open CallProbe C GenRef ParSpec
section cg
variable {S : SC} {K : GenRef.Cx}

set_option maxHeartbeats 1000000

theorem cgT_ite (hS : SK S K) (cm : Nat) (a : Nd) (b : Nd) (t : Nd) (e : Nd) (IA : CGV S K a) (IB : CGV S K b) (IT : CGT S K t) (IE : CGT S K e) :
    CGT S K (.ite cm a b t e) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  obtain ⟨sa3, saE⟩ := sa2.app
  obtain ⟨sa4, saT⟩ := sa3.app
  obtain ⟨saA, saB⟩ := sa4.app
  obtain ⟨ca, cb, ct, ce, i1, i2, i3, Ea, Eb, Et, Ee, hcm, hA, hB, hT, hE, rfl, rfl⟩ := invT_ite hc t0
  simp only [NB] at nb
  obtain ⟨ncm, na, nb', nt, ne⟩ := nb
  have l4 : (ifHd (tg K.X (i + 1))).length = 4 := by simp [ifHd]
  simp only [List.length_append, List.length_cons, List.length_nil, l4] at hh
  obtain ⟨e1, mA, eA, oA⟩ := IA (d + 6) (i + 2) h ca i1 Ea na saA hA (by omega) (by omega)
  subst e1
  obtain ⟨e2, mB, eB, oB⟩ := IB (d + 5) _ (h + ca.length) cb i2 Eb nb' (by simpa [Nat.add_assoc] using saB) hB
    (by omega) (by omega)
  subst e2
  obtain ⟨e3, mT, oT⟩ := IT hd (d + 3) _ _ ct i3 Et X nt (by simpa [Nat.add_assoc] using saT) hT (by omega) (by omega) hhd
  subst e3
  obtain ⟨e4, mE, oE⟩ := IE hd (d + 1) _ _ ce i' Ee X ne (by simpa [Nat.add_assoc] using saE) hE (by omega) (by omega) hhd
  have q1 := eA (by omega); have q2 := eB (by omega)
  subst q1 q2
  have lA : ca.length = lnV S a := by rw [mA.len, tm_len]
  have lB : cb.length = lnV S b := by rw [mB.len, tm_len]
  have lT : ct.length = lnT S t := by rw [mT.len, tmT_len]
  have lE : ce.length = lnT S e := by rw [mE.len, tmT_len]
  rw [show h + ca.length + cb.length + 5 + ct.length + 1 = h + ca.length + cb.length + 6 + ct.length by omega] at mE
  refine ⟨by simp only [e4, Nd.ser, List.length_cons, List.length_append]; omega, ?_, ⟨oA, oB, oT, oE⟩⟩
  rw [t1, ifHd_enc cm ncm]
  simp only [tmT, ifHeadG, List.nil_append]
  have m1 := Mt.app (mA.retarget X) ((mB.retarget X).at (by rw [tm_len, lA]) rfl)
  have m2 := Mt.app m1 (Mt.plain (ifHead4 (cmpJ cm)) _ X)
  have m3 := Mt.app m2 (Mt.jal1 (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1)
    ((lnT S t : Int) + 2) (by omega) (by omega) (by omega) _ X)
  have m4 := Mt.app m3 (mT.at (by simp [tm_len, ifHead4, lA, lB]; omega) rfl)
  have m5 := Mt.app m4 (Mt.jal1 (h + ca.length + cb.length + 5 + ct.length)
    (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length)
    ((lnT S e : Int) + 1) (by omega) (by omega) (by omega) _ X)
  have m6 := Mt.app m5 (mE.at (by simp [tm_len, tmT_len, ifHead4, lA, lB, lT]; omega) rfl)
  simp only [lA, lB, lT, lE] at m6 ⊢
  simpa [ifHead4, List.append_assoc] using m6

theorem cgT_letE (hS : SK S K) (s : Nat) (w : Nat) (v : Nd) (b : Nd) (IV : CGV S K v) (IB : CGT S K b) :
    CGT S K (.letE s w v b) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  obtain ⟨t2, sa3⟩ := sa2.cons
  obtain ⟨saV, saB⟩ := sa3.app
  obtain ⟨cv, cb, i1, Ev, Eb, so, hV, hB, rfl, rfl⟩ := invT_lett hc t0
  simp only [NB] at nb
  obtain ⟨ns, nw, nv, nb'⟩ := nb
  rw [t1, t2] at so hB hh ⊢
  obtain ⟨w0, s251, w251, nsw⟩ := so
  have hs := u_lt_of s ns 251 s251
  have hw := u_lt_of w nw 251 w251
  have hsw : s + w < 251 := by
    have := hS.ns251
    rw [UInt64.lt_iff_toNat_lt] at nsw this
    simp only [UInt64.toNat_add, toU_lt s ns, toU_lt w nw] at nsw
    have : K.ns.toNat < 251 := this; omega
  have ep : K.p = (K.p.toNat).toUInt64 := by simp [Nat.toUInt64]
  have p251 : K.p.toNat < 251 := by have := hS.p251; rw [UInt64.lt_iff_toNat_lt] at this; exact this
  have eg : em (g26 256 K.p s.toUInt64 w.toUInt64) (h + cv.length) = (popN K.p.toNat s w).map encG := by
    have q := em_of (F := g26 256 K.p.toNat.toUInt64 s.toUInt64 w.toUInt64) (B := h + cv.length + 1)
      (t := fun _ => popN K.p.toNat s w) (h := h + cv.length)
      (fun o _ => g26_exact _ p251 256 w s o (by omega) hsw) (by omega)
    rwa [← ep] at q
  rw [eg] at hB hh ⊢
  simp only [List.length_append, List.length_map, popN_len] at hh hB
  obtain ⟨e1, mV, eV, oV⟩ := IV (d + 2) (i + 3) h cv i1 Ev nv (by simpa [Nat.add_assoc] using saV) hV (by omega)
    (by omega)
  subst e1
  obtain ⟨e2, mB, oB⟩ := IB hd d _ _ cb i' Eb X nb' (by simpa [Nat.add_assoc] using saB) hB h1 (by omega) hhd
  have q1 := eV (by omega); subst q1
  have lV : cv.length = lnV S v := by rw [mV.len, tm_len]
  refine ⟨by simp only [e2, Nd.ser, List.length_cons, List.length_append]; omega, ?_, ⟨oV, oB⟩⟩
  simp only [tmT, List.nil_append, hS.p]
  have m1 := Mt.app (mV.retarget X) (Mt.plain (popN K.p.toNat s w) _ X)
  have m2 := Mt.app m1 (mB.at (by simp [tm_len, popN_len, lV]; omega) rfl)
  simpa [lV, popN_len, List.append_assoc] using m2

theorem cgT_cont (hS : SK S K) (e : Nd) (IE : CGV S K e) :
    CGT S K (.cont e) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  simp only [Nd.ser] at sa
  obtain ⟨t0, saE⟩ := sa.cons
  simp only [NB] at nb
  obtain ⟨p1, ne⟩ := nb
  obtain ⟨cv, hV, rfl, rfl⟩ := invT_cont hc t0
  have ep : K.p = (K.p.toNat).toUInt64 := by simp [Nat.toUInt64]
  have p251 : K.p.toNat < 251 := by have := hS.p251; rw [UInt64.lt_iff_toNat_lt] at this; exact this
  rw [hS.p] at p1
  have epm : K.p - 1 = (K.p.toNat - 1).toUInt64 := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
    simp [Nat.toUInt64]; omega
  have eg : em (g26 256 K.p 1 (K.p - 1)) (h + cv.length) = (popN K.p.toNat 1 (K.p.toNat - 1)).map encG := by
    have q := em_of (F := g26 256 K.p.toNat.toUInt64 (1 : Nat).toUInt64 (K.p.toNat - 1).toUInt64)
      (B := h + cv.length + 1) (t := fun _ => popN K.p.toNat 1 (K.p.toNat - 1)) (h := h + cv.length)
      (fun o _ => g26_exact _ p251 256 (K.p.toNat - 1) 1 o (by omega) (by omega)) (by omega)
    rw [← ep, ← epm] at q; exact q
  rw [eg] at hh ⊢
  simp only [List.length_append, List.length_map, popN_len, List.length_cons, List.length_nil] at hh
  obtain ⟨e1, mV, eV, oV⟩ := IE (d + 1) (i + 1) h cv i' [] ne saE hV (by omega) (by omega)
  have lV : cv.length = lnV S e := by rw [mV.len, tm_len]
  refine ⟨by simp only [e1, Nd.ser, List.length_cons]; omega, ?_, oV⟩
  rw [jw_enc _ _ (by simp [popN_len]; omega) (by omega)]
  simp only [tmT, hS.p]
  have m1 := Mt.app (mV.retarget X) (Mt.plain (popN K.p.toNat 1 (K.p.toNat - 1)) _ X)
  have m2 := Mt.app m1 (Mt.plain [J.jal 0 ((hd : Int) - ((h + lnV S e + 3 * (K.p.toNat - 1) : Nat) : Int))] _ X)
  simp only [List.append_nil] at m2
  simpa [lV, popN_len, List.append_assoc] using m2

theorem cgT_val (hS : SK S K) (e : Nd) (IE : CGV S K e) {t : UInt64} (ht : (e.ser).head? = some t) (t4 : t ≠ 4)
    (t5 : t ≠ 5) (t11 : t ≠ 11) : ∀ (hd d i h : Nat) (c : List UInt64) (i' : Nat) (E : List Nat) (X : Nat),
    NB S.p e → SerAt K.X i e.ser → CT K hd d i h c i' E → 1 ≤ d → h + c.length < 2 ^ 24 →
    i' = i + e.ser.length ∧ Mt c (tm S e h ++ [.jal 0 ((X : Int) - ((h + lnV S e : Nat) : Int))]) h E X ∧ OpV e := by
  intro hd d i h c i' E X nb sa hc h1 hh
  have t0 : tg K.X i = t := by
    cases hq : e.ser with
    | nil => rw [hq] at ht; simp at ht
    | cons a l =>
      rw [hq] at ht sa; simp at ht; subst ht
      exact (SerAt.cons sa).1
  obtain ⟨cv, Ev, hV, rfl, rfl⟩ := invT_val hc (by rw [t0]; exact t4) (by rw [t0]; exact t5) (by rw [t0]; exact t11)
  simp only [List.length_append, List.length_cons, List.length_nil] at hh
  obtain ⟨e1, mV, eV, oV⟩ := IE (d + 1) i h cv i' Ev nb sa hV (by omega) (by omega)
  have q := eV (by omega); subst q
  have lV : cv.length = lnV S e := by rw [mV.len, tm_len]
  refine ⟨e1, ?_, oV⟩
  have m0 : Mt [0] [.jal 0 ((X : Int) - ((h + lnV S e : Nat) : Int))] (h + cv.length) [h + cv.length] X := by
    refine ⟨rfl, by simp [lV], fun j hj => ?_⟩
    have : j = 0 := by simpa using hj
    subst this; simp [lV]
  have m := Mt.app (mV.retarget X) (m0.at (by rw [tm_len, lV]) rfl)
  simpa using m

theorem cgT_const (hS : SK S K) (v : UInt64) (IE : CGV S K (.const v)) : CGT S K (.const v) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  have q := cgT_val hS (.const v) IE (t := 1) (by simp [Nd.ser]) (by decide) (by decide) (by decide) hd d i h c i' E X nb sa hc h1 hh
  simpa only [tmT] using q

theorem cgT_loc (hS : SK S K) (s : Nat) (w : Nat) (IE : CGV S K (.loc s w)) : CGT S K (.loc s w) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  have q := cgT_val hS (.loc s w) IE (t := 2) (by simp [Nd.ser]) (by decide) (by decide) (by decide) hd d i h c i' E X nb sa hc h1 hh
  simpa only [tmT] using q

theorem cgT_bin (hS : SK S K) (op : Nat) (a : Nd) (b : Nd) (IE : CGV S K (.bin op a b)) : CGT S K (.bin op a b) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  have q := cgT_val hS (.bin op a b) IE (t := 3) (by simp [Nd.ser]) (by decide) (by decide) (by decide) hd d i h c i' E X nb sa hc h1 hh
  simpa only [tmT] using q

theorem cgT_pair (hS : SK S K) (cs : List Nd) (IE : CGV S K (.pair cs)) : CGT S K (.pair cs) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  have q := cgT_val hS (.pair cs) IE (t := 6) (by simp [Nd.ser]) (by decide) (by decide) (by decide) hd d i h c i' E X nb sa hc h1 hh
  simpa only [tmT] using q

theorem cgT_call (hS : SK S K) (n : Nat) (as : List Nd) (IE : CGV S K (.call n as)) : CGT S K (.call n as) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  have q := cgT_val hS (.call n as) IE (t := 8) (by simp [Nd.ser]) (by decide) (by decide) (by decide) hd d i h c i' E X nb sa hc h1 hh
  simpa only [tmT] using q

theorem cgT_prim (hS : SK S K) (pn : Nat) (as : List Nd) (IE : CGV S K (.prim pn as)) : CGT S K (.prim pn as) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  have q := cgT_val hS (.prim pn as) IE (t := 9) (by simp [Nd.ser]) (by decide) (by decide) (by decide) hd d i h c i' E X nb sa hc h1 hh
  simpa only [tmT] using q

theorem cgT_loop (hS : SK S K) (z : Nd) (s : Nd) (IE : CGV S K (.loop z s)) : CGT S K (.loop z s) := by
  intro hd d i h c i' E X nb sa hc h1 hh hhd
  have q := cgT_val hS (.loop z s) IE (t := 10) (by simp [Nd.ser]) (by decide) (by decide) (by decide) hd d i h c i' E X nb sa hc h1 hh
  simpa only [tmT] using q

end cg
end Templates
