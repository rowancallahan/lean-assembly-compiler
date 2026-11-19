/- Machine bridge (E), part (B) continued: value-mode cases (CONST, LOCAL, BIN, IF, LET) of the matching theorem,
each as a lemma taking the induction hypotheses. -/
import Nano.V2Self.Proof.Machine.NdCG
namespace Templates
open CallProbe C GenRef ParSpec
section cg
variable {S : SC} {K : GenRef.Cx}

def CGV (S : SC) (K : GenRef.Cx) (e : Nd) : Prop := ∀ (d i h : Nat) (c : List UInt64) (i' : Nat) (E : List Nat),
    NB S.p e → SerAt K.X i e.ser → CG K d i h c i' E → 1 ≤ d → h + c.length < 2 ^ 24 →
    i' = i + e.ser.length ∧ Mt c (tm S e h) h E (h + c.length) ∧ (2 ≤ d → E = []) ∧ OpV e
def CGL (S : SC) (K : GenRef.Cx) (cs : List Nd) : Prop := ∀ (d i h n : Nat) (c : List UInt64) (i' : Nat) (E : List Nat),
    NBL S.p cs → n = cs.length → SerAt K.X i (serL cs) → CGs K d i h n c i' E → 1 ≤ d → h + c.length < 2 ^ 24 →
    i' = i + (serL cs).length ∧ Mt c (tmL S cs h) h E (h + c.length) ∧ (2 ≤ d → E = []) ∧ OpL cs
def CGT (S : SC) (K : GenRef.Cx) (e : Nd) : Prop := ∀ (hd d i h : Nat) (c : List UInt64) (i' : Nat) (E : List Nat) (X : Nat),
    NB S.p e → SerAt K.X i e.ser → CT K hd d i h c i' E → 1 ≤ d → h + c.length < 2 ^ 24 → hd < 2 ^ 24 →
    i' = i + e.ser.length ∧ Mt c (tmT S e h X hd) h E X ∧ OpV e

theorem u_lt_of (n : Nat) (hn : n < 2 ^ 32) (b : UInt64) (h : n.toUInt64 < b) : n < b.toNat := by
  rw [UInt64.lt_iff_toNat_lt, toU_lt n hn] at h; exact h

theorem cgV_const (hS : SK S K) (v : UInt64)  :
    CGV S K (.const v) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, -⟩ := sa1.cons
  obtain ⟨rfl, rfl, rfl⟩ := inv_const hc t0
  rw [t1, em_of (B := 2 ^ 32 - 21) (t := fun q => constT 1 q v) (fun o ho => const_exact o v (by omega)) (by omega)]
  simp only [Nd.ser, tm]
  exact ⟨by simp, Mt.plain _ _ _, by simp, by simp [OpV]⟩

theorem cgV_loc (hS : SK S K) (s : Nat) (w : Nat)  :
    CGV S K (.loc s w) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  obtain ⟨t2, -⟩ := sa2.cons
  obtain ⟨so, rfl, rfl, rfl⟩ := inv_local hc t0
  simp only [NB] at nb
  rw [t1, t2] at so ⊢
  obtain ⟨w0, s251, w251, nsw⟩ := so
  have hs := u_lt_of s nb.1 251 s251
  have hw := u_lt_of w nb.2 251 w251
  have hsw : s + w < 251 := by
    have := hS.ns251
    rw [UInt64.lt_iff_toNat_lt] at nsw this
    simp only [UInt64.toNat_add, toU_lt s nb.1, toU_lt w nb.2] at nsw
    have : K.ns.toNat < 251 := this; omega
  have ep : K.p = (K.p.toNat).toUInt64 := by simp [Nat.toUInt64]
  rw [ep, em_of (B := 2 ^ 32 - 5 * w - 4) (t := fun q => localT 1 K.p.toNat s q w)
    (fun o ho => local_exact _ s w o (by have := hS.p251; rw [UInt64.lt_iff_toNat_lt] at this; exact this) hw hsw
      (by omega)) (by omega)]
  simp only [Nd.ser, tm, hS.p]
  exact ⟨by simp, Mt.plain _ _ _, by simp, by simp [OpV]⟩

theorem cgV_bin (hS : SK S K) (op : Nat) (a : Nd) (b : Nd) (IA : CGV S K a) (IB : CGV S K b) :
    CGV S K (.bin op a b) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  obtain ⟨saA, saB⟩ := sa2.app
  obtain ⟨ca, cb, i1, Ea, Eb, hop, hA, hB, rfl, rfl⟩ := inv_bin hc t0
  simp only [NB] at nb
  obtain ⟨nop, na, nb'⟩ := nb
  simp only [List.length_append] at hh
  obtain ⟨ei1, mA, eA, oA⟩ := IA (d + 2) (i + 2) h ca i1 Ea na saA hA (by omega) (by omega)
  subst ei1
  obtain ⟨ei', mB, eB, oB⟩ := IB (d + 1) _ (h + ca.length) cb i' Eb nb' saB hB (by omega) (by omega)
  have ea := eA (by omega); have eb := eB (by omega); subst ea eb
  rw [t1] at hop ⊢
  have h1 : 1 ≤ op ∧ op ≤ 8 := by
    have q := hop; rw [UInt64.lt_iff_toNat_lt] at q
    by_cases z : op = 0
    · subst z; exact absurd q (by decide)
    · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toU_lt op nop]; simp; omega), toU_lt op nop] at q
      simp at q; omega
  rw [em_of (B := 2 ^ 32) (t := fun _ => binT op) (fun o _ => g31_exact o op h1.1 h1.2) (by omega)]
  have lA : ca.length = lnV S a := by rw [mA.len, tm_len]
  have lB : cb.length = lnV S b := by rw [mB.len, tm_len]
  refine ⟨by simp only [ei', Nd.ser, List.length_cons, List.length_append]; omega, ?_, fun _ => rfl, ⟨h1.1, h1.2, oA, oB⟩⟩
  simp only [tm, List.nil_append]
  have q := Mt.app (Mt.app (mA.retarget (h + (ca ++ cb ++ (binT op).map encG).length))
    (by rw [tm_len, ← lA]; exact mB.retarget _)) (Mt.plain (binT op) _ _)
  simpa [tm_len, lA, lB, Nat.add_assoc] using q

theorem cgV_ite (hS : SK S K) (cm : Nat) (a : Nd) (b : Nd) (t : Nd) (e : Nd) (IA : CGV S K a) (IB : CGV S K b) (IT : CGV S K t) (IE : CGV S K e) :
    CGV S K (.ite cm a b t e) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  obtain ⟨sa3, saE⟩ := sa2.app
  obtain ⟨sa4, saT⟩ := sa3.app
  obtain ⟨saA, saB⟩ := sa4.app
  obtain ⟨ca, cb, ct, ce, i1, i2, i3, Ea, Eb, Et, Ee, hcm, hA, hB, hT, hE, rfl, rfl⟩ := inv_ite hc t0
  simp only [NB] at nb
  obtain ⟨ncm, na, nb', nt, ne⟩ := nb
  have l4 : (ifHd (tg K.X (i + 1))).length = 4 := by simp [ifHd]
  simp only [List.length_append, List.length_cons, List.length_nil, l4] at hh
  obtain ⟨e1, mA, eA, oA⟩ := IA (d + 6) (i + 2) h ca i1 Ea na saA hA (by omega) (by omega)
  subst e1
  obtain ⟨e2, mB, eB, oB⟩ := IB (d + 5) _ (h + ca.length) cb i2 Eb nb' (by simpa [Nat.add_assoc] using saB) hB
    (by omega) (by omega)
  subst e2
  obtain ⟨e3, mT, eT, oT⟩ := IT (d + 3) _ _ ct i3 Et nt (by simpa [Nat.add_assoc] using saT) hT (by omega) (by omega)
  subst e3
  obtain ⟨e4, mE, eE, oE⟩ := IE (d + 1) _ _ ce i' Ee ne (by simpa [Nat.add_assoc] using saE) hE (by omega) (by omega)
  have q1 := eA (by omega); have q2 := eB (by omega); have q3 := eT (by omega); have q4 := eE (by omega)
  subst q1 q2 q3 q4
  have lA : ca.length = lnV S a := by rw [mA.len, tm_len]
  have lB : cb.length = lnV S b := by rw [mB.len, tm_len]
  have lT : ct.length = lnV S t := by rw [mT.len, tm_len]
  have lE : ce.length = lnV S e := by rw [mE.len, tm_len]
  rw [show h + ca.length + cb.length + 5 + ct.length + 1 = h + ca.length + cb.length + 6 + ct.length by omega] at mE
  refine ⟨by simp only [e4, Nd.ser, List.length_cons, List.length_append]; omega, ?_, fun _ => by simp, ⟨oA, oB, oT, oE⟩⟩
  rw [t1, ifHd_enc cm ncm]
  simp only [tm, ifHeadG, List.nil_append]
  have m1 := Mt.app (mA.retarget 0) ((mB.retarget 0).at (by rw [tm_len, lA]) rfl)
  have m2 := Mt.app m1 (Mt.plain (ifHead4 (cmpJ cm)) _ 0)
  have m3 := Mt.app m2 (Mt.jal1 (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1)
    ((lnV S t : Int) + 2) (by omega) (by omega) (by omega) _ 0)
  have m4 := Mt.app m3 ((mT.retarget 0).at (by simp [tm_len, ifHead4, lA, lB]; omega) rfl)
  have m5 := Mt.app m4 (Mt.jal1 (h + ca.length + cb.length + 5 + ct.length)
    (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length)
    ((lnV S e : Int) + 1) (by omega) (by omega) (by omega) _ 0)
  have m6 := Mt.app m5 ((mE.retarget 0).at (by simp [tm_len, ifHead4, lA, lB, lT]; omega) rfl)
  simp only [List.append_nil] at m6
  have m7 := m6.retarget (h + (ca ++ cb ++ (ifHead4 (cmpJ cm)).map encG ++
      [jw 0 (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++
      ce).length)
  simp only [lA, lB, lT, lE] at m7 ⊢
  simpa [ifHead4, List.append_assoc] using m7

theorem cgV_letE (hS : SK S K) (s : Nat) (w : Nat) (v : Nd) (b : Nd) (IV : CGV S K v) (IB : CGV S K b) :
    CGV S K (.letE s w v b) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  obtain ⟨t2, sa3⟩ := sa2.cons
  obtain ⟨saV, saB⟩ := sa3.app
  obtain ⟨cv, cb, i1, Ev, Eb, so, hV, hB, rfl, rfl⟩ := inv_lett hc t0
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
  obtain ⟨e2, mB, eB, oB⟩ := IB d _ _ cb i' Eb nb' (by simpa [Nat.add_assoc] using saB) hB hd (by omega)
  have q1 := eV (by omega); subst q1
  have lV : cv.length = lnV S v := by rw [mV.len, tm_len]
  refine ⟨by simp only [e2, Nd.ser, List.length_cons, List.length_append]; omega, ?_, fun h2 => by simp [eB h2], ⟨oV, oB⟩⟩
  simp only [tm, List.nil_append, hS.p]
  have m1 := Mt.app (mV.retarget (h + (cv ++ (popN K.p.toNat s w).map encG ++ cb).length))
    (Mt.plain (popN K.p.toNat s w) _ (h + (cv ++ (popN K.p.toNat s w).map encG ++ cb).length))
  have m2 := Mt.app m1 (mB.at (by simp [tm_len, popN_len, lV]; omega) (by simp [popN_len]; omega))
  simpa [lV, popN_len, List.append_assoc] using m2

end cg
end Templates
