/- Machine bridge (E), part (B) continued: value-mode cases PAIR, CALL, PRIM, LOOP, CONTINUE and operand lists. -/
import Nano.V2Self.Proof.NdCGv
namespace Templates
open CallProbe C GenRef ParSpec
section cg
variable {S : SC} {K : GenRef.Cx}

set_option maxHeartbeats 1000000

theorem cgV_pair (hS : SK S K) (cs : List Nd) (ICS : CGL S K cs) :
    CGV S K (.pair cs) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  simp only [NB] at nb
  obtain ⟨_, hl⟩ := inv_pair hc t0
  rw [t1, toU_lt _ nb.1] at hl
  obtain ⟨e1, m, eE⟩ := ICS d (i + 2) h cs.length c i' E nb.2 rfl sa2 hl hd hh
  simp only [tm]
  exact ⟨by simp only [e1, Nd.ser, List.length_cons]; omega, m, eE⟩

theorem cgV_call (hS : SK S K) (n : Nat) (as : List Nd) (IAS : CGL S K as) :
    CGV S K (.call n as) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  obtain ⟨t2, sa3⟩ := sa2.cons
  simp only [NB] at nb
  obtain ⟨nn, nl, na⟩ := nb
  obtain ⟨ca, _, _, hl, rfl⟩ := inv_call hc t0
  rw [t2, toU_lt _ nl] at hl
  simp only [List.length_append, List.length_cons, List.length_nil] at hh
  obtain ⟨e1, m, eE⟩ := IAS (d + 1) (i + 3) h as.length ca i' E na rfl sa3 hl (by omega) (by omega)
  have e0 := eE (by omega); subst e0
  have lA : ca.length = lnL S as := by rw [m.len, tmL_len]
  have eT : bget K.T (tg K.X (i + 1)) = (S.T n).toUInt64 := by
    rw [t1, hS.T n]; simp [Nat.toUInt64]
  rw [eT, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl,
    g13_enc 1 (h + ca.length) (S.T n) (by omega) (by rw [hS.T]; exact hS.Tb n)]
  refine ⟨by simp only [e1, Nd.ser, List.length_cons]; omega, ?_, fun _ => rfl⟩
  simp only [tm]
  have m2 := Mt.app (m.retarget (h + (ca ++ [encG (J.jal 1 ((S.T n : Int) - ((h + ca.length : Nat) : Int)))]).length))
    (Mt.plain [J.jal 1 ((S.T n : Int) - ((h + ca.length : Nat) : Int))] (h + (tmL S as h).length)
      (h + (ca ++ [encG (J.jal 1 ((S.T n : Int) - ((h + ca.length : Nat) : Int)))]).length))
  simpa [lA, tmL_len] using m2

theorem cgV_prim (hS : SK S K) (pn : Nat) (as : List Nd) (IAS : CGL S K as) :
    CGV S K (.prim pn as) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨t1, sa2⟩ := sa1.cons
  simp only [NB] at nb
  obtain ⟨npn, nl, na⟩ := nb
  obtain ⟨ca, hr, hl, rfl⟩ := inv_prim hc t0
  rw [t1, ← nl] at hl
  rw [t1] at hr ⊢
  have r19 : 1 ≤ pn ∧ pn ≤ 9 := by
    have q := hr; rw [UInt64.lt_iff_toNat_lt] at q
    by_cases z : pn = 0
    · subst z; exact absurd q (by decide)
    · rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toU_lt pn npn]; simp; omega),
        toU_lt pn npn] at q
      simp at q; omega
  have eu : K.u = UInt64.ofNat S.κ := by rw [hS.κ]; simp
  rw [eu, em_of (B := 2 ^ 32 - 50) (t := fun q => primT S pn q) (fun o ho => g32_prim S pn r19.1 r19.2 o (by omega))
    (by simp at hh; omega)]
  simp only [List.length_append, List.length_map] at hh
  obtain ⟨e1, m, eE⟩ := IAS (d + 1) (i + 2) h as.length ca i' E na rfl sa2 hl (by omega) (by omega)
  have e0 := eE (by omega); subst e0
  have lA : ca.length = lnL S as := by rw [m.len, tmL_len]
  refine ⟨by simp only [e1, Nd.ser, List.length_cons]; omega, ?_, fun _ => rfl⟩
  simp only [tm]
  have m2 := Mt.app (m.retarget 0) (Mt.plain (primT S pn (h + lnL S as)) (h + (tmL S as h).length) 0)
  have m3 := m2.retarget (h + (ca ++ (primT S pn (h + ca.length)).map encG).length)
  simpa [lA, tmL_len] using m3

theorem cgV_loop (hS : SK S K) (z : Nd) (s' : Nd) (IZ : CGT S K z) (IS2 : CGT S K s') :
    CGV S K (.loop z s') := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  obtain ⟨t0, sa1⟩ := sa.cons
  obtain ⟨saZ, saS⟩ := sa1.app
  simp only [NB] at nb
  obtain ⟨cz, cs, i1, Ez, Es, rfl, hZ, hS', rfl, rfl⟩ := inv_loop hc t0
  have ep : K.p = (K.p.toNat).toUInt64 := by simp [Nat.toUInt64]
  have p251 : K.p.toNat < 251 := by have := hS.p251; rw [UInt64.lt_iff_toNat_lt] at this; exact this
  have lh : (lpHd K.p).length = 2 := by simp [lpHd]
  have ld : (lpDec K.p).length = 2 := by simp [lpDec]
  simp only [List.length_append, List.length_cons, List.length_nil, lh, ld] at hh
  obtain ⟨e1, mZ⟩ := IZ h 3 (i + 1) (h + 3) cz i1 Ez (h + (3 + lnT S z + 2 + lnT S s')) nb.1 saZ hZ
    (by omega) (by omega) (by omega)
  subst e1
  obtain ⟨e2, mS⟩ := IS2 h 1 _ _ cs i' Es (h + (3 + lnT S z + 2 + lnT S s')) nb.2
    (by simpa [Nat.add_assoc] using saS) hS' (by omega) (by omega) (by omega)
  have lZ : cz.length = lnT S z := by rw [mZ.len, tmT_len]
  have lS : cs.length = lnT S s' := by rw [mS.len, tmT_len]
  obtain ⟨eh, ed⟩ := lp_enc K.p.toNat p251
  rw [← ep] at eh ed
  refine ⟨by simp only [e2, Nd.ser, List.length_cons, List.length_append]; omega, ?_, fun h2 => by omega⟩
  rw [eh, ed, jw_enc _ _ (by omega) (by omega)]
  simp only [tm, loopHead, loopDec, hS.p]
  have m1 := Mt.app (Mt.plain [J.ld 5 8 (slotOff K.p.toNat 0), J.beq 5 0 2,
    J.jal 0 (((h + 3 + cz.length : Nat) : Int) - ((h + 2 : Nat) : Int))] h (h + (3 + lnT S z + 2 + lnT S s')))
    (mZ.at (by simp) rfl)
  have m2 := Mt.app m1 (Mt.plain [J.addi 5 5 (-1), J.sd 5 8 (slotOff K.p.toNat 0)] _
    (h + (3 + lnT S z + 2 + lnT S s')))
  have m3 := Mt.app m2 (mS.at (by simp [tmT_len, lZ]; omega) rfl)
  refine Mt.at (h := h) (X := h + (3 + lnT S z + 2 + lnT S s')) ?_ rfl (by simp [lZ, lS]; omega)
  simpa [lZ, lS, List.append_assoc] using m3

theorem cgV_cont (hS : SK S K) (e : Nd)  :
    CGV S K (.cont e) := by
  intro d i h c i' E nb sa hc hd hh
  simp only [Nd.ser] at sa
  exact (inv_cont11 hc (sa.cons.1)).elim

theorem cgL_nil : CGL S K [] := by
  intro d i h n c i' E _ hn _ hc _ _
  subst hn
  obtain ⟨rfl, rfl, rfl⟩ := invS_nil hc
  exact ⟨by simp [serL], by simpa [tmL] using Mt.plain [] h h, fun _ => rfl⟩

theorem cgL_cons (hS : SK S K) (x : Nd) (xs : List Nd) (IX : CGV S K x) (IL : CGL S K xs) :
    CGL S K (x :: xs) := by
  intro d i h n c i' E nb hn sa hc hd hh
  subst hn
  simp only [serL] at sa
  obtain ⟨sa1, sa2⟩ := sa.app
  simp only [NBL] at nb
  obtain ⟨c1, cs, i1, E1, Es, h1, h2, rfl, rfl⟩ := invS_cons hc
  simp only [List.length_append] at hh
  obtain ⟨e1, m1, eE1⟩ := IX (d + xs.length) i h c1 i1 E1 nb.1 sa1 h1 (by omega) (by omega)
  subst e1
  obtain ⟨e2, m2, eE2⟩ := IL d _ (h + c1.length) xs.length cs i' Es nb.2 rfl sa2 h2 hd (by omega)
  have l1 : c1.length = lnV S x := by rw [m1.len, tm_len]
  refine ⟨by simp only [e2, serL, List.length_append]; omega, ?_, fun q => by
    simp [eE1 (by omega), eE2 q]⟩
  simp only [tmL]
  rcases xs with _ | ⟨y, ys⟩
  · obtain ⟨rfl, rfl, rfl⟩ := invS_nil h2
    simpa [tmL] using m1
  · have q := eE1 (by simp; omega); subst q
    have m := Mt.app (m1.retarget (h + (c1 ++ cs).length)) (m2.at (by rw [tm_len, l1]) (by simp; omega))
    simpa [l1] using m

end cg
end Templates
