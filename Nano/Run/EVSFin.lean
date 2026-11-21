/- Safe retrofit (EVS) P1b: the closing fragments (Opus box E).  `Fin1S/2S/3S` = HeapEV's Fin1/2/3 with SafeX runs;
premise `StkOK` (the operand cells are in the work region, t6 aligned) and `HAl` (heap cells aligned). -/
import Nano.Run.EVSComp
namespace Templates
open CallProbe SimW SafeRun

/-- the stack window [t6, t6 + 8n) lies in the work region, t6 aligned -/
structure StkOK (KL : LayW) (hb E0 n : Nat) (s : St) : Prop where
  lo : KL.lo ≤ hb
  hi : E0 ≤ KL.hi
  top : (s.x 31).toNat + 8 * n ≤ E0
  a31 : (s.x 31).toNat % 8 = 0

def Fin1S (KL : LayW) (C : List J) (q lu : Nat) (Inv : St → Prop) (hb E0 : Nat)
    (F : UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s1 : St) (H1 : Hp) (v : UInt64) (H2 : Hp), Inv s1 → s1.x 0 = 0 → HRel hb s1 H1 → StkOK KL hb E0 1 s1 →
    HAl H1 → F (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = some (v, H2) →
    ∃ s3 : St, SStarX KL C (q, s1) (q + lu, s3) ∧ s3.x 31 = s1.x 31 ∧ s3.m (s1.x 31).toNat = v ∧
      HRel hb s3 H2 ∧ HAl H2 ∧ (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → s3.x r = s1.x r) ∧
      ∀ a, a ≠ (s1.x 31).toNat → ¬ (hb ≤ a ∧ a < H2.top) → s3.m a = s1.m a

def Fin2S (KL : LayW) (C : List J) (q lu : Nat) (Inv : St → Prop) (hb E0 : Nat)
    (F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s2 : St) (H2 : Hp) (v : UInt64) (H3 : Hp), Inv s2 → s2.x 0 = 0 → HRel hb s2 H2 → (s2.x 31).toNat + 16 < 2 ^ 63 →
    StkOK KL hb E0 2 s2 → HAl H2 →
    F (s2.m ((s2.x 31).toNat + 8)) (s2.m (s2.x 31).toNat) (s2.x 31).toNat H2 = some (v, H3) →
    ∃ s3 : St, SStarX KL C (q, s2) (q + lu, s3) ∧ (s3.x 31).toNat = (s2.x 31).toNat + 8 ∧
      s3.m ((s2.x 31).toNat + 8) = v ∧ HRel hb s3 H3 ∧ HAl H3 ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s3.x r = s2.x r) ∧
      ∀ a, a ≠ (s2.x 31).toNat + 8 → ¬ (hb ≤ a ∧ a < H3.top) → s3.m a = s2.m a

def Fin3S (KL : LayW) (C : List J) (q lu : Nat) (Inv : St → Prop) (hb E0 : Nat)
    (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s3 : St) (H3 : Hp) (v : UInt64) (H4 : Hp), Inv s3 → s3.x 0 = 0 → HRel hb s3 H3 → (s3.x 31).toNat + 24 < 2 ^ 62 →
    StkOK KL hb E0 3 s3 → HAl H3 →
    F (s3.m ((s3.x 31).toNat + 16)) (s3.m ((s3.x 31).toNat + 8)) (s3.m (s3.x 31).toNat) (s3.x 31).toNat H3 =
      some (v, H4) →
    ∃ s4 : St, SStarX KL C (q, s3) (q + lu, s4) ∧ (s4.x 31).toNat = (s3.x 31).toNat + 16 ∧
      s4.m ((s3.x 31).toNat + 16) = v ∧ HRel hb s4 H4 ∧ HAl H4 ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s4.x r = s3.x r) ∧
      ∀ a, a ≠ (s3.x 31).toNat + 16 → ¬ (hb ≤ a ∧ a < H4.top) → s4.m a = s3.m a

theorem StkOK.wok {KL : LayW} {hb E0 n : Nat} {s : St} (h : StkOK KL hb E0 n s) (h31 : hb ≤ (s.x 31).toNat)
    {i : Nat} (hi : i < n) : wok KL ((s.x 31).toNat + 8 * i) :=
  ⟨by have := h.lo; omega, by have := h.hi; have := h.top; omega, by have := h.a31; omega⟩

theorem finTail {KL : LayW} {C : List J} {pc q lu t p nl hb : Nat} {Inv : St → Prop} {W : Nat → Prop}
    (hI : InvOKH hb p Inv) (s s1 s3 : St) (env env1 : Env) (H3 : Hp) (v : UInt64)
    (I1 : Inv s1) (z1 : s1.x 0 = 0) (O0 : FrameOK p nl s) (e81 : s1.x 8 = s.x 8) (F1 : Frame p nl s1 env1)
    (ag1 : ∀ k, ¬ W k → env1 k = env k)
    (m1 : ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s1.m a = s.m a)
    (r1 : SStarX KL C (pc, s) (q, s1)) (st3 : SStarX KL C (q, s1) (q + lu, s3)) (A3 : HAl H3)
    (p3 : (s3.x 31).toNat = (s.x 31).toNat - 8) (v3 : s3.m ((s.x 31).toNat - 8) = v) (R3 : HRel hb s3 H3)
    (qx : ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s3.x r = s1.x r)
    (qm : ∀ a, a ≠ (s.x 31).toNat - 8 → ¬ (hb ≤ a ∧ a < H3.top) → s3.m a = s1.m a)
    (sp16 : 16 ≤ (s.x 31).toNat) (hq : q + lu = t) :
    ∃ s' env', SStarX KL C (pc, s) (t, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧
      (s'.x 31).toNat = (s.x 31).toNat - 8 * 1 ∧ [v].length = 1 ∧
      (∀ i, i < 1 → s'.m ((s.x 31).toNat - 8 * (i + 1)) = [v].getD i 0) ∧ s'.x 8 = s.x 8 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧ HRel hb s' H3 ∧ HAl H3 ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a := by
  obtain ⟨o1, o2, o3⟩ := O0
  have top3 := R3.2.2.1
  have q8 : s3.x 8 = s.x 8 := by rw [qx 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e81]
  refine ⟨s3, env1, by rw [← hq]; exact r1.trans st3, ?_, ?_, by rw [p3], rfl, ?_, q8, ?_, ag1, R3, A3, ?_⟩
  · apply hI s1 s3 I1 (by rw [q8, e81]) (qx 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) st3.star.b st3.star.w
    intro a ha
    apply qm
    · intro e; apply ha; rw [e, e81]; constructor
      · have := R3.2.1; omega
      · omega
    · intro ⟨h1, h2⟩; apply ha; rw [e81]; exact ⟨h1, by omega⟩
  · rw [qx 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), z1]
  · intro i hi; have : i = 0 := by omega
    subst this; simpa using v3
  · intro k hk
    show s3.m (slotAddr p (s3.x 8).toNat k) = env1 k
    have hk' := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk
    rw [q8, qm _ (by omega) (by intro ⟨_, h2⟩; omega)]
    have := F1 k hk; rw [e81] at this; exact this
  · intro a ha hW
    rw [qm a (by omega) (by intro ⟨_, h2⟩; omega)]; exact m1 a ha hW

theorem fin2X {KL : LayW} {C : List J} {pc lp lu p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
    {F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hI : InvOKH hb p Inv) (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 2 SP) (hU : Fin2S KL C (pc + lp) lu Inv hb E0 F) :
    EVHwS KL C pc (lp + lu) p nl Inv hb E0 R W 1 (fin2S SP F) where
  stable := fun env env' sp H h => by simp only [fin2S]; rw [hP.stable env env' sp H h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [fin2S, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, A1, m1⟩ := hP.run s env H ab H1 I0 z0 F0 O0 R0 L0 A0 hSP
    match ab, l1, hS, v1 with
    | [a, b], _, hS, v1 =>
    dsimp only at hS
    simp only [Option.map_eq_some_iff] at hS
    obtain ⟨⟨v, H3⟩, hF, e⟩ := hS
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    have sp1 := hrel_sp R1
    have lt64 := (s.x 31).toNat_lt
    have va : s1.m ((s1.x 31).toNat + 8) = a := by
      rw [p1, show (s.x 31).toNat - 8 * 2 + 8 = (s.x 31).toNat - 8 * (0 + 1) by omega]; simpa using v1 0 (by omega)
    have vb : s1.m (s1.x 31).toNat = b := by
      rw [p1, show (s.x 31).toNat - 8 * 2 = (s.x 31).toNat - 8 * (1 + 1) by omega]; simpa using v1 1 (by omega)
    have hF' : F (s1.m ((s1.x 31).toNat + 8)) (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = some (v, H3) := by
      rw [va, vb, p1, show (s.x 31).toNat - 8 * 2 = (s.x 31).toNat - 16 by omega]; exact hF
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    obtain ⟨s3, st3, q31, qv, R3, A3, qx, qm⟩ := hU s1 H1 v H3 I1 z1 R1 (by rw [p1]; have := O0.1; have := O0.2.2; omega)
      ⟨L0.lo, L0.hi, by rw [p1]; have := L0.top; have := O0.1; have := R1.1; have := R1.2.1; have := R1.2.2.1; rw [p1] at *; omega, L1.a31⟩ A1 hF'
    rw [p1, show (s.x 31).toNat - 8 * 2 + 8 = (s.x 31).toNat - 8 by omega] at q31 qv qm
    exact finTail hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 A3 q31 qv R3 qx qm (by omega) (by omega)

theorem fin1X {KL : LayW} {C : List J} {pc lp lu p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
    {F : UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hI : InvOKH hb p Inv) (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 1 SP) (hU : Fin1S KL C (pc + lp) lu Inv hb E0 F) :
    EVHwS KL C pc (lp + lu) p nl Inv hb E0 R W 1 (fin1S SP F) where
  stable := fun env env' sp H h => by simp only [fin1S]; rw [hP.stable env env' sp H h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [fin1S, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, A1, m1⟩ := hP.run s env H ab H1 I0 z0 F0 O0 R0 L0 A0 hSP
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    have K1 : StkOK KL hb E0 1 s1 := ⟨L0.lo, L0.hi, by rw [p1]; have := L0.top; have := O0.1; have := R1.1; have := R1.2.1; have := R1.2.2.1; rw [p1] at *; omega, L1.a31⟩
    match ab, l1, hS, v1 with
    | [a], _, hS, v1 =>
    dsimp only at hS
    simp only [Option.map_eq_some_iff] at hS
    obtain ⟨⟨v, H3⟩, hF, e⟩ := hS
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    have sp1 := hrel_sp R1
    have va : s1.m (s1.x 31).toNat = a := by
      rw [p1, show (s.x 31).toNat - 8 * 1 = (s.x 31).toNat - 8 * (0 + 1) by omega]; simpa using v1 0 (by omega)
    have hF' : F (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = some (v, H3) := by
      rw [va, p1, show (s.x 31).toNat - 8 * 1 = (s.x 31).toNat - 8 by omega]; exact hF
    obtain ⟨s3, st3, q31, qv, R3, A3, qx, qm⟩ := hU s1 H1 v H3 I1 z1 R1 K1 A1 hF'
    have q31' : (s3.x 31).toNat = (s.x 31).toNat - 8 := by rw [q31, p1]
    rw [p1, show (s.x 31).toNat - 8 * 1 = (s.x 31).toNat - 8 by omega] at qv qm
    exact finTail hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 A3 q31' qv R3
      (fun r a b c d e _ => qx r a b c d e) qm (by omega) (by omega)

theorem fin3X {KL : LayW} {C : List J} {pc lp lu p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
    {F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hI : InvOKH hb p Inv) (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 3 SP) (hU : Fin3S KL C (pc + lp) lu Inv hb E0 F) :
    EVHwS KL C pc (lp + lu) p nl Inv hb E0 R W 1 (fin3S SP F) where
  stable := fun env env' sp H h => by simp only [fin3S]; rw [hP.stable env env' sp H h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [fin3S, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, A1, m1⟩ := hP.run s env H ab H1 I0 z0 F0 O0 R0 L0 A0 hSP
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    have K1 : StkOK KL hb E0 3 s1 := ⟨L0.lo, L0.hi, by rw [p1]; have := L0.top; have := O0.1; have := R1.1; have := R1.2.1; have := R1.2.2.1; rw [p1] at *; omega, L1.a31⟩
    match ab, l1, hS, v1 with
    | [a, b, c], _, hS, v1 =>
    dsimp only at hS
    simp only [Option.map_eq_some_iff] at hS
    obtain ⟨⟨v, H3⟩, hF, e⟩ := hS
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    have sp1 := hrel_sp R1
    have va : s1.m ((s1.x 31).toNat + 16) = a := by
      rw [p1, show (s.x 31).toNat - 8 * 3 + 16 = (s.x 31).toNat - 8 * (0 + 1) by omega]; simpa using v1 0 (by omega)
    have vb : s1.m ((s1.x 31).toNat + 8) = b := by
      rw [p1, show (s.x 31).toNat - 8 * 3 + 8 = (s.x 31).toNat - 8 * (1 + 1) by omega]; simpa using v1 1 (by omega)
    have vc : s1.m (s1.x 31).toNat = c := by
      rw [p1, show (s.x 31).toNat - 8 * 3 = (s.x 31).toNat - 8 * (2 + 1) by omega]; simpa using v1 2 (by omega)
    have hF' : F (s1.m ((s1.x 31).toNat + 16)) (s1.m ((s1.x 31).toNat + 8)) (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 =
        some (v, H3) := by
      rw [va, vb, vc, p1, show (s.x 31).toNat - 8 * 3 = (s.x 31).toNat - 24 by omega]; exact hF
    obtain ⟨s3, st3, q31, qv, R3, A3, qx, qm⟩ := hU s1 H1 v H3 I1 z1 R1 (by rw [p1]; have := O0.1; have := O0.2.2; omega) K1 A1 hF'
    rw [p1, show (s.x 31).toNat - 8 * 3 + 16 = (s.x 31).toNat - 8 by omega] at q31 qv qm
    exact finTail hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 A3 q31 qv R3 qx qm (by omega) (by omega)


theorem fin2_alu {KL : LayW} {C : List J} {q op : Nat} {Inv : St → Prop} {hb E0 : Nat} (hC : At C q (binT op))
    (hop : 1 ≤ op ∧ op ≤ 8) : Fin2S KL C q 5 Inv hb E0 (aluF2 op) := by
  intro s2 H2 v H3 I2 z2 hR hl K2 A2 hF
  simp only [aluF2, Option.some.injEq, Prod.mk.injEq] at hF
  obtain ⟨rfl, rfl⟩ := hF
  have h31 : hb ≤ (s2.x 31).toNat := by have := hR.2.1; have := hR.2.2.1; omega
  have hr := bin_srun (K := KL) s2 hC hl hop (by simpa using K2.wok h31 (i := 0) (by omega)) (K2.wok h31 (i := 1) (by omega))
  have t8' : (s2.x 31 + 8).toNat = (s2.x 31).toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨_, hr, ?_, ?_, ?_, A2, ?_, ?_⟩
  · simp [upd, t8']
  · simp [upd_same]
  · refine HRel_stack hR (by simp [upd_ne]) (by simp [upd, t8']; have := hR.2.2.1; omega) ?_
    intro a h1 h2; simp only []; rw [upd_other _ _ (by have := hR.2.2.1; omega)]
  · intro r h5 h6 _ _ _ h31; simp [upd_ne, h5, h6, h31]
  · intro a ha _; simp only []; rw [upd_other _ _ ha]

theorem fin1_rd {KL : LayW} {C : List J} {q : Nat} {Inv : St → Prop} {hb E0 : Nat} {c28 c29 : UInt64}
    {inp : Nat → UInt64} (hC : At C q rdT) (hInv : InpOK Inv c28 c29 inp) (hW : InpW KL Inv) :
    Fin1S KL C q 6 Inv hb E0 (rdF1 c29 inp) := by
  intro s1 H1 v H2 I1 z1 hR K1 A1 hF
  simp only [rdF1, Option.some.injEq, Prod.mk.injEq] at hF
  obtain ⟨rfl, rfl⟩ := hF
  obtain ⟨h28, h29, hin, hb'⟩ := hInv s1 I1
  have h31 : hb ≤ (s1.x 31).toNat := by have := hR.2.1; have := hR.2.2.1; omega
  have hk := rd_srun (K := KL) s1 hC z1 (by rw [h28, h29]; exact hb') (by simpa using K1.wok h31 (i := 0) (by omega))
    (fun hi => hW s1 I1 _ hi)
  have ev : (if (s1.m (s1.x 31).toNat).toNat < (s1.x 29).toNat then
      lbm s1.m ((s1.x 28).toNat + (s1.m (s1.x 31).toNat).toNat) else 0) =
      (if (s1.m (s1.x 31).toNat).toNat < c29.toNat then inp (s1.m (s1.x 31).toNat).toNat else 0) := by
    rw [h29, h28]
    by_cases hi : (s1.m (s1.x 31).toNat).toNat < c29.toNat
    · simp only [hi, if_true]; rw [hin _ hi]
    · simp only [hi, if_false]
  rw [ev] at hk
  refine ⟨_, hk, ?_, ?_, ?_, A1, ?_, ?_⟩
  · simp [upd_ne]
  · simp [upd_same]
  · refine HRel_stack hR (by simp [upd_ne]) (by simp [upd_ne]; exact hR.2.2.1) ?_
    intro a h1 h2; simp only []; rw [upd_other _ _ (by have := hR.2.2.1; omega)]
  · intro r h5 h6 _ _ _; simp [upd_ne, h5, h6]
  · intro a ha _; simp only []; rw [upd_other _ _ ha]

/-- a heap cell (inside [hb, H.top), aligned) is a work cell -/
theorem heap_wok {KL : LayW} {hb E0 n : Nat} {s : St} {H : Hp} (R : HRel hb s H) (K : StkOK KL hb E0 n s) {a : Nat}
    (h1 : hb ≤ a) (h2 : a + 8 ≤ H.top) (h3 : a % 8 = 0) : wok KL a :=
  ⟨by have := K.lo; omega, by have := K.hi; have := K.top; have := R.2.2.1; omega, h3⟩

theorem hread_wok {KL : LayW} {hb E0 n : Nat} {s : St} {H : Hp} (R : HRel hb s H) (K : StkOK KL hb E0 n s)
    (A : HAl H) {a : Nat} {v : UInt64} (h : hread hb H a = some v) : wok KL a := by
  unfold hread at h; split at h
  · rename_i hc
    have h8 := A a v h; have := R.2.2.2.1
    exact heap_wok R K hc.1 (by omega) h8
  · simp at h

theorem bufInfo_al {hb : Nat} {H : Hp} {b : UInt64} {lc : UInt64 × UInt64} (h : bufInfo hb H b = some lc) :
    b.toNat % 8 = 0 := by
  unfold bufInfo at h; split at h
  · rename_i hc; exact hc.2
  · simp at h

theorem fin1_bsize {KL : LayW} {C : List J} {q : Nat} {Inv : St → Prop} {hb E0 : Nat} (hC : At C q bsizeT) :
    Fin1S KL C q 3 Inv hb E0 (bsizeF hb) := by
  intro s1 H1 v H2 I1 z1 hR K1 A1 hF
  simp only [bsizeF, Option.map_eq_some_iff] at hF
  obtain ⟨len, hl, hv⟩ := hF
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  have hm := hread_mem hR hl
  have h31 : hb ≤ (s1.x 31).toNat := by have := hR.2.1; have := hR.2.2.1; omega
  have hr := bsize_srun (K := KL) s1 hC (by simpa using K1.wok h31 (i := 0) (by omega)) (hread_wok hR K1 A1 hl)
  have := hread_lt hl
  refine ⟨_, hr, ?_, ?_, ?_, A1, ?_, ?_⟩
  · simp [upd_ne]
  · simp [hm, upd_same]
  · refine HRel_stack hR (by simp [upd_ne]) (by simp; exact hR.2.2.1) ?_
    intro a h1 h2; simp only []; rw [upd_other _ _ (by have := hR.2.2.1; omega)]
  · intro r h5 h6 h7 h14 h15; simp [upd_ne, h5]
  · intro a ha _; simp only []; rw [upd_other _ _ ha]

theorem fin2_bget {KL : LayW} {C : List J} {q : Nat} {Inv : St → Prop} {hb E0 : Nat} (hC : At C q bgetT) :
    Fin2S KL C q 10 Inv hb E0 (bgetF hb) := by
  intro s2 H2 v H3 I2 z2 hR hl K2 A2 hF
  simp only [bgetF, Option.bind_eq_some_iff] at hF
  obtain ⟨len, hlen, hF⟩ := hF
  have hbuf := hread_mem hR hlen
  have hrng := hread_lt hlen
  have key : (s2.m (s2.m ((s2.x 31).toNat + 8)).toNat).toNat > (s2.m (s2.x 31).toNat).toNat →
      (s2.m ((s2.x 31).toNat + 8)).toNat + 16 + 8 * (s2.m (s2.x 31).toNat).toNat < 2 ^ 63 := by
    intro hg; rw [hbuf] at hg
    by_cases hi : (s2.m (s2.x 31).toNat).toNat < len.toNat
    · simp only [hi, if_true] at hF
      by_cases hc : (s2.m ((s2.x 31).toNat + 8)).toNat + 16 + 8 * (s2.m (s2.x 31).toNat).toNat < 2 ^ 62
      · omega
      · simp only [hc, if_false] at hF; exact absurd hF (by simp)
    · omega
  have h31 : hb ≤ (s2.x 31).toNat := by have := hR.2.1; have := hR.2.2.1; omega
  have wel : (s2.m (s2.x 31).toNat).toNat < (s2.m (s2.m ((s2.x 31).toNat + 8)).toNat).toNat →
      wok KL ((s2.m ((s2.x 31).toNat + 8)).toNat + 16 + 8 * (s2.m (s2.x 31).toNat).toNat) := by
    intro hg; rw [hbuf] at hg
    simp only [hg, if_true] at hF
    by_cases hc : (s2.m ((s2.x 31).toNat + 8)).toNat + 16 + 8 * (s2.m (s2.x 31).toNat).toNat < 2 ^ 62
    · simp only [hc, if_true, Option.map_eq_some_iff] at hF
      obtain ⟨w, hw, _⟩ := hF
      exact hread_wok hR K2 A2 hw
    · simp only [hc, if_false] at hF; exact absurd hF (by simp)
  obtain ⟨s3, hk, hm, hx, hxr⟩ := bget_srun (K := KL) s2 hC z2 hl key (by simpa using K2.wok h31 (i := 0) (by omega))
    (K2.wok h31 (i := 1) (by omega)) (hread_wok hR K2 A2 hlen) wel
  have lt64 := (s2.x 31).toNat_lt
  have hv : s3.m ((s2.x 31).toNat + 8) = v := by
    rw [hm, upd_same]
    by_cases hi : (s2.m (s2.x 31).toNat).toNat < len.toNat
    · simp only [hi, if_true] at hF
      by_cases hc : (s2.m ((s2.x 31).toNat + 8)).toNat + 16 + 8 * (s2.m (s2.x 31).toNat).toNat < 2 ^ 62
      · simp only [hc, if_true, Option.map_eq_some_iff] at hF
        obtain ⟨w, hw, hwv⟩ := hF
        simp only [Prod.mk.injEq] at hwv
        rw [hbuf, if_pos hi, hread_mem hR hw]; exact hwv.1
      · simp only [hc, if_false] at hF; exact absurd hF (by simp)
    · simp only [hi, if_false, Option.some.injEq, Prod.mk.injEq] at hF
      rw [hbuf, if_neg hi]; exact hF.1
  have hH : H3 = H2 := by
    by_cases hi : (s2.m (s2.x 31).toNat).toNat < len.toNat
    · simp only [hi, if_true] at hF
      by_cases hc : (s2.m ((s2.x 31).toNat + 8)).toNat + 16 + 8 * (s2.m (s2.x 31).toNat).toNat < 2 ^ 62
      · simp only [hc, if_true, Option.map_eq_some_iff] at hF
        obtain ⟨w, hw, hwv⟩ := hF
        simp only [Prod.mk.injEq] at hwv; exact hwv.2.symm
      · simp only [hc, if_false] at hF; exact absurd hF (by simp)
    · simp only [hi, if_false, Option.some.injEq, Prod.mk.injEq] at hF; exact hF.2.symm
  subst hH
  have x31 : (s3.x 31).toNat = (s2.x 31).toNat + 8 := by rw [hx]; simp only [UInt64.toNat_ofNat']; omega
  refine ⟨s3, hk, x31, hv, ?_, A2, ?_, ?_⟩
  · refine HRel_stack hR (hxr 30 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [x31]; have := hR.2.2.1; omega) ?_
    intro a h1 h2; rw [hm]; apply upd_other; have := hR.2.2.1; omega
  · intro r h5 h6 h7 h14 h15 h31; exact hxr r h5 h6 h7 h14 h31
  · intro a ha _; rw [hm]; exact upd_other _ _ ha

theorem fin2_bpush {KL : LayW} {C : List J} {q : Nat} {Inv : St → Prop} {hb E0 : Nat} (hC : At C q (bpushT 6 q)) :
    Fin2S KL C q 12 Inv hb E0 (bpushF hb) := by
  intro s2 H2 v H3 I2 z2 hR hl K2 A2 hF
  simp only [bpushF, Option.bind_eq_some_iff] at hF
  obtain ⟨⟨len, cap⟩, hbi, hF⟩ := hF
  obtain ⟨hbb, hrl, hrc, hlc, hcap⟩ := bufInfo_spec hbi
  have ml := hread_mem hR hrl
  have mc := hread_mem hR hrc
  dsimp only at hF
  by_cases hg : len.toNat < cap.toNat ∧ (s2.m ((s2.x 31).toNat + 8)).toNat + 16 + 8 * len.toNat < 2 ^ 62
  · simp only [hg, and_self, if_true, Option.some.injEq, Prod.mk.injEq] at hF
    obtain ⟨hv, hH⟩ := hF
    subst hH
    have h31 : hb ≤ (s2.x 31).toNat := by have := hR.2.1; have := hR.2.2.1; omega
    have hal := bufInfo_al hbi
    obtain ⟨s3, hk, hm, hx, hb', hxr⟩ := bpush_srun (K := KL) s2 hC z2 hl (by rw [ml, mc]; exact hg.1)
      (by rw [ml]; exact hg.2) (by simpa using K2.wok h31 (i := 0) (by omega)) (K2.wok h31 (i := 1) (by omega))
      (hread_wok hR K2 A2 hrl) (hread_wok hR K2 A2 hrc)
      (by rw [ml]; exact heap_wok hR K2 (by omega) (by omega) (by omega))
    rw [ml] at hm
    have hbT := (hread_lt hrl).2
    have htop := hR.2.2.1
    have hsm := s2.m
    generalize hbuf : s2.m ((s2.x 31).toNat + 8) = buf at *
    generalize hc : buf.toNat + 16 + 8 * len.toNat = c at *
    have lt64 := (s2.x 31).toNat_lt
    have x31 : (s3.x 31).toNat = (s2.x 31).toNat + 8 := hx
    have hcT : c + 8 ≤ H2.top := by omega
    have hne : buf.toNat ≠ c := by omega
    have e30 := hxr 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨s3, hk, x31, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm, upd_other _ _ (by omega), upd_other _ _ (by omega), hbuf, hv]
    · refine ⟨hR.1, hR.2.1, (by show H2.top ≤ (s3.x 31).toNat; omega), hR.2.2.2.1, by rw [e30]; exact hR.2.2.2.2.1, ?_⟩
      intro a w h1 h2 hw
      rw [hm]
      by_cases ha : a = buf.toNat
      · subst ha
        simp only [if_true, Option.some.injEq] at hw
        rw [← hw, upd_same]
      · by_cases hac : a = c
        · subst hac
          simp only [ha, if_false, if_true, Option.some.injEq] at hw
          rw [← hw, upd_other _ _ (Ne.symm hne), upd_same]
        · simp only [ha, hac, if_false] at hw
          rw [upd_other _ _ ha, upd_other _ _ hac]; exact hR.2.2.2.2.2 a w h1 h2 hw
    · intro a w hw
      simp only [] at hw
      by_cases ha : a = buf.toNat
      · omega
      · by_cases hac : a = c
        · omega
        · simp only [ha, hac, if_false] at hw; exact A2 a w hw
    · intro r h5 h6 h7 h14 h15 h31; exact hxr r h5 h6 h7 h14 h15 h31
    · intro a ha hn; have hn' : ¬(hb ≤ a ∧ a < H2.top) := hn
      rw [hm]; rw [upd_other _ _ (by omega), upd_other _ _ (by omega)]
  · simp only [hg, if_false] at hF; exact absurd hF (by simp)

theorem fin3_bset {KL : LayW} {C : List J} {q : Nat} {Inv : St → Prop} {hb E0 : Nat} (hC : At C q bsetT) :
    Fin3S KL C q 9 Inv hb E0 (bsetF hb) := by
  intro s3 H3 v H4 I3 z3 hR hl K3 A3 hF
  simp only [bsetF, Option.bind_eq_some_iff] at hF
  obtain ⟨⟨len, cap⟩, hbi, hF⟩ := hF
  obtain ⟨hbb, hrl, hrc, hlc, hcap⟩ := bufInfo_spec hbi
  have ml := hread_mem hR hrl
  dsimp only at hF
  have htop := hR.2.2.1
  have lt64 := (s3.x 31).toNat_lt
  have hB : (s3.m ((s3.x 31).toNat + 16)).toNat + 16 + 8 * (s3.m ((s3.x 31).toNat + 8)).toNat < 2 ^ 62 ∨
      ¬ (s3.m ((s3.x 31).toNat + 8)).toNat < len.toNat := by
    by_cases hi : (s3.m ((s3.x 31).toNat + 8)).toNat < len.toNat
    · left
      simp only [hi, if_true] at hF
      by_cases hc : (s3.m ((s3.x 31).toNat + 16)).toNat + 16 + 8 * (s3.m ((s3.x 31).toNat + 8)).toNat < 2 ^ 62
      · exact hc
      · simp only [hc, if_false] at hF; exact absurd hF (by simp)
    · right; exact hi
  have h31 : hb ≤ (s3.x 31).toNat := by have := hR.2.1; have := hR.2.2.1; omega
  have hal := bufInfo_al hbi
  obtain ⟨s4, hk, hm, hx, hb', hxr⟩ := bset_srun (K := KL) s3 hC z3 hl (by
    intro hg; rw [ml] at hg; rcases hB with h | h
    · exact h
    · omega) (by simpa using K3.wok h31 (i := 0) (by omega)) (K3.wok h31 (i := 1) (by omega))
    (K3.wok h31 (i := 2) (by omega)) (hread_wok hR K3 A3 hrl)
    (fun hg => by rw [ml] at hg; exact heap_wok hR K3 (by omega) (by omega) (by omega))
  rw [ml] at hm
  have hbT := (hread_lt hrl).2
  generalize hbuf : s3.m ((s3.x 31).toNat + 16) = buf at *
  generalize hidx : s3.m ((s3.x 31).toNat + 8) = idx at *
  generalize hval : s3.m (s3.x 31).toNat = w at *
  have e30 := hxr 30 (by decide) (by decide) (by decide) (by decide) (by decide)
  have x31 : (s4.x 31).toNat = (s3.x 31).toNat + 16 := hx
  by_cases hi : idx.toNat < len.toNat
  · have hc : buf.toNat + 16 + 8 * idx.toNat < 2 ^ 62 := by
      rcases hB with h | h
      · exact h
      · exact absurd hi h
    simp only [hi, hc, if_true, Option.some.injEq, Prod.mk.injEq] at hF
    obtain ⟨hv, hH⟩ := hF
    subst hH
    have hcT : buf.toNat + 16 + 8 * idx.toNat + 8 ≤ H3.top := by omega
    rw [if_pos hi] at hm
    refine ⟨s4, hk, x31, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm, upd_other _ _ (by omega), hbuf, hv]
    · refine ⟨hR.1, hR.2.1, (by show H3.top ≤ (s4.x 31).toNat; omega), hR.2.2.2.1, by rw [e30]; exact hR.2.2.2.2.1, ?_⟩
      intro a y h1 h2 hy
      rw [hm]
      by_cases hac : a = buf.toNat + 16 + 8 * idx.toNat
      · subst hac
        simp only [if_true, Option.some.injEq] at hy
        rw [← hy, upd_same]
      · simp only [hac, if_false] at hy
        rw [upd_other _ _ hac]; exact hR.2.2.2.2.2 a y h1 h2 hy
    · intro a y hy
      simp only [] at hy
      by_cases hac : a = buf.toNat + 16 + 8 * idx.toNat
      · omega
      · simp only [hac, if_false] at hy; exact A3 a y hy
    · intro r h5 h6 h7 h14 h15 h31; exact hxr r h5 h6 h7 h14 h31
    · intro a ha hn; have hn' : ¬(hb ≤ a ∧ a < H3.top) := hn
      rw [hm, upd_other _ _ (by omega)]
  · simp only [hi, if_false, Option.some.injEq, Prod.mk.injEq] at hF
    obtain ⟨hv, hH⟩ := hF
    subst hH
    rw [if_neg hi] at hm
    refine ⟨s4, hk, x31, ?_, ?_, A3, ?_, ?_⟩
    · rw [hm, hbuf, hv]
    · refine ⟨hR.1, hR.2.1, (by show H3.top ≤ (s4.x 31).toNat; omega), hR.2.2.2.1, by rw [e30]; exact hR.2.2.2.2.1, ?_⟩
      intro a y h1 h2 hy
      rw [hm]; exact hR.2.2.2.2.2 a y h1 h2 hy
    · intro r h5 h6 h7 h14 h15 h31; exact hxr r h5 h6 h7 h14 h31
    · intro a ha hn; rw [hm]


theorem bnew_EVH {KL : LayW} {C : List J} {pc tgt κ p nl hb E0 : Nat} {Inv : St → Prop} (hI : InvOKH hb p Inv)
    (hC : At C pc (bnewT tgt pc κ)) :
    EVHS KL C pc (bnewT tgt pc κ).length p nl Inv hb E0 (fun _ => False) (fun _ => False) (bnewS κ) where
  stable := fun _ _ _ _ _ => rfl
  run := fun s env H v H' I0 hx0 hF hO hR L0 A0 hS => by
    have hR0 := hR
    obtain ⟨hb16, hb1, htop, hal, hx30, hcells⟩ := hR
    simp only [bnewS] at hS
    by_cases hg : H.top + 8 * (κ + 2) + 8 ≤ (s.x 31).toNat ∧ (s.x 31).toNat < 2 ^ 62 ∧ κ < 2 ^ 40
    · simp only [hg, and_self, if_true, Option.some.injEq, Prod.mk.injEq] at hS
      obtain ⟨hv, hH⟩ := hS
      subst hH
      obtain ⟨hr, hsp, hk⟩ := hg
      have hO' := hO
      obtain ⟨o1, o2, o3⟩ := hO'
      have hE : (s.x 31).toNat ≤ E0 := by have := L0.top; omega
      obtain ⟨s', hk', x31, x30, x5, hm, hb', hxr⟩ := bnew_srun (L := KL) s hC hx0 hk hsp (by rw [hx30]; exact hr)
        (by rw [hx30]; exact L0.wok (by omega) (by omega) hal) (by rw [hx30]; exact L0.wok (by omega) (by omega) (by omega))
        (L0.wok (by omega) (by omega) (by have := L0.a31; omega))
      have lt64 := (s.x 31).toNat_lt
      have lt30 := (s.x 30).toNat_lt
      have e30 : s.x 30 = UInt64.ofNat H.top := by rw [← hx30]; simp
      have hFK := hO
      obtain ⟨hf1, hf2, hf3⟩ := hO
      have sl : ∀ k, k < nl → (s.x 31).toNat ≤ slotAddr p (s.x 8).toNat k := fun k hk => slotAddr_ge hf1 hf2 hk
      rw [hx30] at hm
      have hne1 : ∀ a, a < (s.x 31).toNat - 8 → a ≠ (s.x 31).toNat - 8 := fun a h => by omega
      refine ⟨s', env, hk', ?_, hxr 0 (by decide) (by decide) (by decide) (by decide) (by decide) ▸ hx0, x31, ?_,
        hxr 8 (by decide) (by decide) (by decide) (by decide) (by decide), ?_, fun _ _ => rfl, ?_, ?_, ?_⟩
      · apply hI s s' I0 (hxr 8 (by decide) (by decide) (by decide) (by decide) (by decide))
          (hxr 28 (by decide) (by decide) (by decide) (by decide) (by decide))
          (hxr 29 (by decide) (by decide) (by decide) (by decide) (by decide)) hb' hk'.star.w
        intro a ha
        rw [hm, upd_other _ _ (by omega), upd_other _ _ (by omega), upd_other _ _ (by omega)]
      · rw [hm, upd_same, e30]; exact hv
      · intro k hk
        rw [hxr 8 (by decide) (by decide) (by decide) (by decide) (by decide), hm, upd_other _ _ (by have := sl k hk; omega),
          upd_other _ _ (by have := sl k hk; omega), upd_other _ _ (by have := sl k hk; omega)]
        exact hF k hk
      · refine ⟨hb16, (by show hb ≤ H.top + 8 * (κ + 2); omega), ?_, (by show (H.top + 8 * (κ + 2)) % 8 = 0; omega), ?_, ?_⟩
        · show H.top + 8 * (κ + 2) ≤ (s'.x 31).toNat; omega
        · show (s'.x 30).toNat = H.top + 8 * (κ + 2); omega
        · intro a w h1 h2 hw
          show s'.m a = w
          rw [hm]
          have h2' : a < H.top + 8 * (κ + 2) := h2
          by_cases ha : a = H.top
          · subst ha; simp only [if_true, Option.some.injEq] at hw
            rw [← hw, upd_other _ _ (by omega), upd_other _ _ (by omega), upd_same]
          · by_cases hb8 : a = H.top + 8
            · subst hb8; simp only [ha, if_false, if_true, Option.some.injEq] at hw
              rw [← hw, upd_other _ _ (by omega), upd_same]
            · by_cases hlt : a < H.top
              · simp only [ha, hb8, hlt, if_false, if_true] at hw
                rw [upd_other _ _ (by omega), upd_other _ _ (by omega), upd_other _ _ (by omega)]
                exact hcells a w h1 hlt hw
              · simp only [ha, hb8, hlt, if_false] at hw; exact absurd hw (by simp)
      · intro a w hw
        simp only [] at hw
        by_cases ha : a = H.top
        · omega
        · by_cases hb8 : a = H.top + 8
          · omega
          · by_cases hlt : a < H.top
            · simp only [ha, hb8, hlt, if_false, if_true] at hw; exact A0 a w hw
            · simp only [ha, hb8, hlt, if_false] at hw; exact absurd hw (by simp)
      · intro a ha _
        rw [hm, upd_other _ _ (by omega), upd_other _ _ (by omega), upd_other _ _ (by omega)]
    · simp only [hg, if_false] at hS; exact absurd hS (by simp)


/-- BNEW κ -/
theorem bnewX {KL : LayW} {C : List J} {pc κ p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    (hI : InvOKH hb p Inv) (hC : At C pc (bnewT 1 pc κ)) :
    EVHwS KL C pc (bnewT 1 pc κ).length p nl Inv hb E0 R W 1 (one (bnewS κ)) :=
  (ofEVH (bnew_EVH (nl := nl) hI hC)).mono (fun _ h => h.elim) (fun _ h => h.elim)

end Templates
