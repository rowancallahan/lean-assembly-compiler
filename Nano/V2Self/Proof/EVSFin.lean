/- Safe retrofit (EVS) P1b: the closing fragments (Opus box E).  `Fin1S/2S/3S` = HeapEV's Fin1/2/3 with SafeX runs;
premise `StkOK` (the operand cells are in the work region, t6 aligned) and `HAl` (heap cells aligned). -/
import Nano.V2Self.Proof.EVSComp
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

theorem finTailS {KL : LayW} {C : List J} {pc q lu t p nl hb : Nat} {Inv : St → Prop} {W : Nat → Prop}
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
      (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) st3.star.b
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

theorem fin2XS {KL : LayW} {C : List J} {pc lp lu p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
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
    exact finTailS hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 A3 q31 qv R3 qx qm (by omega) (by omega)

theorem fin1XS {KL : LayW} {C : List J} {pc lp lu p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
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
    exact finTailS hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 A3 q31' qv R3
      (fun r a b c d e _ => qx r a b c d e) qm (by omega) (by omega)

theorem fin3XS {KL : LayW} {C : List J} {pc lp lu p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemW}
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
    exact finTailS hI s s1 s3 env env1 H3 v I1 z1 O0 e81 F1 ag1 m1 r1 st3 A3 q31 qv R3 qx qm (by omega) (by omega)


end Templates
