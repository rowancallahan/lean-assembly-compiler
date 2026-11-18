/- The HEAP environment contract `EVH` (success path first): fragments that may allocate / write heap buffers.
`Hp` = heap image (top + known cells); `HRel hb s H` ties it to the machine: t5 = top, hb ≤ top ≤ t6, 8-aligned, and every known
cell [hb, top) equals memory.  `EVH` is `Templates.EV` plus the heap: the semantic function threads the heap image
(`S env sp H = some (v, H')` is the success case).  `lift_EV` makes every non-heap EV leaf an EVH. -/
import Nano.V2Self.Proof.Templates
import Nano.V2Self.Proof.Heap
namespace Templates
open CallProbe

structure Hp where
  top : Nat
  m : Nat → Option UInt64

/-- memory agrees with the heap image on its known cells; t5 is the heap top -/
def HI (hb : Nat) (H : Hp) (s : St) : Prop :=
  (s.x 30).toNat = H.top ∧ ∀ a v, hb ≤ a → a < H.top → H.m a = some v → s.m a = v

def HRel (hb : Nat) (s : St) (H : Hp) : Prop :=
  16 ≤ hb ∧ hb ≤ H.top ∧ H.top ≤ (s.x 31).toNat ∧ H.top % 8 = 0 ∧ HI hb H s

/-- `Inv` reads only s0, x28, x29 and memory outside [hb, frame top) -/
def InvOKH (hb p : Nat) (Inv : St → Prop) : Prop :=
  ∀ s s' : St, Inv s → s'.x 8 = s.x 8 → s'.x 28 = s.x 28 → s'.x 29 = s.x 29 →
    (∀ a, ¬ (hb ≤ a ∧ a < (s.x 8).toNat + 8 * p + 16) → s'.m a = s.m a) → Inv s'

/-- bridge: with the heap image kept in the invariant, `InvOKH` gives EV's `InvOK` -/
theorem invOK_of_H {hb p : Nat} {Inv : St → Prop} (h : InvOKH hb p Inv) (H : Hp) (hh : hb ≤ H.top) :
    InvOK p (fun s => Inv s ∧ HI hb H s) := by
  intro s s' ⟨I, hx30, hm⟩ e8 e28 e29 e30 hmem
  refine ⟨h s s' I e8 e28 e29 ?_, ?_, ?_⟩
  · intro a ha; apply hmem; intro ⟨h1, h2⟩; apply ha; refine ⟨by omega, ?_⟩; omega
  · rw [e30, hx30]
  · intro a v h1 h2 hv; rw [hmem a (by intro ⟨q1, q2⟩; omega)]; exact hm a v h1 h2 hv

structure EVH (C : List J) (pc len p nl : Nat) (Inv : St → Prop) (hb : Nat) (R W : Nat → Prop)
    (S : (Nat → UInt64) → Nat → Hp → Option (UInt64 × Hp)) : Prop where
  run : ∀ (s : St) (env : Nat → UInt64) (H : Hp) (v : UInt64) (H' : Hp), Inv s → s.x 0 = 0 → Frame p nl s env →
    FrameOK p nl s → HRel hb s H →
    S env (s.x 31).toNat H = some (v, H') →
    ∃ s' env', Star C (pc, s) (pc + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
      s'.m ((s.x 31).toNat - 8) = v ∧ s'.x 8 = s.x 8 ∧ Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧
      HRel hb s' H' ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  stable : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H

/-- every non-heap EV fragment (for every heap image) is an EVH; success needs the stack room `n` the EV asks for -/
theorem lift_EV {C : List J} {pc len n p nl hb : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    {V : (Nat → UInt64) → UInt64}
    (hEV : ∀ H : Hp, EV C pc len n p nl (fun s => Inv s ∧ HI hb H s) R W V) (hn : 1 ≤ n) :
    EVH C pc len p nl Inv hb R W (fun env sp H => if H.top + 8 * n ≤ sp then some (V env, H) else none) where
  stable := fun env env' sp H h => by rw [(hEV H).stable env env' h]
  run := fun s env H v H' I0 hx0 hF hO hR hS => by
    obtain ⟨hb16, hb1, htop, hal, hHI⟩ := hR
    by_cases hc : H.top + 8 * n ≤ (s.x 31).toNat
    · rw [if_pos hc] at hS
      simp only [Option.some.injEq, Prod.mk.injEq] at hS
      obtain ⟨rfl, rfl⟩ := hS
      obtain ⟨s', env', r, ⟨I1, hHI1⟩, z, p31, vm, e8, e30, F, ag, mm⟩ :=
        (hEV H).run s env ⟨I0, hHI⟩ hx0 hF hO (by rw [hHI.1]; exact hc)
      refine ⟨s', env', r, I1, z, p31, vm, e8, F, ag, ⟨hb16, hb1, ?_, hal, hHI1⟩, mm⟩
      rw [p31]; omega
    · rw [if_neg hc] at hS; exact absurd hS (by simp)

/-- the closing fragment of a two-operand step (pops two words, pushes the result over the new top) -/
def Fin2 (C : List J) (q lu : Nat) (Inv : St → Prop) (hb : Nat)
    (F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s2 : St) (H2 : Hp) (v : UInt64) (H3 : Hp), Inv s2 → s2.x 0 = 0 → HRel hb s2 H2 → (s2.x 31).toNat + 16 < 2 ^ 63 →
    F (s2.m ((s2.x 31).toNat + 8)) (s2.m (s2.x 31).toNat) (s2.x 31).toNat H2 = some (v, H3) →
    ∃ s3 : St, Star C (q, s2) (q + lu, s3) ∧ (s3.x 31).toNat = (s2.x 31).toNat + 8 ∧ s3.m ((s2.x 31).toNat + 8) = v ∧
      HRel hb s3 H3 ∧ (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s3.x r = s2.x r) ∧
      ∀ a, a ≠ (s2.x 31).toNat + 8 → ¬ (hb ≤ a ∧ a < H3.top) → s3.m a = s2.m a

/-- A; B; a closing fragment: operands A (below), B (top), heap threaded -/
theorem bin_gen_EVH {C : List J} {pc la lb lu p nl hb : Nat} {F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    {Inv : St → Prop} {RA WA RB WB : Nat → Prop}
    {SA SB : (Nat → UInt64) → Nat → Hp → Option (UInt64 × Hp)} (hI : InvOKH hb p Inv)
    (hA : EVH C pc la p nl Inv hb RA WA SA) (hB : EVH C (pc + la) lb p nl Inv hb RB WB SB)
    (hU : Fin2 C (pc + la + lb) lu Inv hb F) (hsc : ∀ k, RB k → ¬ WA k) :
    EVH C pc (la + lb + lu) p nl Inv hb (fun k => RA k ∨ RB k) (fun k => WA k ∨ WB k)
      (fun env sp H => (SA env sp H).bind fun r1 => (SB env (sp - 8) r1.2).bind fun r2 => F r1.1 r2.1 (sp - 16) r2.2) where
  stable := fun env env' sp H h => by
    rw [hA.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases hA' : SA env' sp H with
    | none => rfl
    | some r1 => simp only [Option.bind_some]; rw [hB.stable env env' (sp - 8) r1.2 (fun k hk => h k (Or.inr hk))]
  run := fun s env H v H' hI0 hx0 hF hO hR hS => by
    obtain ⟨o1, o2, o3⟩ := hO
    have lt64 := (s.x 31).toNat_lt
    simp only [Option.bind_eq_some_iff] at hS
    obtain ⟨⟨a, H1⟩, hSA, ⟨b, H2⟩, hSB, hSF⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, F1, ag1, hR1, m1⟩ := hA.run s env H a H1 hI0 hx0 hF ⟨o1, o2, o3⟩ hR hSA
    have hs1 : 16 ≤ (s1.x 31).toNat := by have := hR1.1; have := hR1.2.1; have := hR1.2.2.1; omega
    have hO1 : FrameOK p nl s1 := ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩
    have hSB1 : SB env1 ((s1.x 31).toNat) H1 = some (b, H2) := by
      rw [p1, hB.stable env1 env _ _ (fun k hk => ag1 k (hsc k hk))]; exact hSB
    obtain ⟨s2, env2, r2, I2, z2, p2, v2, e82, F2, ag2, hR2, m2⟩ :=
      hB.run s1 env1 H1 b H2 I1 z1 F1 hO1 hR1 hSB1
    have hne : ∀ k, k < nl → slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 8 := fun k hk => by
      have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega
    have vB : s2.m ((s.x 31).toNat - 8 - 8) = b := by rw [p1] at p2 v2; exact v2
    have vA : s2.m ((s.x 31).toNat - 8) = a := by
      rw [m2 _ (by omega) (fun k hk _ => by rw [e81]; exact (hne k hk).symm)]; exact v1
    have e2' : (s2.x 31).toNat + 8 = (s.x 31).toNat - 8 := by rw [p2, p1]; omega
    have e2'' : (s2.x 31).toNat = (s.x 31).toNat - 8 - 8 := by rw [p2, p1]
    have hl : (s2.x 31).toNat + 16 < 2 ^ 63 := by rw [p2, p1]; omega
    have hF' : F (s2.m ((s2.x 31).toNat + 8)) (s2.m (s2.x 31).toNat) (s2.x 31).toNat H2 = some (v, H') := by
      rw [e2', e2'', vA, vB]; rw [show (s.x 31).toNat - 8 - 8 = (s.x 31).toNat - 16 by omega]; exact hSF
    obtain ⟨s3, st3, q31, qv, hR3, qx, qm⟩ := hU s2 H2 v H' I2 z2 hR2 hl hF'
    have q8 : s3.x 8 = s.x 8 := by rw [qx 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e82, e81]
    have z3 : s3.x 0 = 0 := by rw [qx 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), z2]
    have top3 : H'.top ≤ (s3.x 31).toNat := hR3.2.2.1
    have p3 : (s3.x 31).toNat = (s.x 31).toNat - 8 := by rw [q31, e2']
    have I3 : Inv s3 := by
      apply hI s2 s3 I2 (by rw [q8, e82, e81])
        (qx 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      intro a ha
      apply qm
      · intro e; apply ha; rw [e, e2', e82, e81]; constructor
        · have := hR1.1; have := hR1.2.1; have := hR1.2.2.1; omega
        · omega
      · intro ⟨q1, q2⟩; apply ha; rw [e82, e81]; constructor
        · exact q1
        · omega
    have F3 : Frame p nl s3 env2 := by
      intro k hk
      show s3.m (slotAddr p (s3.x 8).toNat k) = env2 k
      have hk' := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk
      rw [q8, qm _ (by omega) (by intro ⟨q1, q2⟩; omega)]
      have := F2 k hk; rw [e82, e81] at this; exact this
    refine ⟨s3, env2, ?_, I3, z3, p3, ?_, q8, F3, ?_, hR3, ?_⟩
    · have : pc + la + lb + lu = pc + (la + lb + lu) := by omega
      rw [← this]; exact (r1.trans r2).trans st3
    · rw [← e2', qv]
    · intro k hk
      rw [not_or] at hk
      rw [ag2 k hk.2, ag1 k hk.1]
    · intro a ha hW
      rw [qm a (by omega) (by intro ⟨q1, q2⟩; omega)]
      rw [m2 a (by omega) (fun k hk wk => by rw [e81]; exact hW k hk (Or.inr wk))]
      exact m1 a ha (fun k hk wk => hW k hk (Or.inl wk))

/-- the closing fragment of a one-operand step (rewrites the top word in place) -/
def Fin1 (C : List J) (q lu : Nat) (Inv : St → Prop) (hb : Nat)
    (F : UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s1 : St) (H1 : Hp) (v : UInt64) (H2 : Hp), Inv s1 → s1.x 0 = 0 → HRel hb s1 H1 →
    F (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = some (v, H2) →
    ∃ s3 : St, Star C (q, s1) (q + lu, s3) ∧ s3.x 31 = s1.x 31 ∧ s3.m (s1.x 31).toNat = v ∧
      HRel hb s3 H2 ∧ (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → s3.x r = s1.x r) ∧
      ∀ a, a ≠ (s1.x 31).toNat → ¬ (hb ≤ a ∧ a < H2.top) → s3.m a = s1.m a

/-- A; a closing one-operand fragment -/
theorem un_gen_EVH {C : List J} {pc la lu p nl hb : Nat} {F : UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    {Inv : St → Prop} {RA WA : Nat → Prop} {SA : (Nat → UInt64) → Nat → Hp → Option (UInt64 × Hp)}
    (hI : InvOKH hb p Inv) (hA : EVH C pc la p nl Inv hb RA WA SA) (hU : Fin1 C (pc + la) lu Inv hb F) :
    EVH C pc (la + lu) p nl Inv hb RA WA
      (fun env sp H => (SA env sp H).bind fun r1 => F r1.1 (sp - 8) r1.2) where
  stable := fun env env' sp H h => by
    rw [hA.stable env env' sp H h]
  run := fun s env H v H' hI0 hx0 hF hO hR hS => by
    obtain ⟨o1, o2, o3⟩ := hO
    have lt64 := (s.x 31).toNat_lt
    simp only [Option.bind_eq_some_iff] at hS
    obtain ⟨⟨a, H1⟩, hSA, hSF⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, F1, ag1, hR1, m1⟩ := hA.run s env H a H1 hI0 hx0 hF ⟨o1, o2, o3⟩ hR hSA
    have hs1 : 16 ≤ (s1.x 31).toNat := by have := hR1.1; have := hR1.2.1; have := hR1.2.2.1; omega
    have hne : ∀ k, k < nl → slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 8 := fun k hk => by
      have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega
    have hv : s1.m (s1.x 31).toNat = a := by rw [p1]; exact v1
    have hF' : F (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = some (v, H') := by rw [hv, p1]; exact hSF
    obtain ⟨s3, st3, q31, qv, hR3, qx, qm⟩ := hU s1 H1 v H' I1 z1 hR1 hF'
    have q8 : s3.x 8 = s.x 8 := by rw [qx 8 (by decide) (by decide) (by decide) (by decide) (by decide), e81]
    have z3 : s3.x 0 = 0 := by rw [qx 0 (by decide) (by decide) (by decide) (by decide) (by decide), z1]
    have p3 : (s3.x 31).toNat = (s.x 31).toNat - 8 := by rw [q31, p1]
    have top3 : H'.top ≤ (s3.x 31).toNat := hR3.2.2.1
    have I3 : Inv s3 := by
      apply hI s1 s3 I1 (by rw [q8, e81])
        (qx 28 (by decide) (by decide) (by decide) (by decide) (by decide))
        (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide))
      intro a' ha
      apply qm
      · intro e; apply ha; rw [e, p1, e81]; constructor
        · have := hR1.1; have := hR1.2.1; have := hR1.2.2.1; omega
        · omega
      · intro ⟨q1, q2⟩; apply ha; rw [e81]; constructor
        · exact q1
        · omega
    have F3 : Frame p nl s3 env1 := by
      intro k hk
      show s3.m (slotAddr p (s3.x 8).toNat k) = env1 k
      have hk' := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk
      rw [q8, qm _ (by omega) (by intro ⟨q1, q2⟩; omega)]
      have := F1 k hk; rw [e81] at this; exact this
    refine ⟨s3, env1, ?_, I3, z3, p3, ?_, q8, F3, ag1, hR3, ?_⟩
    · have : pc + la + lu = pc + (la + lu) := by omega
      rw [← this]; exact r1.trans st3
    · rw [← p1]; exact qv
    · intro a' ha hW
      rw [qm a' (by omega) (by intro ⟨q1, q2⟩; omega)]
      exact m1 a' ha hW

/-- the closing fragment of a three-operand step (buf below, index, value on top; result over the buffer's cell) -/
def Fin3 (C : List J) (q lu : Nat) (Inv : St → Prop) (hb : Nat)
    (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s3 : St) (H3 : Hp) (v : UInt64) (H4 : Hp), Inv s3 → s3.x 0 = 0 → HRel hb s3 H3 → (s3.x 31).toNat + 24 < 2 ^ 62 →
    F (s3.m ((s3.x 31).toNat + 16)) (s3.m ((s3.x 31).toNat + 8)) (s3.m (s3.x 31).toNat) (s3.x 31).toNat H3 = some (v, H4) →
    ∃ s4 : St, Star C (q, s3) (q + lu, s4) ∧ (s4.x 31).toNat = (s3.x 31).toNat + 16 ∧
      s4.m ((s3.x 31).toNat + 16) = v ∧ HRel hb s4 H4 ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s4.x r = s3.x r) ∧
      ∀ a, a ≠ (s3.x 31).toNat + 16 → ¬ (hb ≤ a ∧ a < H4.top) → s4.m a = s3.m a

/-- A; B; C; a closing three-operand fragment -/
theorem tri_gen_EVH {C : List J} {pc la lb lc lu p nl hb : Nat}
    {F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)} {Inv : St → Prop} {RA WA RB WB RC WC : Nat → Prop}
    {SA SB SC : (Nat → UInt64) → Nat → Hp → Option (UInt64 × Hp)} (hI : InvOKH hb p Inv)
    (hA : EVH C pc la p nl Inv hb RA WA SA) (hB : EVH C (pc + la) lb p nl Inv hb RB WB SB)
    (hC : EVH C (pc + la + lb) lc p nl Inv hb RC WC SC)
    (hU : Fin3 C (pc + la + lb + lc) lu Inv hb F) (hsB : ∀ k, RB k → ¬ WA k) (hsC : ∀ k, RC k → ¬ WA k ∧ ¬ WB k) :
    EVH C pc (la + lb + lc + lu) p nl Inv hb (fun k => RA k ∨ RB k ∨ RC k) (fun k => WA k ∨ WB k ∨ WC k)
      (fun env sp H => (SA env sp H).bind fun r1 => (SB env (sp - 8) r1.2).bind fun r2 =>
        (SC env (sp - 16) r2.2).bind fun r3 => F r1.1 r2.1 r3.1 (sp - 24) r3.2) where
  stable := fun env env' sp H h => by
    rw [hA.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases hA' : SA env' sp H with
    | none => rfl
    | some r1 =>
      simp only [Option.bind_some]
      rw [hB.stable env env' (sp - 8) r1.2 (fun k hk => h k (Or.inr (Or.inl hk)))]
      cases hB' : SB env' (sp - 8) r1.2 with
      | none => rfl
      | some r2 =>
        simp only [Option.bind_some]
        rw [hC.stable env env' (sp - 16) r2.2 (fun k hk => h k (Or.inr (Or.inr hk)))]
  run := fun s env H v H' hI0 hx0 hF hO hR hS => by
    obtain ⟨o1, o2, o3⟩ := hO
    have lt64 := (s.x 31).toNat_lt
    simp only [Option.bind_eq_some_iff] at hS
    obtain ⟨⟨a, H1⟩, hSA, ⟨b, H2⟩, hSB, ⟨c, H3⟩, hSC, hSF⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, v1, e81, F1, ag1, hR1, m1⟩ := hA.run s env H a H1 hI0 hx0 hF ⟨o1, o2, o3⟩ hR hSA
    have hO1 : FrameOK p nl s1 := ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩
    have hSB1 : SB env1 (s1.x 31).toNat H1 = some (b, H2) := by
      rw [p1, hB.stable env1 env _ _ (fun k hk => ag1 k (hsB k hk))]; exact hSB
    obtain ⟨s2, env2, r2, I2, z2, p2, v2, e82, F2, ag2, hR2, m2⟩ := hB.run s1 env1 H1 b H2 I1 z1 F1 hO1 hR1 hSB1
    have hO2 : FrameOK p nl s2 := ⟨by rw [p2, e82, e81, p1]; omega, o2, by rw [e82, e81]; omega⟩
    have hSC1 : SC env2 (s2.x 31).toNat H2 = some (c, H3) := by
      have : SC env2 (s2.x 31).toNat H2 = SC env (s2.x 31).toNat H2 := hC.stable env2 env _ _ (fun k hk => by
        obtain ⟨n1, n2⟩ := hsC k hk
        rw [ag2 k n2, ag1 k n1])
      rw [this, p2, p1]; rw [show (s.x 31).toNat - 8 - 8 = (s.x 31).toNat - 16 by omega]; exact hSC
    obtain ⟨s3, env3, r3, I3, z3, p3, v3, e83, F3, ag3, hR3, m3⟩ := hC.run s2 env2 H2 c H3 I2 z2 F2 hO2 hR2 hSC1
    have hb16 := hR3.1; have hbt := hR3.2.1; have ht3 := hR3.2.2.1
    have hne : ∀ k, k < nl → slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 8 ∧ slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 16 ∧
        slotAddr p (s.x 8).toNat k ≠ (s.x 31).toNat - 24 := fun k hk => by
      have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega
    have vC : s3.m ((s.x 31).toNat - 24) = c := by rw [p2, p1] at p3 v3; rw [show (s.x 31).toNat - 8 - 8 - 8 = (s.x 31).toNat - 24 by omega] at v3; exact v3
    have vB : s3.m ((s.x 31).toNat - 16) = b := by
      rw [m3 _ (by omega) (fun k hk _ => by rw [e82, e81]; exact (hne k hk).2.1.symm)]
      rw [p1] at p2 v2; rw [show (s.x 31).toNat - 8 - 8 = (s.x 31).toNat - 16 by omega] at v2; exact v2
    have vA : s3.m ((s.x 31).toNat - 8) = a := by
      rw [m3 _ (by omega) (fun k hk _ => by rw [e82, e81]; exact (hne k hk).1.symm)]
      rw [m2 _ (by omega) (fun k hk _ => by rw [e81]; exact (hne k hk).1.symm)]; exact v1
    have sp3 : (s3.x 31).toNat = (s.x 31).toNat - 24 := by rw [p3, p2, p1]; omega
    have hF' : F (s3.m ((s3.x 31).toNat + 16)) (s3.m ((s3.x 31).toNat + 8)) (s3.m (s3.x 31).toNat) (s3.x 31).toNat H3 = some (v, H') := by
      rw [show (s3.x 31).toNat + 16 = (s.x 31).toNat - 8 by omega, show (s3.x 31).toNat + 8 = (s.x 31).toNat - 16 by omega,
        sp3, vA, vB, vC]; exact hSF
    obtain ⟨s4, st4, q31, qv, hR4, qx, qm⟩ := hU s3 H3 v H' I3 z3 hR3 (by omega) hF'
    have q8 : s4.x 8 = s.x 8 := by rw [qx 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e83, e82, e81]
    have z4 : s4.x 0 = 0 := by rw [qx 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), z3]
    have p4 : (s4.x 31).toNat = (s.x 31).toNat - 8 := by rw [q31, sp3]; omega
    have top4 : H'.top ≤ (s4.x 31).toNat := hR4.2.2.1
    have I4 : Inv s4 := by
      apply hI s3 s4 I3 (by rw [q8, e83, e82, e81])
        (qx 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      intro a' ha
      apply qm
      · intro e; apply ha; rw [e, e83, e82, e81]; constructor
        · omega
        · omega
      · intro ⟨q1, q2⟩; apply ha; rw [e83, e82, e81]; constructor
        · exact q1
        · omega
    have F4 : Frame p nl s4 env3 := by
      intro k hk
      show s4.m (slotAddr p (s4.x 8).toNat k) = env3 k
      have hk' := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk
      rw [q8, qm _ (by omega) (by intro ⟨q1, q2⟩; omega)]
      have := F3 k hk; rw [e83, e82, e81] at this; exact this
    refine ⟨s4, env3, ?_, I4, z4, p4, ?_, q8, F4, ?_, hR4, ?_⟩
    · have : pc + la + lb + lc + lu = pc + (la + lb + lc + lu) := by omega
      rw [← this]; exact ((r1.trans r2).trans r3).trans st4
    · rw [show (s.x 31).toNat - 8 = (s3.x 31).toNat + 16 by omega]; exact qv
    · intro k hk
      rw [not_or, not_or] at hk
      rw [ag3 k hk.2.2, ag2 k hk.2.1, ag1 k hk.1]
    · intro a' ha hW
      rw [qm a' (by omega) (by intro ⟨q1, q2⟩; omega)]
      rw [m3 a' (by omega) (fun k hk wk => by rw [e82, e81]; exact hW k hk (Or.inr (Or.inr wk)))]
      rw [m2 a' (by omega) (fun k hk wk => by rw [e81]; exact hW k hk (Or.inr (Or.inl wk)))]
      exact m1 a' ha (fun k hk wk => hW k hk (Or.inl wk))

end Templates
