/- The HEAP environment contract `EVH` (success path first): fragments that may allocate / write heap buffers.
`Hp` = heap image (top + known cells); `HRel hb s H` ties it to the machine: t5 = top, hb ≤ top ≤ t6, 8-aligned, and every known
cell [hb, top) equals memory.  `EVH` is `Templates.EV` plus the heap: the semantic function threads the heap image
(`S env sp H = some (v, H')` is the success case).  `lift_EV` makes every non-heap EV leaf an EVH. -/
import Nano.V2Self.Proof.Machine.Templates
import Nano.V2Self.Proof.Machine.Heap
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

/-- `Inv` reads only s0, x28, x29, the code base and memory outside [hb, frame top) (the code base never changes
along a run: `Star.b`; the machine bridge's global invariant bounds it for return addresses) -/
def InvOKH (hb p : Nat) (Inv : St → Prop) : Prop :=
  ∀ s s' : St, Inv s → s'.x 8 = s.x 8 → s'.x 28 = s.x 28 → s'.x 29 = s.x 29 → s'.b = s.b → s'.wk = s.wk →
    (∀ a, ¬ (hb ≤ a ∧ a < (s.x 8).toNat + 8 * p + 16) → s'.m a = s.m a) → Inv s'

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
        (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) st3.b st3.w
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
        (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide)) st3.b st3.w
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
        (qx 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) st4.b st4.w
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

/-! ## the heap prims as closing fragments -/

/-- a known heap cell -/
def hread (hb : Nat) (H : Hp) (a : Nat) : Option UInt64 := if hb ≤ a ∧ a < H.top then H.m a else none

theorem hread_mem {hb : Nat} {s : St} {H : Hp} {a : Nat} {v : UInt64} (hR : HRel hb s H) (h : hread hb H a = some v) :
    s.m a = v := by
  unfold hread at h; split at h
  · rename_i hc; exact hR.2.2.2.2.2 a v hc.1 hc.2 h
  · simp at h

theorem hread_lt {hb : Nat} {H : Hp} {a : Nat} {v : UInt64} (h : hread hb H a = some v) : hb ≤ a ∧ a < H.top := by
  unfold hread at h; split at h
  · assumption
  · simp at h

/-- only stack-side changes (not in the heap, t5 kept, t6 above the heap) keep the heap relation -/
theorem HRel_stack {hb : Nat} {s s' : St} {H : Hp} (hR : HRel hb s H) (e30 : s'.x 30 = s.x 30)
    (h31 : H.top ≤ (s'.x 31).toNat) (hm : ∀ a, hb ≤ a → a < H.top → s'.m a = s.m a) : HRel hb s' H := by
  obtain ⟨b16, b1, t1, al, hx, hc⟩ := hR
  refine ⟨b16, b1, h31, al, ?_, ?_⟩
  · rw [e30]; exact hx
  · intro a v h1 h2 hv; rw [hm a h1 h2]; exact hc a v h1 h2 hv

/-- BSIZE: the buffer's length word -/
def bsizeF (hb : Nat) : UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun b _ H => (hread hb H b.toNat).map fun len => (len, H)

theorem fin1_bsize {C : List J} {q : Nat} {Inv : St → Prop} {hb : Nat} (hC : At C q bsizeT) :
    Fin1 C q 3 Inv hb (bsizeF hb) := by
  intro s1 H1 v H2 I1 z1 hR hF
  simp only [bsizeF, Option.map_eq_some_iff] at hF
  obtain ⟨len, hl, hv⟩ := hF
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  have hm := hread_mem hR hl
  have hr := bsize_run s1 hC
  have := hread_lt hl
  refine ⟨_, run_star hr, ?_, ?_, ?_, ?_, ?_⟩
  · simp [upd_ne]
  · simp [hm, upd_same]
  · refine HRel_stack hR (by simp [upd_ne]) (by simp; exact hR.2.2.1) ?_
    intro a h1 h2; simp only []; rw [upd_other _ _ (by have := hR.2.2.1; omega)]
  · intro r h5 h6 h7 h14 h15; simp [upd_ne, h5]
  · intro a ha _; simp only []; rw [upd_other _ _ ha]

/-- BGET: word `idx` of buffer `buf` (0 when out of range) -/
def bgetF (hb : Nat) : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun buf idx _ H => (hread hb H buf.toNat).bind fun len =>
    if idx.toNat < len.toNat then
      (if buf.toNat + 16 + 8 * idx.toNat < 2 ^ 62 then (hread hb H (buf.toNat + 16 + 8 * idx.toNat)).map fun w => (w, H) else none)
    else some (0, H)

theorem fin2_bget {C : List J} {q : Nat} {Inv : St → Prop} {hb : Nat} (hC : At C q bgetT) :
    Fin2 C q 10 Inv hb (bgetF hb) := by
  intro s2 H2 v H3 I2 z2 hR hl hF
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
  obtain ⟨k, s3, hk, hm, hx, hxr⟩ := bget_run s2 hC z2 hl key
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
  refine ⟨s3, run_star hk, x31, hv, ?_, ?_, ?_⟩
  · refine HRel_stack hR (hxr 30 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [x31]; have := hR.2.2.1; omega) ?_
    intro a h1 h2; rw [hm]; apply upd_other; have := hR.2.2.1; omega
  · intro r h5 h6 h7 h14 h15 h31; exact hxr r h5 h6 h7 h14 h31
  · intro a ha _; rw [hm]; exact upd_other _ _ ha

/-- a well-formed buffer in the heap image: (len, cap) -/
def bufInfo (hb : Nat) (H : Hp) (b : UInt64) : Option (UInt64 × UInt64) :=
  if hb ≤ b.toNat ∧ b.toNat % 8 = 0 then
    (hread hb H b.toNat).bind fun len => (hread hb H (b.toNat + 8)).bind fun cap =>
      if len.toNat ≤ cap.toNat ∧ b.toNat + 16 + 8 * cap.toNat ≤ H.top then some (len, cap) else none
  else none

theorem bufInfo_spec {hb : Nat} {H : Hp} {b len cap : UInt64} (h : bufInfo hb H b = some (len, cap)) :
    hb ≤ b.toNat ∧ hread hb H b.toNat = some len ∧ hread hb H (b.toNat + 8) = some cap ∧ len.toNat ≤ cap.toNat ∧
      b.toNat + 16 + 8 * cap.toNat ≤ H.top := by
  unfold bufInfo at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, c, hcc, h⟩ := h
    split at h
    · rename_i hh; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨hc.1, hl, hcc, hh.1, hh.2⟩
    · simp at h
  · simp at h

/-- BPUSH / PUT: append `v` to the buffer `buf` (cap exit = failure here); the buffer address stays -/
def bpushF (hb : Nat) : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun buf v _ H => (bufInfo hb H buf).bind fun lc =>
    if lc.1.toNat < lc.2.toNat ∧ buf.toNat + 16 + 8 * lc.1.toNat < 2 ^ 62 then
      some (buf, ⟨H.top, fun a => if a = buf.toNat then some (lc.1 + 1)
        else if a = buf.toNat + 16 + 8 * lc.1.toNat then some v else H.m a⟩)
    else none

theorem fin2_bpush {C : List J} {q : Nat} {Inv : St → Prop} {hb : Nat} (hC : At C q (bpushT 6 q)) :
    Fin2 C q 12 Inv hb (bpushF hb) := by
  intro s2 H2 v H3 I2 z2 hR hl hF
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
    obtain ⟨k, s3, hk, hm, hx, hb', hxr⟩ := bpush_run s2 hC z2 hl (by rw [ml, mc]; exact hg.1) (by rw [ml]; exact hg.2)
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
    refine ⟨s3, run_star hk, x31, ?_, ?_, ?_, ?_⟩
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
    · intro r h5 h6 h7 h14 h15 h31; exact hxr r h5 h6 h7 h14 h15 h31
    · intro a ha hn; have hn' : ¬(hb ≤ a ∧ a < H2.top) := hn
      rw [hm]; rw [upd_other _ _ (by omega), upd_other _ _ (by omega)]
  · simp only [hg, if_false] at hF; exact absurd hF (by simp)

/-- BSET: write `v` at index `idx` when in range (out of range is a no-op); result is the buffer -/
def bsetF (hb : Nat) : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun buf idx v _ H => (bufInfo hb H buf).bind fun lc =>
    if idx.toNat < lc.1.toNat then
      (if buf.toNat + 16 + 8 * idx.toNat < 2 ^ 62 then
        some (buf, ⟨H.top, fun a => if a = buf.toNat + 16 + 8 * idx.toNat then some v else H.m a⟩) else none)
    else some (buf, H)

theorem fin3_bset {C : List J} {q : Nat} {Inv : St → Prop} {hb : Nat} (hC : At C q bsetT) :
    Fin3 C q 9 Inv hb (bsetF hb) := by
  intro s3 H3 v H4 I3 z3 hR hl hF
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
  obtain ⟨k, s4, hk, hm, hx, hb', hxr⟩ := bset_run s3 hC z3 hl (by
    intro hg; rw [ml] at hg; rcases hB with h | h
    · exact h
    · omega)
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
    refine ⟨s4, run_star hk, x31, ?_, ?_, ?_, ?_⟩
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
    · intro r h5 h6 h7 h14 h15 h31; exact hxr r h5 h6 h7 h14 h31
    · intro a ha hn; have hn' : ¬(hb ≤ a ∧ a < H3.top) := hn
      rw [hm, upd_other _ _ (by omega)]
  · simp only [hi, if_false, Option.some.injEq, Prod.mk.injEq] at hF
    obtain ⟨hv, hH⟩ := hF
    subst hH
    rw [if_neg hi] at hm
    refine ⟨s4, run_star hk, x31, ?_, ?_, ?_, ?_⟩
    · rw [hm, hbuf, hv]
    · refine ⟨hR.1, hR.2.1, (by show H3.top ≤ (s4.x 31).toNat; omega), hR.2.2.2.1, by rw [e30]; exact hR.2.2.2.2.1, ?_⟩
      intro a y h1 h2 hy
      rw [hm]; exact hR.2.2.2.2.2 a y h1 h2 hy
    · intro r h5 h6 h7 h14 h15 h31; exact hxr r h5 h6 h7 h14 h31
    · intro a ha hn; rw [hm]

/-- BNEW κ: allocate a zeroed header (len 0, cap κ) at the heap top; the new heap image knows only the header -/
def bnewS (κ : Nat) : (Nat → UInt64) → Nat → Hp → Option (UInt64 × Hp) :=
  fun _ sp H => if H.top + 8 * (κ + 2) + 8 ≤ sp ∧ sp < 2 ^ 62 ∧ κ < 2 ^ 40 then
    some (UInt64.ofNat H.top, ⟨H.top + 8 * (κ + 2), fun a =>
      if a = H.top then some 0 else if a = H.top + 8 then some (UInt64.ofNat κ) else if a < H.top then H.m a else none⟩)
  else none

theorem bnew_EVH {C : List J} {pc tgt κ p nl hb : Nat} {Inv : St → Prop} (hI : InvOKH hb p Inv)
    (hC : At C pc (bnewT tgt pc κ)) :
    EVH C pc (bnewT tgt pc κ).length p nl Inv hb (fun _ => False) (fun _ => False) (bnewS κ) where
  stable := fun _ _ _ _ _ => rfl
  run := fun s env H v H' I0 hx0 hF hO hR hS => by
    obtain ⟨hb16, hb1, htop, hal, hx30, hcells⟩ := hR
    simp only [bnewS] at hS
    by_cases hg : H.top + 8 * (κ + 2) + 8 ≤ (s.x 31).toNat ∧ (s.x 31).toNat < 2 ^ 62 ∧ κ < 2 ^ 40
    · simp only [hg, and_self, if_true, Option.some.injEq, Prod.mk.injEq] at hS
      obtain ⟨hv, hH⟩ := hS
      subst hH
      obtain ⟨hr, hsp, hk⟩ := hg
      obtain ⟨k, s', hk', x31, x30, x5, hm, hb', hxr⟩ := bnew_run s hC hx0 hk hsp (by rw [hx30]; exact hr)
      have lt64 := (s.x 31).toNat_lt
      have lt30 := (s.x 30).toNat_lt
      have e30 : s.x 30 = UInt64.ofNat H.top := by rw [← hx30]; simp
      have hFK := hO
      obtain ⟨hf1, hf2, hf3⟩ := hO
      have sl : ∀ k, k < nl → (s.x 31).toNat ≤ slotAddr p (s.x 8).toNat k := fun k hk => slotAddr_ge hf1 hf2 hk
      rw [hx30] at hm
      have hne1 : ∀ a, a < (s.x 31).toNat - 8 → a ≠ (s.x 31).toNat - 8 := fun a h => by omega
      refine ⟨s', env, run_star hk', ?_, hxr 0 (by decide) (by decide) (by decide) (by decide) (by decide) ▸ hx0, x31, ?_,
        hxr 8 (by decide) (by decide) (by decide) (by decide) (by decide), ?_, fun _ _ => rfl, ?_, ?_⟩
      · apply hI s s' I0 (hxr 8 (by decide) (by decide) (by decide) (by decide) (by decide))
          (hxr 28 (by decide) (by decide) (by decide) (by decide) (by decide))
          (hxr 29 (by decide) (by decide) (by decide) (by decide) (by decide)) (run_star hk').b (run_star hk').w
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
      · intro a ha _
        rw [hm, upd_other _ _ (by omega), upd_other _ _ (by omega), upd_other _ _ (by omega)]
    · simp only [hg, if_false] at hS; exact absurd hS (by simp)

end Templates
