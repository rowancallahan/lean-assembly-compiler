/- Safe retrofit (EVS) P2: conversions, empty fragment, sequencing, LOCAL w (Opus box E).  As EVX with SafeX runs;
`Lay` at intermediate states by `Lay.post`. -/
import Nano.V2Self.Proof.EVSLeaf
namespace Templates
open CallProbe SimW SafeRun

theorem ofEVHS {KL : LayW} {C : List J} {pc len p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    {S : Env → Nat → Hp → Option (UInt64 × Hp)} (h : EVHS KL C pc len p nl Inv hb E0 R W S) :
    EVHwS KL C pc len p nl Inv hb E0 R W 1 (one S) where
  stable := fun env env' sp H hk => by simp only [one]; rw [h.stable env env' sp H hk]
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [one, Option.map_eq_some_iff] at hS
    obtain ⟨⟨v, H1⟩, hS, e⟩ := hS
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    obtain ⟨s', env', r, I, z, p31, vm, e8, F, ag, hR, hA, mm⟩ := h.run s env H v H1 I0 z0 F0 O0 R0 L0 A0 hS
    refine ⟨s', env', r, I, z, by rw [p31], rfl, fun i hi => ?_, e8, F, ag, hR, hA, mm⟩
    have : i = 0 := by omega
    subst this; simpa using vm

theorem toEVHS {KL : LayW} {C : List J} {pc len p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {S : SemW}
    (h : EVHwS KL C pc len p nl Inv hb E0 R W 1 S) : EVHS KL C pc len p nl Inv hb E0 R W (hd1 S) where
  stable := fun env env' sp H hk => by simp only [hd1]; rw [h.stable env env' sp H hk]
  run := fun s env H v H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [hd1, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨vs, H1⟩, hS, e⟩ := hS
    obtain ⟨s', env', r, I, z, p31, hl, vm, e8, F, ag, hR, hA, mm⟩ := h.run s env H vs H1 I0 z0 F0 O0 R0 L0 A0 hS
    match vs, hl, e with
    | [x], _, e =>
      simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨s', env', r, I, z, by rw [p31], by simpa using vm 0 (by omega), e8, F, ag, hR, hA, mm⟩

theorem EVHwS.mono {KL : LayW} {C : List J} {pc len p nl hb E0 w : Nat} {Inv : St → Prop} {R W R' W' : Nat → Prop}
    {S : SemW} (h : EVHwS KL C pc len p nl Inv hb E0 R W w S) (hR : ∀ k, R k → R' k) (hW : ∀ k, W k → W' k) :
    EVHwS KL C pc len p nl Inv hb E0 R' W' w S where
  stable := fun env env' sp H hk => h.stable env env' sp H (fun k q => hk k (hR k q))
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    obtain ⟨s', env', r, I, z, p31, l, v, e8, F, ag, hRl, hA, mm⟩ := h.run s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS
    exact ⟨s', env', r, I, z, p31, l, v, e8, F, fun k hk => ag k (fun q => hk (hW k q)), hRl, hA,
      fun a ha hw => mm a ha (fun k hk q => hw k hk (hW k q))⟩

theorem EVHwS.len {KL : LayW} {C : List J} {pc len len' p nl hb E0 w : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    {S : SemW} (h : EVHwS KL C pc len p nl Inv hb E0 R W w S) (e : len = len') :
    EVHwS KL C pc len' p nl Inv hb E0 R W w S := e ▸ h

theorem EVHwS.wid {KL : LayW} {C : List J} {pc len p nl hb E0 w w' : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    {S : SemW} (h : EVHwS KL C pc len p nl Inv hb E0 R W w S) (e : w = w') :
    EVHwS KL C pc len p nl Inv hb E0 R W w' S := e ▸ h

theorem nilXS {KL : LayW} {C : List J} {pc p nl hb E0 : Nat} {Inv : St → Prop} :
    EVHwS KL C pc 0 p nl Inv hb E0 (fun _ => False) (fun _ => False) 0 nilS where
  stable := fun _ _ _ _ _ => rfl
  run := fun s env H vs H' I0 z0 F0 _ R0 _ A0 hS => by
    simp only [nilS, Option.some.injEq, Prod.mk.injEq] at hS; obtain ⟨rfl, rfl⟩ := hS
    exact ⟨s, env, by simpa using SStarX.refl (K := KL) (C := C) (pc, s), I0, z0, by omega, rfl,
      fun i hi => absurd hi (by omega), rfl, F0, fun _ _ => rfl, R0, A0, fun _ _ _ => rfl⟩

theorem pairXS {KL : LayW} {C : List J} {pc la lb p nl hb E0 wa wb : Nat} {Inv : St → Prop}
    {RA WA RB WB : Nat → Prop} {SA SB : SemW}
    (hA : EVHwS KL C pc la p nl Inv hb E0 RA WA wa SA) (hB : EVHwS KL C (pc + la) lb p nl Inv hb E0 RB WB wb SB)
    (sB : ∀ k, RB k → ¬ WA k) :
    EVHwS KL C pc (la + lb) p nl Inv hb E0 (fun k => RA k ∨ RB k) (fun k => WA k ∨ WB k) (wa + wb)
      (pairS wa SA SB) where
  stable := fun env env' sp H h => by
    simp only [pairS]
    rw [hA.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SA env' sp H with
    | none => rfl
    | some r1 => simp only [Option.bind_some]; rw [hB.stable env env' _ r1.2 (fun k hk => h k (Or.inr hk))]
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    obtain ⟨o1, o2, o3⟩ := O0
    simp only [pairS, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨⟨a, H1⟩, hSA, ⟨b, H2⟩, hSB, rfl, rfl⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, la1, v1, e81, F1, ag1, R1, A1, m1⟩ :=
      hA.run s env H a H1 I0 z0 F0 ⟨o1, o2, o3⟩ R0 L0 A0 hSA
    have hs1 := hrel_sp R1
    have hSB1 : SB env1 (s1.x 31).toNat H1 = some (b, H2) := by
      rw [p1, hB.stable env1 env _ _ (fun k hk => ag1 k (sB k hk))]; exact hSB
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.2.2.1; omega)
    obtain ⟨s2, env2, r2, I2, z2, p2, lb2, v2, e82, F2, ag2, R2, A2, m2⟩ :=
      hB.run s1 env1 H1 b H2 I1 z1 F1 ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩ R1 L1 A1 hSB1
    rw [p1] at p2 v2 m2; rw [e81] at m2
    refine ⟨s2, env2, by rw [← Nat.add_assoc]; exact r1.trans r2, I2, z2, by rw [p2]; omega, by simp [la1, lb2],
      ?_, by rw [e82, e81], F2, ?_, R2, A2, ?_⟩
    · intro i hi
      by_cases hi' : i < wa
      · rw [m2 _ (by omega) (fun k hk _ => by
          have := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk; omega), v1 i hi']
        rw [getD_app_l _ _ _ (by rw [la1]; exact hi')]
      · have := v2 (i - wa) (by omega)
        rw [show (s.x 31).toNat - 8 * wa - 8 * (i - wa + 1) = (s.x 31).toNat - 8 * (i + 1) by omega] at this
        rw [this, getD_app_r _ _ _ (by rw [la1]; omega), la1]
    · intro k hk; simp only [not_or] at hk; rw [ag2 k hk.2, ag1 k hk.1]
    · intro a ha hw
      rw [m2 a (by omega) (fun k hk wk => hw k hk (Or.inr wk)), m1 a ha (fun k hk wk => hw k hk (Or.inl wk))]

theorem localXS {KL : LayW} {C : List J} {p nl hb E0 : Nat} {Inv : St → Prop}
    (hI : InvOKH hb p Inv) (hp : p < 2 ^ 20) (hnl : nl < 251) :
    ∀ w k pc, k + w ≤ nl → At C pc (localT 1 p k pc w) →
      EVHwS KL C pc (5 * w) p nl Inv hb E0 (fun j => k ≤ j ∧ j < k + w) (fun _ => False) w (localS k w)
  | 0, k, pc, _, _ => (nilXS (KL := KL) (C := C) (pc := pc) (p := p) (nl := nl) (hb := hb) (E0 := E0)
      (Inv := Inv)).mono (fun _ h => h.elim) (fun _ h => h)
  | w + 1, k, pc, hk, hC => by
    rw [localT_succ] at hC
    have h1 := local1XS (KL := KL) (nl := nl) (k := k) (W := fun _ => False) (E0 := E0) hI hp hnl (by omega) hC.left
    have h2 := localXS (KL := KL) (nl := nl) (E0 := E0) hI hp hnl w (k + 1) (pc + 5) (by omega) (by simpa using hC.right)
    exact ((pairXS h1 h2 (fun _ _ h => h)).mono (R' := fun j => k ≤ j ∧ j < k + (w + 1)) (W' := fun _ => False)
      (fun j q => by rcases q with e | ⟨e1, e2⟩ <;> constructor <;> omega)
      (fun j q => by rcases q with e | e <;> exact e)).len (len' := 5 * (w + 1)) (by omega) |>.wid (by omega)

end Templates
