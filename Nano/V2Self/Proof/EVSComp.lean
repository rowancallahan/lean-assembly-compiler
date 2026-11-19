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

/-- a deterministic run whose every intermediate state is SafeX -/
theorem sstarX_of_run {KL : LayW} {C : List J} : ∀ {k : Nat} {a b : Nat × St}, run C k a = some b →
    (∀ j, j < k → ∀ c, run C j a = some c → SafeX KL C c) → SStarX KL C a b
  | 0, a, b, h, _ => by simp [run] at h; subst h; exact .refl _
  | k + 1, a, b, h, hs => by
    simp only [run] at h
    cases e : step C a with
    | none => simp [e] at h
    | some c =>
      simp [e] at h
      refine .head (hs 0 (by omega) a rfl) e (sstarX_of_run h fun j hj d hd => hs (j + 1) (by omega) d ?_)
      simp [run, e, hd]

theorem ifXS {KL : LayW} {C : List J} {pc lp lt le p nl hb E0 w cmp : Nat} {Inv : St → Prop} {RP WP RT WT RE WE : Nat → Prop}
    {SP ST SE : SemW} (hI : InvOKH hb p Inv)
    (hP : EVHwS KL C pc lp p nl Inv hb E0 RP WP 2 SP) (hH : At C (pc + lp) (ifHeadG cmp lt))
    (hT : EVHwS KL C (pc + lp + 5) lt p nl Inv hb E0 RT WT w ST)
    (hJ : C[pc + lp + 5 + lt]? = some (.jal 0 ((le : Int) + 1)))
    (hE : EVHwS KL C (pc + lp + 6 + lt) le p nl Inv hb E0 RE WE w SE)
    (sT : ∀ k, RT k → ¬ WP k) (sE : ∀ k, RE k → ¬ WP k) (hCl : pc + (lp + 6 + lt + le) < C.length)
    (hC18 : C.length < 2 ^ 18) :
    EVHwS KL C pc (lp + 6 + lt + le) p nl Inv hb E0 (fun k => RP k ∨ RT k ∨ RE k) (fun k => WP k ∨ WT k ∨ WE k) w
      (ifS cmp SP ST SE) where
  stable := fun env env' sp H h => by
    simp only [ifS]
    rw [hP.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SP env' sp H with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      rw [hT.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inl hk))),
        hE.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inr hk)))]
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    obtain ⟨o1, o2, o3⟩ := O0
    have lt64 := (s.x 31).toNat_lt
    simp only [ifS, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, A1, m1⟩ := hP.run s env H ab H1 I0 z0 F0 ⟨o1, o2, o3⟩ R0 L0 A0 hSP
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    match ab, l1, hS, v1 with
    | [a, b], _, hS, v1 =>
    have va : s1.m ((s.x 31).toNat - 8) = a := by simpa using v1 0 (by omega)
    have vb : s1.m ((s.x 31).toNat - 8 - 8) = b := by
      have := v1 1 (by omega); rw [show (s.x 31).toNat - 8 * (1 + 1) = (s.x 31).toNat - 8 - 8 by omega] at this
      simpa using this
    dsimp only at hS
    have c0 := hH.at 0 (by simp [ifHeadG]); have c1 := hH.at 1 (by simp [ifHeadG])
    have c2 := hH.at 2 (by simp [ifHeadG]); have c3 := hH.at 3 (by simp [ifHeadG])
    have c4 := hH.at 4 (by simp [ifHeadG])
    simp only [ifHeadG, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 c3 c4
    have sp1 := hrel_sp R1
    have ea0 : ea (s1.x 31) 0 = (s.x 31).toNat - 8 - 8 := by simp [ea, p1]; omega
    have ea8 : ea (s1.x 31) 8 = (s.x 31).toNat - 8 := by simp [ea, p1]; omega
    have ea16 : ea (s1.x 31) 16 = (s.x 31).toNat := by simp [ea, p1]; omega
    let s2 : St := ⟨upd (upd (upd s1.x 6 b) 5 a) 31 (UInt64.ofNat (s.x 31).toNat), s1.m, s1.b⟩
    have r2 : run C 3 (pc + lp, s1) = some (pc + lp + 3, s2) := by
      simp [run, step, c0, c1, c2, wr, ea0, ea8, va, vb, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
        upd_other _ _ (show (31:Nat) ≠ 5 by decide), ea16, s2]
    have x31 : (s2.x 31).toNat = (s.x 31).toNat := by simp [s2, upd]
    have x8 : s2.x 8 = s.x 8 := by simp [s2, upd, e81]
    have x30 : s2.x 30 = s1.x 30 := by simp [s2, upd]
    have x5 : s2.x 5 = a := by simp [s2, upd]
    have x6 : s2.x 6 = b := by simp [s2, upd]
    have z2 : s2.x 0 = 0 := by simp [s2, upd, z1]
    have I2 : Inv s2 := hI s1 s2 I1 (by simp [s2, upd]) (by simp [s2, upd]) (by simp [s2, upd]) rfl (fun _ _ => rfl)
    have F2 : Frame p nl s2 env1 := by
      intro k hk; show s1.m (slotAddr p (s2.x 8).toNat k) = env1 k; rw [x8, ← e81]; exact F1 k hk
    have O2 : FrameOK p nl s2 := ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩
    have R2 : HRel hb s2 H1 := HRel_stack R1 x30 (by rw [x31]; have := R1.2.2.1; omega) (fun _ _ _ => rfl)
    have w1a : wok KL ((s.x 31).toNat - 8 - 8) := L1.wok (by have := R1.2.1; have := R1.2.2.1; omega)
      (by have := L0.top; omega) (by have := L1.a31; omega)
    have w1b : wok KL ((s.x 31).toNat - 8) := L1.wok (by have := R1.2.1; have := R1.2.2.1; omega)
      (by have := L0.top; omega) (by have := L1.a31; omega)
    have st2 : SStarX KL C (pc, s) (pc + lp + 3, s2) := r1.trans (sstarX_of_run r2 (fun j hj c hc => by
      rcases j with _ | _ | _ | j
      · simp [run] at hc; subst hc; simp only [SafeX, c0]; rw [ea0]
        exact ⟨by decide, by decide, by decide, by decide, by omega, w1a⟩
      · simp [run, step, c0, wr, ea0] at hc; subst hc; simp only [SafeX, c1]
        refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
        · simp [upd]; omega
        · have : ea (upd s1.x 6 (s1.m ((s.x 31).toNat - 8 - 8)) 31) 8 = (s.x 31).toNat - 8 := by simpa [upd] using ea8
          simpa [this] using w1b
      · simp [run, step, c0, c1, wr, ea0, ea8, upd] at hc; subst hc; simp only [SafeX, c2]; simp [upd]; omega
      · omega))
    have safe3 : SafeX KL C (pc + lp + 3, s2) := by
      have hc3 := c3; unfold cmpJ at hc3; split at hc3 <;> (simp only [SafeX, hc3]; decide)
    have mm : ∀ a', (s.x 31).toNat ≤ a' → (∀ k, k < nl → WP k → a' ≠ slotAddr p (s.x 8).toNat k) → s2.m a' = s.m a' :=
      fun a' h1 h2 => m1 a' h1 h2
    have sc := step_cmp (s := s2) c3
    rw [x5, x6] at sc
    by_cases hc : cmpF cmp a b
    · rw [if_pos hc] at hS sc
      have hST : ST env1 (s2.x 31).toNat H1 = some (vs, H') := by
        rw [x31, hT.stable env1 env _ _ (fun k hk => ag1 k (sT k hk))]; exact hS
      have L2 : Lay KL hb E0 p s2 := L0.post' x8 r1.star.b (by rw [x31])
      obtain ⟨s4, env4, r4, I4, z4, p4, l4, v4, e84, F4, ag4, R4, A4, m4⟩ := hT.run s2 env1 H1 vs H' I2 z2 F2 O2 R2 L2 A1 hST
      have sj : step C (pc + lp + 5 + lt, s4) =
          some (pc + (lp + 6 + lt + le), wr s4 0 (UInt64.ofNat (s4.b + 4 * (pc + lp + 5 + lt + 1)))) := by
        simp [step, hJ]; omega
      have w4 : wr s4 0 (UInt64.ofNat (s4.b + 4 * (pc + lp + 5 + lt + 1))) = s4 := by simp [wr]
      rw [w4] at sj
      have sj4 : SafeX KL C (pc + lp + 5 + lt, s4) := by simp only [SafeX, hJ]; simp; omega
      refine ⟨s4, env4, st2.trans (.head safe3 sc (r4.trans (.head sj4 sj (.refl _)))), I4, z4, by rw [p4, x31], l4, ?_,
        by rw [e84, x8], F4, ?_, R4, A4, ?_⟩
      · intro i hi; rw [x31] at v4; exact v4 i hi
      · intro k hk; simp only [not_or] at hk; rw [ag4 k hk.2.1, ag1 k hk.1]
      · intro a' ha hW
        rw [m4 a' (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inl wk))),
          mm a' ha (fun k hk wk => hW k hk (Or.inl wk))]
    · rw [if_neg hc] at hS sc
      have hSE : SE env1 (s2.x 31).toNat H1 = some (vs, H') := by
        rw [x31, hE.stable env1 env _ _ (fun k hk => ag1 k (sE k hk))]; exact hS
      have sj0 : step C (pc + lp + 4, s2) =
          some (pc + lp + 6 + lt, wr s2 0 (UInt64.ofNat (s2.b + 4 * (pc + lp + 4 + 1)))) := by
        simp [step, c4]; omega
      have w2 : wr s2 0 (UInt64.ofNat (s2.b + 4 * (pc + lp + 4 + 1))) = s2 := by simp [wr]
      rw [w2] at sj0
      have L2 : Lay KL hb E0 p s2 := L0.post' x8 r1.star.b (by rw [x31])
      obtain ⟨s5, env5, r5, I5, z5, p5, l5, v5, e85, F5, ag5, R5, A5, m5⟩ := hE.run s2 env1 H1 vs H' I2 z2 F2 O2 R2 L2 A1 hSE
      have sj2 : SafeX KL C (pc + lp + 4, s2) := by simp only [SafeX, c4]; simp; omega
      refine ⟨s5, env5, ?_, I5, z5, by rw [p5, x31], l5, ?_, by rw [e85, x8], F5, ?_, R5, A5, ?_⟩
      · have : pc + lp + 6 + lt + le = pc + (lp + 6 + lt + le) := by omega
        rw [← this]; exact st2.trans (.head safe3 sc (.head sj2 sj0 r5))
      · intro i hi; rw [x31] at v5; exact v5 i hi
      · intro k hk; simp only [not_or] at hk; rw [ag5 k hk.2.2, ag1 k hk.1]
      · intro a' ha hW
        rw [m5 a' (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inr wk))),
          mm a' ha (fun k hk wk => hW k hk (Or.inl wk))]


end Templates
