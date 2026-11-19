/- Safe retrofit (EVS) P3: tail mode (EVXT) as `EVHtS` (Opus box E). -/
import Nano.V2Self.Proof.Machine.EVSFin
namespace Templates
open CallProbe SimW SafeRun

theorem valTS {KL : LayW} {C : List J} {pc lc p nl hb E0 w X Hd : Nat} {Inv : St → Prop} {R W : Nat → Prop} {S : SemW}
    (h : EVHwS KL C pc lc p nl Inv hb E0 R W w S) (hJ : C[pc + lc]? = some (.jal 0 ((X : Int) - ((pc + lc : Nat) : Int))))
    (hX : X < C.length) (hpc : pc + lc < C.length) (hC18 : C.length < 2 ^ 18) :
    EVHtS KL C pc p nl Inv hb E0 R W w X Hd (exitS S) where
  stable := fun env env' sp H hk => by simp only [exitS]; rw [h.stable env env' sp H hk]
  cont := fun s env H st H' _ _ _ _ _ _ _ hS => by
    simp only [exitS, Option.map_eq_some_iff] at hS
    obtain ⟨_, _, e⟩ := hS; simp at e
  exit := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [exitS, Option.map_eq_some_iff] at hS
    obtain ⟨⟨u, H1⟩, hS, e⟩ := hS
    simp only [Prod.mk.injEq, Sum.inl.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    obtain ⟨s', env', r, I, z, p31, l, v, e8, F, ag, hR, hA, mm⟩ := h.run s env H u H1 I0 z0 F0 O0 R0 L0 A0 hS
    have sj : step C (pc + lc, s') = some (X, wr s' 0 (UInt64.ofNat (s'.b + 4 * (pc + lc + 1)))) := by
      simp [step, hJ]; omega
    have w0 : wr s' 0 (UInt64.ofNat (s'.b + 4 * (pc + lc + 1))) = s' := by simp [wr]
    rw [w0] at sj
    have sx : SafeX KL C (pc + lc, s') := by simp only [SafeX, hJ]; simp; omega
    exact ⟨s', env', r.trans (.head sx sj (.refl _)), I, z, p31, l, v, e8, F, ag, hR, hA, mm⟩

theorem contTS {KL : LayW} {C : List J} {pc le p nl hb E0 w X Hd : Nat} {Inv : St → Prop} {R W : Nat → Prop} {S : SemW}
    (hI : InvOKH hb p Inv)
    (he : EVHwS KL C pc le p nl Inv hb E0 R W (p - 1) S) (hS : At C (pc + le) (popN p 1 (p - 1)))
    (hJ : C[pc + le + 3 * (p - 1)]? = some (.jal 0 ((Hd : Int) - ((pc + le + 3 * (p - 1) : Nat) : Int))))
    (hp : 1 ≤ p) (hpn : p ≤ nl) (hnl : nl < 251) (hHd : Hd < C.length) (hpc : pc + le + 3 * (p - 1) < C.length)
    (hC18 : C.length < 2 ^ 18) :
    EVHtS KL C pc p nl Inv hb E0 R W w X Hd (contS S) where
  stable := fun env env' sp H hk => by simp only [contS]; rw [he.stable env env' sp H hk]
  exit := fun s env H st H' _ _ _ _ _ _ _ hS => by
    simp only [contS, Option.map_eq_some_iff] at hS
    obtain ⟨_, _, e⟩ := hS; simp at e
  cont := fun s env H st H' I0 z0 F0 O0 R0 L0 A0 hS' => by
    simp only [contS, Option.map_eq_some_iff] at hS'
    obtain ⟨⟨u, H1⟩, hSV, e⟩ := hS'
    simp only [Prod.mk.injEq, Sum.inr.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    obtain ⟨s1, env1, r1, I1, z1, p1, lu, v1, e81, F1, ag1, R1, A1, m1⟩ := he.run s env H u H1 I0 z0 F0 O0 R0 L0 A0 hSV
    obtain ⟨o1, o2, o3⟩ := O0
    have lt64 := (s.x 31).toNat_lt
    have sp1 := hrel_sp R1
    have T1 : (s1.x 31).toNat + 8 * (p - 1) = (s.x 31).toNat := by rw [p1]; have := R1.2.2.1; omega
    obtain ⟨s2, r2, p2, e82, ex2, eb2, ms2, mo2⟩ := popN_run (p := p) (k0 := 1) (p - 1) (pc + le) s1 hS (by omega)
      (fun j j' hj hj' e => by have := slotAddr_inj (nl := nl) (by rw [e81]; omega) (by omega) (by omega) e; omega)
      (fun j i hj hi => by
        rw [e81]; have := slotAddr_ge (T := (s.x 31).toNat) (k := 1 + j) (nl := nl) (by omega) o2 (by omega); omega)
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    have ss2 : SStarX KL C (pc + le, s1) (pc + le + 3 * (p - 1), s2) := SStarX.of (popN_srun (p - 1) (pc + le) s1 hS
      (by omega)
      (fun j hj => by
        have hk : 1 + j < nl := by omega
        obtain ⟨g1, g2, g3, g4⟩ := slotT_wok (k := 1 + j) L1 ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩
          (by have := R1.2.1; have := R1.2.2.1; omega) hk hnl
        refine ⟨L1.wok (by have := R1.2.1; have := R1.2.2.1; omega) (by have := L0.top; omega)
          (by have := L1.a31; omega), g1, g2, g3, g4⟩)
      _ r2)
    rw [e81] at ms2 mo2
    have x31 : (s2.x 31).toNat = (s.x 31).toNat := by rw [p2, T1]
    have x8 : s2.x 8 = s.x 8 := by rw [e82, e81]
    have x30 : s2.x 30 = s1.x 30 := ex2 30 (by decide) (by decide)
    have F2 : Frame p nl s2 (setW env1 1 (p - 1) u) := by
      intro k hk
      show s2.m (slotAddr p (s2.x 8).toNat k) = setW env1 1 (p - 1) u k
      rw [x8]
      by_cases e : 1 ≤ k ∧ k < 1 + (p - 1)
      · have := ms2 (k - 1) (by omega)
        rw [show 1 + (k - 1) = k by omega] at this
        rw [this, show (s1.x 31).toNat + 8 * (p - 1 - 1 - (k - 1)) = (s.x 31).toNat - 8 * (k - 1 + 1) by omega,
          v1 (k - 1) (by omega)]
        simp [setW, e]
      · rw [mo2 _ (fun j hj h => e (by have := slotAddr_inj (nl := nl) (by omega) hk (by omega) h; omega))]
        simp only [setW, e, if_false]; rw [← e81]; exact F1 k hk
    have slot_hi : ∀ j, j < p - 1 → (s.x 31).toNat ≤ slotAddr p (s.x 8).toNat (1 + j) ∧
        slotAddr p (s.x 8).toNat (1 + j) < (s.x 8).toNat + 8 * p + 16 := fun j hj =>
      ⟨slotAddr_ge (T := (s.x 31).toNat) (k := 1 + j) (nl := nl) (by omega) o2 (by omega),
        slotAddr_lt (nl := nl) (by omega) (by omega)⟩
    have I2 : Inv s2 := by
      apply hI s1 s2 I1 (by rw [e82]) (ex2 28 (by decide) (by decide)) (ex2 29 (by decide) (by decide)) eb2
      intro a ha
      apply mo2 a; intro j hj e; apply ha; rw [e81, e]
      have hh := slot_hi j hj; have := R1.1; have := R1.2.1; have := R1.2.2.1
      exact ⟨by omega, hh.2⟩
    have z2 : s2.x 0 = 0 := by rw [ex2 0 (by decide) (by decide), z1]
    have R2 : HRel hb s2 H1 := HRel_stack R1 x30 (by rw [x31]; have := R1.2.2.1; omega) (fun a h1 h2 => by
      apply mo2 a; intro j hj e; have := slot_hi j hj; have := R1.2.2.1; omega)
    have sj : step C (pc + le + 3 * (p - 1), s2) = some (Hd, s2) := by
      simp [step, hJ, wr]; omega
    have sx : SafeX KL C (pc + le + 3 * (p - 1), s2) := by simp only [SafeX, hJ]; simp; omega
    refine ⟨s2, env1, (r1.trans ss2).trans (.head sx sj (.refl _)), I2, z2, x31, lu, x8, F2, ag1, R2, A1, ?_⟩
    intro a ha hW
    rw [mo2 a (fun j hj e => hW (1 + j) (by omega) (Or.inr ⟨by omega, by omega⟩) e)]
    exact m1 a ha (fun k hk wk => hW k hk (Or.inl wk))


theorem ifPreS {KL : LayW} {C : List J} {pc lp lt p nl hb E0 cmp : Nat} {Inv : St → Prop} {RP WP : Nat → Prop} {SP : SemW}
    (hI : InvOKH hb p Inv) (hP : EVHwS KL C pc lp p nl Inv hb E0 RP WP 2 SP) (hH : At C (pc + lp) (ifHeadG cmp lt))
    (s : St) (env : Env) (H : Hp) (a b : UInt64) (H1 : Hp) (I0 : Inv s) (z0 : s.x 0 = 0) (F0 : Frame p nl s env)
    (O0 : FrameOK p nl s) (R0 : HRel hb s H) (L0 : Lay KL hb E0 p s) (A0 : HAl H)
    (hSP : SP env (s.x 31).toNat H = some ([a, b], H1)) (hCl : pc + lp + 6 + lt < C.length) (hC18 : C.length < 2 ^ 18) :
    ∃ s2 env1, SStarX KL C (pc, s) (if cmpF cmp a b then pc + lp + 5 else pc + lp + 6 + lt, s2) ∧ Inv s2 ∧ s2.x 0 = 0 ∧
      (s2.x 31).toNat = (s.x 31).toNat ∧ s2.x 8 = s.x 8 ∧ Frame p nl s2 env1 ∧ FrameOK p nl s2 ∧ HRel hb s2 H1 ∧
      Lay KL hb E0 p s2 ∧ HAl H1 ∧
      (∀ k, ¬ WP k → env1 k = env k) ∧
      ∀ a', (s.x 31).toNat ≤ a' → (∀ k, k < nl → WP k → a' ≠ slotAddr p (s.x 8).toNat k) → s2.m a' = s.m a' := by
  obtain ⟨o1, o2, o3⟩ := O0
  have lt64 := (s.x 31).toNat_lt
  obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, A1, m1⟩ := hP.run s env H _ H1 I0 z0 F0 ⟨o1, o2, o3⟩ R0 L0 A0 hSP
  have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
  have va : s1.m ((s.x 31).toNat - 8) = a := by simpa using v1 0 (by omega)
  have vb : s1.m ((s.x 31).toNat - 8 - 8) = b := by
    have := v1 1 (by omega); rw [show (s.x 31).toNat - 8 * (1 + 1) = (s.x 31).toNat - 8 - 8 by omega] at this
    simpa using this
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
  have L2 : Lay KL hb E0 p s2 := L0.post' x8 r1.star.b (by rw [x31])
  have sc := step_cmp (s := s2) c3
  rw [x5, x6] at sc
  by_cases hc : cmpF cmp a b
  · rw [if_pos hc] at sc ⊢
    exact ⟨s2, env1, st2.trans (.head safe3 sc (.refl _)), I2, z2, x31, x8, F2, O2, R2, L2, A1, ag1,
      fun a' h1 h2 => m1 a' h1 h2⟩
  · rw [if_neg hc] at sc ⊢
    have sj0 : step C (pc + lp + 4, s2) =
        some (pc + lp + 6 + lt, wr s2 0 (UInt64.ofNat (s2.b + 4 * (pc + lp + 4 + 1)))) := by
      simp [step, c4]; omega
    have w2 : wr s2 0 (UInt64.ofNat (s2.b + 4 * (pc + lp + 4 + 1))) = s2 := by simp [wr]
    rw [w2] at sj0
    have sj2 : SafeX KL C (pc + lp + 4, s2) := by simp only [SafeX, c4]; simp; omega
    exact ⟨s2, env1, st2.trans (.head safe3 sc (.head sj2 sj0 (.refl _))), I2, z2, x31, x8, F2, O2, R2, L2, A1, ag1,
      fun a' h1 h2 => m1 a' h1 h2⟩

theorem ifTS' {KL : LayW} {C : List J} {pc lp lt p nl hb E0 w cmp X Hd : Nat} {Inv : St → Prop} {RP WP RT WT RE WE : Nat → Prop}
    {SP : SemW} {ST SE : SemT} (hI : InvOKH hb p Inv)
    (hP : EVHwS KL C pc lp p nl Inv hb E0 RP WP 2 SP) (hH : At C (pc + lp) (ifHeadG cmp lt))
    (hT : EVHtS KL C (pc + lp + 5) p nl Inv hb E0 RT WT w X Hd ST)
    (hE : EVHtS KL C (pc + lp + 6 + lt) p nl Inv hb E0 RE WE w X Hd SE)
    (sT : ∀ k, RT k → ¬ WP k) (sE : ∀ k, RE k → ¬ WP k) (hCl : pc + lp + 6 + lt < C.length) (hC18 : C.length < 2 ^ 18) :
    EVHtS KL C pc p nl Inv hb E0 (fun k => RP k ∨ RT k ∨ RE k) (fun k => WP k ∨ WT k ∨ WE k) w X Hd (ifTS cmp SP ST SE) where
  stable := fun env env' sp H h => by
    simp only [ifTS]
    rw [hP.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SP env' sp H with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      rw [hT.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inl hk))),
        hE.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inr hk)))]
  exit := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [ifTS, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    have l1 := (hP.run s env H ab H1 I0 z0 F0 O0 R0 L0 A0 hSP).choose_spec.choose_spec.2.2.2.2.1
    match ab, l1, hS, hSP with
    | [a, b], _, hS, hSP =>
    dsimp only at hS
    obtain ⟨s2, env1, st2, I2, z2, x31, x8, F2, O2, R2, L2, A1, ag1, mm⟩ :=
      ifPreS hI hP hH s env H a b H1 I0 z0 F0 O0 R0 L0 A0 hSP hCl hC18
    by_cases hc : cmpF cmp a b
    · rw [if_pos hc] at hS st2
      have h2 : ST env1 (s2.x 31).toNat H1 = some (.inl vs, H') := by
        rw [x31, hT.stable env1 env _ _ (fun k hk => ag1 k (sT k hk))]; exact hS
      obtain ⟨s4, env4, r4, I4, z4, p4, l4, v4, e84, F4, ag4, R4, A4, m4⟩ := hT.exit s2 env1 H1 vs H' I2 z2 F2 O2 R2 L2 A1 h2
      refine ⟨s4, env4, st2.trans r4, I4, z4, by rw [p4, x31], l4, ?_, by rw [e84, x8], F4, ?_, R4, A4, ?_⟩
      · intro i hi; rw [x31] at v4; exact v4 i hi
      · intro k hk; simp only [not_or] at hk; rw [ag4 k hk.2.1, ag1 k hk.1]
      · intro a' ha hW
        rw [m4 a' (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inl wk))),
          mm a' ha (fun k hk wk => hW k hk (Or.inl wk))]
    · rw [if_neg hc] at hS st2
      have h2 : SE env1 (s2.x 31).toNat H1 = some (.inl vs, H') := by
        rw [x31, hE.stable env1 env _ _ (fun k hk => ag1 k (sE k hk))]; exact hS
      obtain ⟨s4, env4, r4, I4, z4, p4, l4, v4, e84, F4, ag4, R4, A4, m4⟩ := hE.exit s2 env1 H1 vs H' I2 z2 F2 O2 R2 L2 A1 h2
      refine ⟨s4, env4, st2.trans r4, I4, z4, by rw [p4, x31], l4, ?_, by rw [e84, x8], F4, ?_, R4, A4, ?_⟩
      · intro i hi; rw [x31] at v4; exact v4 i hi
      · intro k hk; simp only [not_or] at hk; rw [ag4 k hk.2.2, ag1 k hk.1]
      · intro a' ha hW
        rw [m4 a' (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inr wk))),
          mm a' ha (fun k hk wk => hW k hk (Or.inl wk))]
  cont := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [ifTS, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨ab, H1⟩, hSP, hS⟩ := hS
    have l1 := (hP.run s env H ab H1 I0 z0 F0 O0 R0 L0 A0 hSP).choose_spec.choose_spec.2.2.2.2.1
    match ab, l1, hS, hSP with
    | [a, b], _, hS, hSP =>
    dsimp only at hS
    obtain ⟨s2, env1, st2, I2, z2, x31, x8, F2, O2, R2, L2, A1, ag1, mm⟩ :=
      ifPreS hI hP hH s env H a b H1 I0 z0 F0 O0 R0 L0 A0 hSP hCl hC18
    by_cases hc : cmpF cmp a b
    · rw [if_pos hc] at hS st2
      have h2 : ST env1 (s2.x 31).toNat H1 = some (.inr vs, H') := by
        rw [x31, hT.stable env1 env _ _ (fun k hk => ag1 k (sT k hk))]; exact hS
      obtain ⟨s4, env4, r4, I4, z4, p4, l4, e84, F4, ag4, R4, A4, m4⟩ := hT.cont s2 env1 H1 vs H' I2 z2 F2 O2 R2 L2 A1 h2
      refine ⟨s4, env4, st2.trans r4, I4, z4, by rw [p4, x31], l4, by rw [e84, x8], F4, ?_, R4, A4, ?_⟩
      · intro k hk; simp only [not_or] at hk; rw [ag4 k hk.2.1, ag1 k hk.1]
      · intro a' ha hW
        rw [m4 a' (by rw [x31]; exact ha) (fun k hk wk => by
            rw [x8]; exact hW k hk (wk.elim (fun h => Or.inl (Or.inr (Or.inl h))) Or.inr)),
          mm a' ha (fun k hk wk => hW k hk (Or.inl (Or.inl wk)))]
    · rw [if_neg hc] at hS st2
      have h2 : SE env1 (s2.x 31).toNat H1 = some (.inr vs, H') := by
        rw [x31, hE.stable env1 env _ _ (fun k hk => ag1 k (sE k hk))]; exact hS
      obtain ⟨s4, env4, r4, I4, z4, p4, l4, e84, F4, ag4, R4, A4, m4⟩ := hE.cont s2 env1 H1 vs H' I2 z2 F2 O2 R2 L2 A1 h2
      refine ⟨s4, env4, st2.trans r4, I4, z4, by rw [p4, x31], l4, by rw [e84, x8], F4, ?_, R4, A4, ?_⟩
      · intro k hk; simp only [not_or] at hk; rw [ag4 k hk.2.2, ag1 k hk.1]
      · intro a' ha hW
        rw [m4 a' (by rw [x31]; exact ha) (fun k hk wk => by
            rw [x8]; exact hW k hk (wk.elim (fun h => Or.inl (Or.inr (Or.inr h))) Or.inr)),
          mm a' ha (fun k hk wk => hW k hk (Or.inl (Or.inl wk)))]


theorem letPreS {KL : LayW} {C : List J} {pc lv p nl hb E0 k0 w : Nat} {Inv : St → Prop} {Rv Wv : Nat → Prop} {SV : SemW}
    (hI : InvOKH hb p Inv) (hv : EVHwS KL C pc lv p nl Inv hb E0 Rv Wv w SV) (hS : At C (pc + lv) (popN p k0 w))
    (hk0 : k0 + w ≤ nl) (hnl : nl < 251)
    (s : St) (env : Env) (H : Hp) (u : List UInt64) (H1 : Hp) (I0 : Inv s) (z0 : s.x 0 = 0) (F0 : Frame p nl s env)
    (O0 : FrameOK p nl s) (R0 : HRel hb s H) (L0 : Lay KL hb E0 p s) (A0 : HAl H)
    (hSV : SV env (s.x 31).toNat H = some (u, H1)) :
    ∃ s2 env1, SStarX KL C (pc, s) (pc + lv + 3 * w, s2) ∧ Inv s2 ∧ s2.x 0 = 0 ∧
      (s2.x 31).toNat = (s.x 31).toNat ∧ s2.x 8 = s.x 8 ∧ Frame p nl s2 (setW env1 k0 w u) ∧ FrameOK p nl s2 ∧
      HRel hb s2 H1 ∧ Lay KL hb E0 p s2 ∧ HAl H1 ∧ (∀ k, ¬ Wv k → env1 k = env k) ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → (Wv k ∨ (k0 ≤ k ∧ k < k0 + w)) → a ≠ slotAddr p (s.x 8).toNat k) →
        s2.m a = s.m a := by
  obtain ⟨s1, env1, r1, I1, z1, p1, lu, v1, e81, F1, ag1, R1, A1, m1⟩ := hv.run s env H u H1 I0 z0 F0 O0 R0 L0 A0 hSV
  obtain ⟨o1, o2, o3⟩ := O0
  have lt64 := (s.x 31).toNat_lt
  have sp1 := hrel_sp R1
  have T1 : (s1.x 31).toNat + 8 * w = (s.x 31).toNat := by rw [p1]; have := R1.2.2.1; omega
  obtain ⟨s2, r2, p2, e82, ex2, eb2, ms2, mo2⟩ := popN_run (p := p) (k0 := k0) w (pc + lv) s1 hS (by omega)
    (fun j j' hj hj' e => by have := slotAddr_inj (nl := nl) (by rw [e81]; omega) (by omega) (by omega) e; omega)
    (fun j i hj hi => by
      rw [e81]; have := slotAddr_ge (T := (s.x 31).toNat) (k := k0 + j) (by omega) o2 (by omega); omega)
  have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
  have ss2 : SStarX KL C (pc + lv, s1) (pc + lv + 3 * w, s2) := SStarX.of (popN_srun w (pc + lv) s1 hS (by omega)
    (fun j hj => by
      have hk : k0 + j < nl := by omega
      obtain ⟨g1, g2, g3, g4⟩ := slotT_wok (k := k0 + j) L1 ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩
        (by have := R1.2.1; have := R1.2.2.1; omega) hk hnl
      refine ⟨L1.wok (by have := R1.2.1; have := R1.2.2.1; omega) (by have := L0.top; omega)
        (by have := L1.a31; omega), g1, g2, g3, g4⟩)
    _ r2)
  rw [e81] at ms2 mo2
  have x31 : (s2.x 31).toNat = (s.x 31).toNat := by rw [p2, T1]
  have x8 : s2.x 8 = s.x 8 := by rw [e82, e81]
  have x30 : s2.x 30 = s1.x 30 := ex2 30 (by decide) (by decide)
  have F2 : Frame p nl s2 (setW env1 k0 w u) := by
    intro k hk
    show s2.m (slotAddr p (s2.x 8).toNat k) = setW env1 k0 w u k
    rw [x8]
    by_cases e : k0 ≤ k ∧ k < k0 + w
    · have := ms2 (k - k0) (by omega)
      rw [show k0 + (k - k0) = k by omega] at this
      rw [this, show (s1.x 31).toNat + 8 * (w - 1 - (k - k0)) = (s.x 31).toNat - 8 * (k - k0 + 1) by omega,
        v1 (k - k0) (by omega)]
      simp [setW, e]
    · rw [mo2 _ (fun j hj h => e (by have := slotAddr_inj (nl := nl) (by omega) hk (by omega) h; omega))]
      simp only [setW, e, if_false]; rw [← e81]; exact F1 k hk
  have slot_hi : ∀ j, j < w → (s.x 31).toNat ≤ slotAddr p (s.x 8).toNat (k0 + j) ∧
      slotAddr p (s.x 8).toNat (k0 + j) < (s.x 8).toNat + 8 * p + 16 := fun j hj =>
    ⟨slotAddr_ge (T := (s.x 31).toNat) (k := k0 + j) (by omega) o2 (by omega), slotAddr_lt (nl := nl) (by omega) (by omega)⟩
  have I2 : Inv s2 := by
    apply hI s1 s2 I1 (by rw [e82]) (ex2 28 (by decide) (by decide)) (ex2 29 (by decide) (by decide)) eb2
    intro a ha
    apply mo2 a; intro j hj e; apply ha; rw [e81, e]
    have hh := slot_hi j hj; have := R1.1; have := R1.2.1; have := R1.2.2.1
    exact ⟨by omega, hh.2⟩
  have z2 : s2.x 0 = 0 := by rw [ex2 0 (by decide) (by decide), z1]
  have R2 : HRel hb s2 H1 := HRel_stack R1 x30 (by rw [x31]; have := R1.2.2.1; omega) (fun a h1 h2 => by
    apply mo2 a; intro j hj e; have := slot_hi j hj; have := R1.2.2.1; omega)
  refine ⟨s2, env1, r1.trans ss2, I2, z2, x31, x8, F2, ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩, R2,
    L0.post' x8 (by rw [eb2, r1.star.b]) x31, A1, ag1, ?_⟩
  intro a ha hW
  rw [mo2 a (fun j hj e => hW (k0 + j) (by omega) (Or.inr ⟨by omega, by omega⟩) e)]
  exact m1 a ha (fun k hk wk => hW k hk (Or.inl wk))

/-- **CT.lett**: value; pop; body (tail) -/
theorem letTS' {KL : LayW} {C : List J} {pc lv p nl hb E0 k0 w wb X Hd : Nat} {Inv : St → Prop} {Rv Wv Rb Wb : Nat → Prop}
    {SV : SemW} {SB : SemT} (hI : InvOKH hb p Inv)
    (hv : EVHwS KL C pc lv p nl Inv hb E0 Rv Wv w SV) (hS : At C (pc + lv) (popN p k0 w))
    (hb' : EVHtS KL C (pc + lv + 3 * w) p nl Inv hb E0 Rb Wb wb X Hd SB)
    (hk0 : k0 + w ≤ nl) (hsc : ∀ k, Rb k → ¬ (k0 ≤ k ∧ k < k0 + w) → ¬ Wv k) (hnl : nl < 251) :
    EVHtS KL C pc p nl Inv hb E0 (fun k => Rv k ∨ (Rb k ∧ ¬ (k0 ≤ k ∧ k < k0 + w)))
      (fun k => Wv k ∨ (k0 ≤ k ∧ k < k0 + w) ∨ Wb k) wb X Hd (letTS k0 w SV SB) where
  stable := fun env env' sp H h => by
    simp only [letTS]
    rw [hv.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SV env' sp H with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      apply hb'.stable; intro k hk
      unfold setW
      split
      · rfl
      · rename_i hk'; exact h k (Or.inr ⟨hk, hk'⟩)
  exit := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS' => by
    simp only [letTS, Option.bind_eq_some_iff] at hS'
    obtain ⟨⟨u, H1⟩, hSV, hSB⟩ := hS'
    obtain ⟨s2, env1, r2, I2, z2, x31, x8, F2, O2, R2, L2, A2, ag1, mm⟩ :=
      letPreS hI hv hS hk0 hnl s env H u H1 I0 z0 F0 O0 R0 L0 A0 hSV
    have h2 : SB (setW env1 k0 w u) (s2.x 31).toNat H1 = some (.inl vs, H') := by
      rw [x31, ← hSB]; exact hb'.stable _ _ _ _ (setW_agree ag1 hsc)
    obtain ⟨s3, env3, r3, I3, z3, p3, l3, v3, e83, F3, ag3, R3, A3, m3⟩ := hb'.exit s2 _ H1 vs H' I2 z2 F2 O2 R2 L2 A2 h2
    refine ⟨s3, env3, r2.trans r3, I3, z3, by rw [p3, x31], l3, ?_, by rw [e83, x8], F3, ?_, R3, A3, ?_⟩
    · intro i hi; rw [x31] at v3; exact v3 i hi
    · intro k hk; simp only [not_or] at hk
      rw [ag3 k hk.2.2]; simp only [setW, hk.2.1, if_false]; exact ag1 k hk.1
    · intro a ha hW
      rw [m3 a (by rw [x31]; exact ha) (fun k hk wk => by rw [x8]; exact hW k hk (Or.inr (Or.inr wk)))]
      exact mm a ha (fun k hk wk => hW k hk (wk.elim Or.inl (fun h => Or.inr (Or.inl h))))
  cont := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS' => by
    simp only [letTS, Option.bind_eq_some_iff] at hS'
    obtain ⟨⟨u, H1⟩, hSV, hSB⟩ := hS'
    obtain ⟨s2, env1, r2, I2, z2, x31, x8, F2, O2, R2, L2, A2, ag1, mm⟩ :=
      letPreS hI hv hS hk0 hnl s env H u H1 I0 z0 F0 O0 R0 L0 A0 hSV
    have h2 : SB (setW env1 k0 w u) (s2.x 31).toNat H1 = some (.inr vs, H') := by
      rw [x31, ← hSB]; exact hb'.stable _ _ _ _ (setW_agree ag1 hsc)
    obtain ⟨s3, env3, r3, I3, z3, p3, l3, e83, F3, ag3, R3, A3, m3⟩ := hb'.cont s2 _ H1 vs H' I2 z2 F2 O2 R2 L2 A2 h2
    refine ⟨s3, env3, r2.trans r3, I3, z3, by rw [p3, x31], l3, by rw [e83, x8], F3, ?_, R3, A3, ?_⟩
    · intro k hk; simp only [not_or] at hk
      rw [ag3 k hk.2.2]; simp only [setW, hk.2.1, if_false]; exact ag1 k hk.1
    · intro a ha hW
      rw [m3 a (by rw [x31]; exact ha) (fun k hk wk => by
        rw [x8]; exact hW k hk (wk.elim (fun h => Or.inl (Or.inr (Or.inr h))) Or.inr))]
      exact mm a ha (fun k hk wk => hW k hk (Or.inl (wk.elim Or.inl (fun h => Or.inr (Or.inl h)))))

end Templates
