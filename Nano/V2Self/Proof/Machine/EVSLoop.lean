/- Safe retrofit (EVS) P4: the LOOP node as `EVHwS` (Opus box E). -/
import Nano.V2Self.Proof.Machine.EVSTail
namespace Templates
open CallProbe SimW SafeRun

theorem loop_passS {KL : LayW} {C : List J} {h S len p nl hb E0 w : Nat} {Inv : St → Prop} {RZ WZ RS WS : Nat → Prop} {SZ SS : SemT}
    (hI : InvOKH hb p Inv)
    (hH : At C h (loopHead p ((S : Int) - ((h + 2 : Nat) : Int)))) (hD : At C S (loopDec p))
    (hZ : EVHtS KL C (h + 3) p nl Inv hb E0 RZ WZ w (h + len) h SZ)
    (hSt : EVHtS KL C (S + 2) p nl Inv hb E0 RS WS w (h + len) h SS)
    (hp : 1 ≤ p) (hpn : p ≤ nl) (hWp : ∀ k, (WZ k ∨ WS k) → p ≤ k) (hsc : ∀ k, (RZ k ∨ RS k) → ¬ (WZ k ∨ WS k))
    (hnl : nl < 251) (hSC : S + 2 ≤ C.length) (hhC : h + 3 ≤ C.length) (hC18 : C.length < 2 ^ 18) :
    ∀ n (env_s env_m : Env) (s : St) (H : Hp) (vs : List UInt64) (H' : Hp), Inv s → s.x 0 = 0 →
      Frame p nl s env_m → FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → HAl H →
      (∀ k, ¬ (WZ k ∨ WS k) → env_m k = env_s k) →
      loopGo p SZ SS (s.x 31).toNat n env_s H = some (vs, H') →
      ∃ s' env', SStarX KL C (h, s) (h + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
        vs.length = w ∧ (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
        Frame p nl s' env' ∧ (∀ k, ¬ (WZ k ∨ WS k ∨ k < p) → env' k = env_m k) ∧ HRel hb s' H' ∧ HAl H' ∧
        ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → (WZ k ∨ WS k ∨ k < p) → a ≠ slotAddr p (s.x 8).toNat k) →
          s'.m a = s.m a := by
  have c0 := hH.at 0 (by simp [loopHead]); have c1 := hH.at 1 (by simp [loopHead])
  have c2 := hH.at 2 (by simp [loopHead])
  have d0 := hD.at 0 (by simp [loopDec]); have d1 := hD.at 1 (by simp [loopDec])
  simp only [loopHead, loopDec, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 d0 d1
  have n0 : ¬ (WZ 0 ∨ WS 0) := fun h0 => by have := hWp 0 h0; omega
  -- facts about writing t0 (x5)
  have w5 : ∀ (s : St) (v : UInt64), Inv s → Inv (wr s 5 v) ∧ (wr s 5 v).x 0 = s.x 0 ∧ (wr s 5 v).x 8 = s.x 8 ∧
      (wr s 5 v).x 31 = s.x 31 ∧ (wr s 5 v).x 30 = s.x 30 ∧ (wr s 5 v).m = s.m ∧ (wr s 5 v).x 5 = v := by
    intro s v I
    have e : wr s 5 v = { s with x := upd s.x 5 v } := by simp [wr]
    rw [e]
    exact ⟨hI s _ I (by simp [upd]) (by simp [upd]) (by simp [upd]) rfl rfl (fun _ _ => rfl), by simp [upd], by simp [upd],
      by simp [upd], by simp [upd], rfl, by simp [upd]⟩
  have fuel : ∀ (s : St) (env : Env), Frame p nl s env → s.m (ea (s.x 8) (slotOff p 0)) = env 0 := by
    intro s env F; exact F 0 (by omega)
  have sx1 : ∀ (s : St) (H : Hp), FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → SafeX KL C (h, s) := by
    intro s H O R L
    obtain ⟨g1, g2, g3, g4⟩ := slotT_wok (k := 0) L O (by have := R.2.1; have := R.2.2.1; omega) (by omega) hnl
    simp only [SafeX, c0]
    exact ⟨by decide, by decide, g2, g3, g4, g1⟩
  have sx2 : ∀ (s : St), SafeX KL C (h + 1, s) := by intro s; simp only [SafeX, c1]; decide
  -- the zero arm
  have zc : ∀ (env_s env_m : Env) (s : St) (H : Hp) (vs : List UInt64) (H' : Hp), Inv s → s.x 0 = 0 →
      Frame p nl s env_m → FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → HAl H →
      (∀ k, ¬ (WZ k ∨ WS k) → env_m k = env_s k) →
      env_s 0 = 0 → (SZ env_s (s.x 31).toNat H).bind exitOnly = some (vs, H') →
      ∃ s' env', SStarX KL C (h, s) (h + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
        vs.length = w ∧ (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
        Frame p nl s' env' ∧ (∀ k, ¬ (WZ k ∨ WS k ∨ k < p) → env' k = env_m k) ∧ HRel hb s' H' ∧ HAl H' ∧
        ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → (WZ k ∨ WS k ∨ k < p) → a ≠ slotAddr p (s.x 8).toNat k) →
          s'.m a = s.m a := by
    intro env_s env_m s H vs H' I0 z0 F0 O0 R0 L0 A0 ag hz hS
    simp only [Option.bind_eq_some_iff] at hS
    obtain ⟨⟨r, H1⟩, hS, e⟩ := hS
    have e0 : env_m 0 = 0 := by rw [ag 0 n0, hz]
    obtain ⟨I1, z1, x81, x311, x301, m1, x51⟩ := w5 s (env_m 0) I0
    have st1 : step C (h, s) = some (h + 1, wr s 5 (env_m 0)) := by simp [step, c0, fuel s env_m F0]
    have x50 : (wr s 5 (env_m 0)).x 5 = (wr s 5 (env_m 0)).x 0 := by rw [x51, z1, z0, e0]
    have st2 : step C (h + 1, wr s 5 (env_m 0)) = some (h + 3, wr s 5 (env_m 0)) := by
      simp [step, c1, x50]; omega
    match r, e with
    | .inl u, e =>
    simp only [exitOnly, Option.some.injEq, Prod.mk.injEq] at e
    have e1 := e.1.symm; have e2 := e.2.symm; subst e1 e2
    have F1 : Frame p nl (wr s 5 (env_m 0)) env_m := by intro k hk; rw [m1, x81]; exact F0 k hk
    have O1 : FrameOK p nl (wr s 5 (env_m 0)) := by unfold FrameOK; rw [x81, x311]; exact O0
    have R1 : HRel hb (wr s 5 (env_m 0)) H := HRel_stack R0 x301 (by rw [x311]; exact R0.2.2.1) (fun a _ _ => by rw [m1])
    have hS' : SZ env_m ((wr s 5 (env_m 0)).x 31).toNat H = some (.inl vs, H') := by
      rw [x311, hZ.stable env_m env_s _ _ (fun k hk => ag k (hsc k (Or.inl hk)))]; exact hS
    have L1 : Lay KL hb E0 p (wr s 5 (env_m 0)) := L0.post' x81 (wr_b _ _ _) (by rw [x311])
    obtain ⟨s', env', r', I', z', p', l', v', e8', F', ag', R', A', m'⟩ :=
      hZ.exit _ env_m H vs H' I1 (by rw [z1, z0]) F1 O1 R1 L1 A0 hS'
    rw [x311] at p' v'; rw [x81] at e8'
    refine ⟨s', env', .head (sx1 s H O0 R0 L0) st1 (.head (sx2 _) st2 r'), I', z', p', l', v', e8', F', ?_, R', A', ?_⟩
    · intro k hk; simp only [not_or] at hk; exact ag' k hk.1
    · intro a ha hW
      rw [m' a (by rw [x311]; exact ha) (fun k hk wk => by rw [x81]; exact hW k hk (Or.inl wk)), m1]
  intro n
  induction n with
  | zero =>
    intro env_s env_m s H vs H' I0 z0 F0 O0 R0 L0 A0 ag hS
    by_cases hz : env_s 0 = 0
    · simp only [loopGo, hz, if_true] at hS
      exact zc env_s env_m s H vs H' I0 z0 F0 O0 R0 L0 A0 ag hz hS
    · simp [loopGo, hz] at hS
  | succ n ih =>
    intro env_s env_m s H vs H' I0 z0 F0 O0 R0 L0 A0 ag hS
    have sx1' := sx1 s H O0 R0 L0
    by_cases hz : env_s 0 = 0
    · simp only [loopGo, hz, if_true] at hS
      exact zc env_s env_m s H vs H' I0 z0 F0 O0 R0 L0 A0 ag hz hS
    simp only [loopGo, hz, if_false, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨r, H1⟩, hSS, hS⟩ := hS
    have e0 : env_m 0 = env_s 0 := ag 0 n0
    have hz' : env_m 0 ≠ 0 := by rw [e0]; exact hz
    obtain ⟨o1, o2, o3⟩ := O0
    have lt64 := (s.x 31).toNat_lt
    have sp0 := hrel_sp R0
    -- head and decrement
    obtain ⟨I1, z1, x81, x311, x301, m1, x51⟩ := w5 s (env_m 0) I0
    have st1 : step C (h, s) = some (h + 1, wr s 5 (env_m 0)) := by simp [step, c0, fuel s env_m F0]
    have x50 : (wr s 5 (env_m 0)).x 5 ≠ (wr s 5 (env_m 0)).x 0 := by rw [x51, z1, z0]; exact hz'
    have st2 : step C (h + 1, wr s 5 (env_m 0)) = some (h + 2, wr s 5 (env_m 0)) := by
      simp [step, c1, x50]
    have st3 : step C (h + 2, wr s 5 (env_m 0)) = some (S, wr s 5 (env_m 0)) := by
      simp [step, c2, wr]; omega
    let v := env_m 0 - 1
    let a0 := slotAddr p (s.x 8).toNat 0
    let s4 : St := ⟨upd s.x 5 v, upd s.m a0 v, s.b, s.ly⟩
    have ev : UInt64.ofNat (ea ((wr s 5 (env_m 0)).x 5) (-1)) = v := by rw [x51]; exact ea_dec _ hz'
    have st45 : run C 2 (S, wr s 5 (env_m 0)) = some (S + 2, s4) := by
      have q : ea ((wr (wr s 5 (env_m 0)) 5 v).x 8) (slotOff p 0) = a0 := by
        simp [wr, upd]; rfl
      simp only [run, step, d0, d1, ev, Option.bind_some, q]
      simp [wr, s4, LoopT.upd2, upd_same]
    have a0lo : (s.x 31).toNat ≤ a0 := slotAddr_ge (T := (s.x 31).toNat) o1 o2 (by omega)
    have a0hi : a0 < (s.x 8).toNat + 8 * p + 16 := slotAddr_lt (nl := nl) (by omega) (by omega)
    have I4 : Inv s4 := hI s s4 I0 (by simp [s4, upd]) (by simp [s4, upd]) (by simp [s4, upd]) rfl rfl (fun a ha => by
      simp only [s4, upd]; split
      · rename_i e; subst e; exfalso; apply ha; have := R0.1; have := R0.2.1; have := R0.2.2.1; omega
      · rfl)
    have z4 : s4.x 0 = 0 := by simp [s4, upd, z0]
    have x84 : s4.x 8 = s.x 8 := by simp [s4, upd]
    have x314 : s4.x 31 = s.x 31 := by simp [s4, upd]
    have x304 : s4.x 30 = s.x 30 := by simp [s4, upd]
    have F4 : Frame p nl s4 (decE env_m) := by
      intro k hk
      show upd s.m a0 v (slotAddr p (s4.x 8).toNat k) = decE env_m k
      rw [x84]
      by_cases k0 : k = 0
      · subst k0; simp [upd, decE, v, a0]
      · have ne : slotAddr p (s.x 8).toNat k ≠ a0 := fun e => k0 (slotAddr_inj (nl := nl) (by omega) hk (by omega) e)
        simp [upd, ne, decE, k0]; exact F0 k hk
    have O4 : FrameOK p nl s4 := ⟨by rw [x314, x84]; exact o1, o2, by rw [x84]; exact o3⟩
    have R4 : HRel hb s4 H := HRel_stack R0 x304 (by rw [x314]; exact R0.2.2.1) (fun a _ h2 => by
      simp only [s4, upd]; split
      · rename_i e; subst e; have := R0.2.2.1; omega
      · rfl)
    obtain ⟨g1, g2, g3, g4⟩ := slotT_wok (k := 0) L0 ⟨o1, o2, o3⟩ (by have := R0.2.1; have := R0.2.2.1; omega) (by omega) hnl
    have lt5 := (env_m 0).toNat_lt
    have nz5 : (env_m 0).toNat ≠ 0 := fun e => hz' (UInt64.toNat_inj.mp (by simpa using e))
    have sx3 : SafeX KL C (h + 2, wr s 5 (env_m 0)) := by simp only [SafeX, c2]; simp; omega
    have s45 : SStarX KL C (S, wr s 5 (env_m 0)) (S + 2, s4) := sstar_of_run st45 (fun j hj c hc => by
      rcases j with _ | _ | j
      · simp [run] at hc; subst hc; simp only [SafeX, d0]; rw [x51]
        exact ⟨by decide, by decide, by decide, by decide, by omega, by omega⟩
      · simp [run, step, d0, ev] at hc; subst hc; simp only [SafeX, d1]
        refine ⟨by decide, by decide, g2, g3, ?_, ?_⟩
        · simpa [wr, upd] using g4
        · have q : ea ((wr (wr s 5 (env_m 0)) 5 v).x 8) (slotOff p 0) = slotAddr p (s.x 8).toNat 0 := by
            simp [wr, upd]; rfl
          rw [q]; exact g1
      · omega)
    have pre : SStarX KL C (h, s) (S + 2, s4) := .head sx1' st1 (.head (sx2 _) st2 (.head sx3 st3 s45))
    have L4 : Lay KL hb E0 p s4 := L0.post' x84 rfl (by rw [x314])
    have mm4 : ∀ a, a ≠ a0 → s4.m a = s.m a := fun a ha => by simp [s4, upd, ha]
    have agd : ∀ k, ¬ (WZ k ∨ WS k) → decE env_m k = decE env_s k := by
      intro k hk; simp only [decE]; split
      · rw [e0]
      · exact ag k hk
    have hSS' : SS (decE env_m) (s4.x 31).toNat H = some (r, H1) := by
      rw [x314, hSt.stable (decE env_m) (decE env_s) _ _ (fun k hk => agd k (hsc k (Or.inr hk)))]; exact hSS
    match r, hS, hSS' with
    | .inl u, hS, hSS' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hS
      have e1 := hS.1.symm; have e2 := hS.2.symm; subst e1 e2
      obtain ⟨s', env', r', I', z', p', l', v', e8', F', ag', R', A', m'⟩ := hSt.exit s4 _ H vs H' I4 z4 F4 O4 R4 L4 A0 hSS'
      rw [x314] at p' v'; rw [x84] at e8'
      refine ⟨s', env', pre.trans r', I', z', p', l', v', e8', F', ?_, R', A', ?_⟩
      · intro k hk; simp only [not_or] at hk
        rw [ag' k hk.2.1]; simp only [decE, show k ≠ 0 by omega, if_false]
      · intro a ha hW
        rw [m' a (by rw [x314]; exact ha) (fun k hk wk => by rw [x84]; exact hW k hk (Or.inr (Or.inl wk)))]
        exact mm4 a (hW 0 (by omega) (Or.inr (Or.inr hp)))
    | .inr st, hS, hSS' =>
      obtain ⟨s5, env5, r5, I5, z5, p5, l5, e85, F5, ag5, R5, A5, m5⟩ := hSt.cont s4 _ H st H1 I4 z4 F4 O4 R4 L4 A0 hSS'
      rw [x314] at p5; rw [x84] at e85
      have O5 : FrameOK p nl s5 := ⟨by rw [p5, e85]; exact o1, o2, by rw [e85]; exact o3⟩
      have ag5' : ∀ k, ¬ (WZ k ∨ WS k) → setW env5 1 (p - 1) st k = setW (decE env_s) 1 (p - 1) st k := by
        intro k hk; simp only [setW]; split
        · rfl
        · rw [ag5 k (fun w => hk (Or.inr w))]; exact agd k hk
      have hS5 : loopGo p SZ SS (s5.x 31).toNat n (setW (decE env_s) 1 (p - 1) st) H1 = some (vs, H') := by
        rw [p5]; exact hS
      have L5 : Lay KL hb E0 p s5 := L4.post' (by rw [e85, x84]) r5.star.b (by rw [p5, x314])
      obtain ⟨s', env', r', I', z', p', l', v', e8', F', ag', R', A', m'⟩ :=
        ih (setW (decE env_s) 1 (p - 1) st) (setW env5 1 (p - 1) st) s5 H1 vs H' I5 z5 F5 O5 R5 L5 A5 ag5' hS5
      rw [p5] at p' v'; rw [e85] at e8'
      refine ⟨s', env', (pre.trans r5).trans r', I', z', p', l', v', e8', F', ?_, R', A', ?_⟩
      · intro k hk; simp only [not_or] at hk
        rw [ag' k (by simp only [not_or]; exact hk)]
        simp only [setW, show ¬ (1 ≤ k ∧ k < 1 + (p - 1)) by omega, if_false]
        rw [ag5 k hk.2.1]; simp only [decE, show k ≠ 0 by omega, if_false]
      · intro a ha hW
        rw [m' a (by rw [p5]; exact ha) (fun k hk wk => by rw [e85]; exact hW k hk wk)]
        rw [m5 a (by rw [x314]; exact ha) (fun k hk wk => by
          rw [x84]; exact hW k hk (wk.elim (fun q => Or.inr (Or.inl q)) (fun q => Or.inr (Or.inr (by omega)))))]
        exact mm4 a (hW 0 (by omega) (Or.inr (Or.inr hp)))

/-- **LOOP** (Gen's CG.loop at a def's root): the whole node is a value fragment whose exits land at h + len -/
theorem loopXS {KL : LayW} {C : List J} {h S len p nl hb E0 w : Nat} {Inv : St → Prop} {RZ WZ RS WS : Nat → Prop} {SZ SS : SemT}
    (hI : InvOKH hb p Inv)
    (hH : At C h (loopHead p ((S : Int) - ((h + 2 : Nat) : Int)))) (hD : At C S (loopDec p))
    (hZ : EVHtS KL C (h + 3) p nl Inv hb E0 RZ WZ w (h + len) h SZ)
    (hSt : EVHtS KL C (S + 2) p nl Inv hb E0 RS WS w (h + len) h SS)
    (hp : 1 ≤ p) (hpn : p ≤ nl) (hWp : ∀ k, (WZ k ∨ WS k) → p ≤ k) (hsc : ∀ k, (RZ k ∨ RS k) → ¬ (WZ k ∨ WS k))
    (hnl : nl < 251) (hSC : S + 2 ≤ C.length) (hhC : h + 3 ≤ C.length) (hC18 : C.length < 2 ^ 18) :
    EVHwS KL C h len p nl Inv hb E0 (fun k => RZ k ∨ RS k ∨ k = 0) (fun k => WZ k ∨ WS k ∨ k < p) w (loopS p SZ SS) where
  stable := fun env env' sp H hk => by
    simp only [loopS]; rw [hk 0 (Or.inr (Or.inr rfl))]
    exact loopGo_stable (R := fun k => RZ k ∨ RS k)
      (fun e e' sp H h => hZ.stable e e' sp H (fun k q => h k (Or.inl q)))
      (fun e e' sp H h => hSt.stable e e' sp H (fun k q => h k (Or.inr q))) _ env env' H
      (fun k q => hk k (q.elim (fun q => q.elim (fun q => Or.inl q) (fun q => Or.inr (Or.inl q))) (fun q => Or.inr (Or.inr q))))
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS =>
    loop_passS hI hH hD hZ hSt hp hpn hWp hsc hnl hSC hhC hC18 _ env env s H vs H' I0 z0 F0 O0 R0 L0 A0 (fun _ _ => rfl) hS

end Templates
