/- Opus box E: the capacity exit as SAFE runs.  `bpush_capS`: BPUSH on a full buffer reaches the cap stub (word 6)
on safe steps, memory untouched. -/
import Nano.V2Self.Proof.SemX
import Nano.V2Self.Proof.EVSFin
import Nano.V2Self.Proof.EVSComp
namespace Templates
open CallProbe SimW

theorem bpush_capS {K : LayW} {C : List J} {pc : Nat} (s : St) (hC : At C pc (bpushT 6 pc)) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 16 < 2 ^ 62)
    (hlen : (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat ≤ (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat)
    (hb : (s.m ((s.x 31).toNat + 8)).toNat + 16 < 2 ^ 62)
    (w0 : wok K (s.x 31).toNat) (w1 : wok K ((s.x 31).toNat + 8)) (w2 : wok K (s.m ((s.x 31).toNat + 8)).toNat)
    (w3 : wok K ((s.m ((s.x 31).toNat + 8)).toNat + 8)) (h6 : 6 < C.length) (hC18 : C.length < 2 ^ 18) :
    ∃ s', SStarX K C (pc, s) (6, s') ∧ s'.m = s.m ∧ s'.b = s.b ∧ s'.x 0 = 0 ∧
      ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r := by
  have hs : ∀ i, i < 12 → C[pc + i]? = (bpushT 6 pc)[i]? := fun i hi => hC i (by simp [bpushT]; omega)
  have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega); have h3 := hs 3 (by omega)
  have h4 := hs 4 (by omega); have h5 := hs 5 (by omega); have h6' := hs 6 (by omega)
  simp [bpushT] at h0 h1 h2 h3 h4 h5 h6'
  have lt := (s.x 31).toNat_lt
  have hpl : pc + 6 < C.length := (List.getElem?_eq_some_iff.1 h6').1
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have eb0 : ∀ b : UInt64, ea b 0 = b.toNat := fun b => by simp [ea]
  have blt := (s.m ((s.x 31).toNat + 8)).toNat_lt
  have ebuf8 : ea (s.m ((s.x 31).toNat + 8)) 8 = (s.m ((s.x 31).toNat + 8)).toNat + 8 := by simp [ea]; omega
  have hc : ¬ (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat := by omega
  have ej : ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 1 + (6 - (pc + 6 : Nat))).toNat = 6 := by omega
  have hr : ∃ s', run C 7 (pc, s) = some (6, s') ∧ s'.m = s.m ∧ s'.b = s.b ∧ s'.x 0 = 0 ∧
      ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r := by
    simp [CallProbe.run, CallProbe.step, h0, h1, h2, h3, h4, h5, h6', CallProbe.wr, e0, e8, eb0, ebuf8, hc, upd_ne, upd_same, ej]
    refine ⟨_, ⟨by omega, rfl⟩, rfl, rfl, by simp [upd_ne, hx0], fun r r5 r6 r7 r14 r31 => ?_⟩
    simp [upd, r5, r6, r7, r14, r31]
  obtain ⟨s', hr, rest⟩ := hr
  refine ⟨s', SStarX.of (SafeRun.sstar_of_run hr ?_), rest⟩
  intro j hj c hc'
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CallProbe.run, CallProbe.step, h0, h1, h2, h3, h4, h5, h6', CallProbe.wr, e0, e8, eb0, ebuf8, hc, upd_ne, upd_same] at hc' <;> subst hc' <;>
    simp [Safe, h0, h1, h2, h3, h4, h5, h6', CallProbe.wr, e0, e8, eb0, ebuf8, hc, upd_ne, upd_same, hx0] <;>
    first | omega | assumption | exact ⟨by omega, by assumption⟩

/-! ## the capacity contracts: the kinded semantics fails with `cap` ⇒ the run reaches the cap stub (word 6) -/

/-- **CapW** (multi-word results): `cap` ⇒ a safe run to word 6 keeping the invariant; reads only `R` -/
structure CapW (KL : LayW) (C : List J) (pc p nl : Nat) (Inv : St → Prop) (hb E0 : Nat) (R : Nat → Prop)
    (S : SemWX) : Prop where
  cap : ∀ (s : St) (env : Env) (H : Hp), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s → HRel hb s H →
    Lay KL hb E0 p s → HAl H → S env (s.x 31).toNat H = .error .cap →
    ∃ s', SStarX KL C (pc, s) (6, s') ∧ Inv s' ∧ s'.x 0 = 0
  stable : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H

theorem bind_cap {α β : Type} {x : Except Fail α} {f : α → Except Fail β} (h : x.bind f = .error .cap) :
    x = .error .cap ∨ ∃ a, x = .ok a ∧ f a = .error .cap := by
  cases x with
  | error e => left; simpa [Except.bind] using h
  | ok a => right; exact ⟨a, rfl, h⟩

theorem pairCap {KL : LayW} {C : List J} {pc la p nl hb E0 wa wb : Nat} {Inv : St → Prop}
    {RA WA RB : Nat → Prop} {SA SB : SemWX}
    (hA : EVHwS KL C pc la p nl Inv hb E0 RA WA wa (oW SA)) (cA : CapW KL C pc p nl Inv hb E0 RA SA)
    (cB : CapW KL C (pc + la) p nl Inv hb E0 RB SB) (sB : ∀ k, RB k → ¬ WA k) :
    CapW KL C pc p nl Inv hb E0 (fun k => RA k ∨ RB k) (pairF wa SA SB) where
  stable := fun env env' sp H h => by
    simp only [pairF]
    rw [cA.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SA env' sp H with
    | error e => rfl
    | ok r1 => simp only [Except.bind]; rw [cB.stable env env' _ r1.2 (fun k hk => h k (Or.inr hk))]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [pairF] at hS
    rcases bind_cap hS with h1 | ⟨⟨a, H1⟩, hSA, h2⟩
    · exact cA.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    rcases bind_cap h2 with h3 | ⟨_, _, h4⟩
    · obtain ⟨o1, o2, o3⟩ := O0
      obtain ⟨s1, env1, r1, I1, z1, p1, la1, v1, e81, F1, ag1, R1, A1, m1⟩ :=
        hA.run s env H a H1 I0 z0 F0 ⟨o1, o2, o3⟩ R0 L0 A0 (by simp [oW, hSA])
      have hs1 := hrel_sp R1
      have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.2.2.1; omega)
      have hSB1 : SB env1 (s1.x 31).toNat H1 = .error .cap := by
        rw [p1, cB.stable env1 env _ _ (fun k hk => ag1 k (sB k hk))]; exact h3
      obtain ⟨s2, r2, I2, z2⟩ := cB.cap s1 env1 H1 I1 z1 F1 ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩ R1 L1 A1 hSB1
      exact ⟨s2, r1.trans r2, I2, z2⟩
    · exact absurd h4 (by simp)

end Templates
