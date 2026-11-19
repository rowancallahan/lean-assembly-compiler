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

theorem map_cap {α β : Type} {x : Except Fail α} {f : α → β} (h : x.map f = .error .cap) : x = .error .cap := by
  cases x with
  | error e => simpa [Except.map] using h
  | ok a => simp [Except.map] at h

/-- a semantics that never fails with `cap` -/
theorem noCap {KL : LayW} {C : List J} {pc p nl hb E0 : Nat} {Inv : St → Prop} {R : Nat → Prop} {S : SemWX}
    (hn : ∀ env sp H, S env sp H ≠ .error .cap)
    (hs : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H) :
    CapW KL C pc p nl Inv hb E0 R S :=
  ⟨fun s env H _ _ _ _ _ _ _ h => absurd h (hn _ _ _), hs⟩

/-- the two-operand closing at the capacity exit -/
def Fin2CapS (KL : LayW) (C : List J) (q : Nat) (Inv : St → Prop) (hb E0 : Nat)
    (F : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : Prop :=
  ∀ (s2 : St) (H2 : Hp), Inv s2 → s2.x 0 = 0 → HRel hb s2 H2 → (s2.x 31).toNat + 16 < 2 ^ 63 →
    StkOK KL hb E0 2 s2 → HAl H2 →
    F (s2.m ((s2.x 31).toNat + 8)) (s2.m (s2.x 31).toNat) (s2.x 31).toNat H2 = .error .cap →
    ∃ s3 : St, SStarX KL C (q, s2) (6, s3) ∧ Inv s3 ∧ s3.x 0 = 0

theorem fin2Cap_ofO {KL : LayW} {C : List J} {q : Nat} {Inv : St → Prop} {hb E0 : Nat}
    (F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) :
    Fin2CapS KL C q Inv hb E0 (fun a b sp H => ofO .stuck (F a b sp H)) := by
  intro s2 H2 _ _ _ _ _ _ h
  cases e : F (s2.m ((s2.x 31).toNat + 8)) (s2.m (s2.x 31).toNat) (s2.x 31).toNat H2 <;> simp [e, ofO] at h

theorem fin2Cap_bpush {KL : LayW} {C : List J} {q : Nat} {Inv : St → Prop} {hb E0 : Nat} (hI : ∀ p, InvOKH hb p Inv)
    (hC : At C q (bpushT 6 q)) (h6 : 6 < C.length) (hC18 : C.length < 2 ^ 18) (he : E0 < 2 ^ 62) :
    Fin2CapS KL C q Inv hb E0 (bpushFF hb) := by
  intro s2 H2 I2 z2 hR hl K2 A2 hF
  simp only [bpushFF] at hF
  split at hF
  · simp at hF
  · rename_i lc hbi
    split at hF
    · rename_i hlt
      cases e : bpushF hb (s2.m ((s2.x 31).toNat + 8)) (s2.m (s2.x 31).toNat) (s2.x 31).toNat H2 <;> simp [e, ofO] at hF
    · rename_i hlt
      obtain ⟨len, cp⟩ := lc
      obtain ⟨hbb, hrl, hrc, hlc, hcap⟩ := bufInfo_spec hbi
      have ml := hread_mem hR hrl
      have mc := hread_mem hR hrc
      have h31 : hb ≤ (s2.x 31).toNat := by have := hR.2.1; have := hR.2.2.1; omega
      have hbT := (hread_lt hrl).2
      have htop := hR.2.2.1
      have kt := K2.top
      obtain ⟨s3, st3, m3, b3, z3, x3⟩ := bpush_capS (K := KL) s2 hC z2 (by have := K2.top; have := K2.hi; omega)
        (by rw [ml, mc]; simp at hlt; omega) (by omega)
        (by simpa using K2.wok h31 (i := 0) (by omega)) (K2.wok h31 (i := 1) (by omega))
        (hread_wok hR K2 A2 hrl) (hread_wok hR K2 A2 hrc) h6 hC18
      refine ⟨s3, st3, hI 0 s2 s3 I2 (x3 8 (by decide) (by decide) (by decide) (by decide) (by decide))
        (x3 28 (by decide) (by decide) (by decide) (by decide) (by decide))
        (x3 29 (by decide) (by decide) (by decide) (by decide) (by decide)) b3 (fun a _ => by rw [m3]), z3⟩

theorem fin2Cap {KL : LayW} {C : List J} {pc lp p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemWX}
    {F : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)}
    (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 2 (oW SP)) (cP : CapW KL C pc p nl Inv hb E0 R SP)
    (hU : Fin2CapS KL C (pc + lp) Inv hb E0 F) :
    CapW KL C pc p nl Inv hb E0 R (fin2F SP F) where
  stable := fun env env' sp H h => by unfold fin2F; rw [cP.stable env env' sp H h]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [fin2F] at hS
    rcases bind_cap hS with h1 | ⟨⟨ab, H1⟩, hSP, h2⟩
    · exact cP.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, A1, m1⟩ :=
      hP.run s env H ab H1 I0 z0 F0 O0 R0 L0 A0 (by simp [oW, hSP])
    match ab, l1, h2, v1 with
    | [a, b], _, h2, v1 =>
    dsimp only at h2
    have hF := map_cap h2
    have sp1 := hrel_sp R1
    have lt64 := (s.x 31).toNat_lt
    have va : s1.m ((s1.x 31).toNat + 8) = a := by
      rw [p1, show (s.x 31).toNat - 8 * 2 + 8 = (s.x 31).toNat - 8 * (0 + 1) by omega]; simpa using v1 0 (by omega)
    have vb : s1.m (s1.x 31).toNat = b := by
      rw [p1, show (s.x 31).toNat - 8 * 2 = (s.x 31).toNat - 8 * (1 + 1) by omega]; simpa using v1 1 (by omega)
    have hF' : F (s1.m ((s1.x 31).toNat + 8)) (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = .error .cap := by
      rw [va, vb, p1, show (s.x 31).toNat - 8 * 2 = (s.x 31).toNat - 16 by omega]; exact hF
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    obtain ⟨s3, st3, I3, z3⟩ := hU s1 H1 I1 z1 R1 (by rw [p1]; have := O0.1; have := O0.2.2; omega)
      ⟨L0.lo, L0.hi, by rw [p1]; have := L0.top; have := O0.1; have := R1.1; have := R1.2.1; have := R1.2.2.1; rw [p1] at *; omega, L1.a31⟩ A1 hF'
    exact ⟨s3, r1.trans st3, I3, z3⟩

/-- a closing that never fails with `cap`: the cap comes from the operands -/
theorem finCap_of {KL : LayW} {C : List J} {pc lp p nl hb E0 w : Nat} {Inv : St → Prop} {R W : Nat → Prop}
    {SP : SemWX} {G : Nat → (List UInt64 × Hp) → Except Fail (List UInt64 × Hp)}
    (hP : EVHwS KL C pc lp p nl Inv hb E0 R W w (oW SP)) (cP : CapW KL C pc p nl Inv hb E0 R SP)
    (hG : ∀ sp r, G sp r ≠ .error .cap) :
    CapW KL C pc p nl Inv hb E0 R (fun env sp H => (SP env sp H).bind (G sp)) where
  stable := fun env env' sp H h => by
    show (SP env sp H).bind (G sp) = (SP env' sp H).bind (G sp); rw [cP.stable env env' sp H h]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    rcases bind_cap hS with h1 | ⟨r, _, h2⟩
    · exact cP.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    · exact absurd h2 (hG _ r)

theorem ofO_ne_cap {α : Type} (o : Option α) : ofO .stuck o ≠ .error .cap := by cases o <;> simp [ofO]
theorem map_ne_cap {α β : Type} {x : Except Fail α} (f : α → β) (h : x ≠ .error .cap) : x.map f ≠ .error .cap :=
  fun e => h (map_cap e)

theorem fin1Cap {KL : LayW} {C : List J} {pc lp p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemWX}
    {F : UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 1 (oW SP)) (cP : CapW KL C pc p nl Inv hb E0 R SP) :
    CapW KL C pc p nl Inv hb E0 R (fin1F SP (fun a sp H => ofO .stuck (F a sp H))) :=
  finCap_of hP cP (fun sp r => by
    obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp only [] <;>
      first | exact map_ne_cap _ (ofO_ne_cap _) | simp)

theorem fin3Cap {KL : LayW} {C : List J} {pc lp p nl hb E0 : Nat} {Inv : St → Prop} {R W : Nat → Prop} {SP : SemWX}
    {F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 3 (oW SP)) (cP : CapW KL C pc p nl Inv hb E0 R SP) :
    CapW KL C pc p nl Inv hb E0 R (fin3F SP (fun a b c sp H => ofO .stuck (F a b c sp H))) :=
  finCap_of hP cP (fun sp r => by
    obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp only [] <;>
      first | exact map_ne_cap _ (ofO_ne_cap _) | simp)

/-! ## IF: the head (pop the two operands, compare, branch) as a lemma -/

theorem ifHeadS {KL : LayW} {C : List J} {q lt p nl hb E0 cmp : Nat} {Inv : St → Prop} (hI : InvOKH hb p Inv)
    (hH : At C q (ifHeadG cmp lt)) (hCl : q + 6 + lt < C.length) (hC18 : C.length < 2 ^ 18)
    (s s1 : St) (env1 : Env) (H1 : Hp) (a b : UInt64) (O0 : FrameOK p nl s) (L0 : Lay KL hb E0 p s)
    (I1 : Inv s1) (z1 : s1.x 0 = 0) (p1 : (s1.x 31).toNat = (s.x 31).toNat - 8 * 2)
    (va : s1.m ((s.x 31).toNat - 8) = a) (vb : s1.m ((s.x 31).toNat - 8 - 8) = b) (e81 : s1.x 8 = s.x 8)
    (F1 : Frame p nl s1 env1) (R1 : HRel hb s1 H1) (eb : s1.b = s.b) :
    ∃ s2, SStarX KL C (q, s1) (if cmpF cmp a b then q + 5 else q + 6 + lt, s2) ∧ Inv s2 ∧ s2.x 0 = 0 ∧
      (s2.x 31).toNat = (s.x 31).toNat ∧ s2.x 8 = s.x 8 ∧ s2.m = s1.m ∧ s2.b = s.b ∧ Frame p nl s2 env1 ∧
      FrameOK p nl s2 ∧ HRel hb s2 H1 ∧ Lay KL hb E0 p s2 := by
  obtain ⟨o1, o2, o3⟩ := O0
  have lt64 := (s.x 31).toNat_lt
  have L1 : Lay KL hb E0 p s1 := L0.post e81 eb p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
  have c0 := hH.at 0 (by simp [ifHeadG]); have c1 := hH.at 1 (by simp [ifHeadG])
  have c2 := hH.at 2 (by simp [ifHeadG]); have c3 := hH.at 3 (by simp [ifHeadG])
  have c4 := hH.at 4 (by simp [ifHeadG])
  simp only [ifHeadG, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 c3 c4
  have sp1 := hrel_sp R1
  have ea0 : ea (s1.x 31) 0 = (s.x 31).toNat - 8 - 8 := by simp [ea, p1]; omega
  have ea8 : ea (s1.x 31) 8 = (s.x 31).toNat - 8 := by simp [ea, p1]; omega
  have ea16 : ea (s1.x 31) 16 = (s.x 31).toNat := by simp [ea, p1]; omega
  let s2 : St := ⟨upd (upd (upd s1.x 6 b) 5 a) 31 (UInt64.ofNat (s.x 31).toNat), s1.m, s1.b⟩
  have r2 : CallProbe.run C 3 (q, s1) = some (q + 3, s2) := by
    simp [CallProbe.run, CallProbe.step, c0, c1, c2, CallProbe.wr, ea0, ea8, va, vb, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
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
  have st2 : SStarX KL C (q, s1) (q + 3, s2) := sstarX_of_run r2 (fun j hj c hc => by
    rcases j with _ | _ | _ | j
    · simp [CallProbe.run] at hc; subst hc; simp only [SafeX, c0]; rw [ea0]
      exact ⟨by decide, by decide, by decide, by decide, by omega, w1a⟩
    · simp [CallProbe.run, CallProbe.step, c0, CallProbe.wr, ea0] at hc; subst hc; simp only [SafeX, c1]
      refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
      · simp [upd]; omega
      · have : ea (upd s1.x 6 (s1.m ((s.x 31).toNat - 8 - 8)) 31) 8 = (s.x 31).toNat - 8 := by simpa [upd] using ea8
        simpa [this] using w1b
    · simp [CallProbe.run, CallProbe.step, c0, c1, CallProbe.wr, ea0, ea8, upd] at hc; subst hc; simp only [SafeX, c2]; simp [upd]; omega
    · omega)
  have safe3 : SafeX KL C (q + 3, s2) := by
    have hc3 := c3; unfold cmpJ at hc3; split at hc3 <;> (simp only [SafeX, hc3]; decide)
  have sc := step_cmp (s := s2) c3
  rw [x5, x6] at sc
  have L2 : Lay KL hb E0 p s2 := L0.post' x8 (by show s1.b = s.b; exact eb) (by rw [x31])
  by_cases hc : cmpF cmp a b
  · rw [if_pos hc] at sc ⊢
    exact ⟨s2, st2.trans (.head safe3 sc (.refl _)), I2, z2, x31, x8, rfl, eb, F2, O2, R2, L2⟩
  · rw [if_neg hc] at sc ⊢
    have sj0 : CallProbe.step C (q + 4, s2) = some (q + 6 + lt, CallProbe.wr s2 0 (UInt64.ofNat (s2.b + 4 * (q + 4 + 1)))) := by
      simp [CallProbe.step, c4]; omega
    have w2 : CallProbe.wr s2 0 (UInt64.ofNat (s2.b + 4 * (q + 4 + 1))) = s2 := by simp [CallProbe.wr]
    rw [w2] at sj0
    have sj2 : SafeX KL C (q + 4, s2) := by simp only [SafeX, c4]; simp; omega
    exact ⟨s2, st2.trans (.head safe3 sc (.head sj2 sj0 (.refl _))), I2, z2, x31, x8, rfl, eb, F2, O2, R2, L2⟩

theorem ifCap {KL : LayW} {C : List J} {pc lp lt p nl hb E0 cmp : Nat} {Inv : St → Prop} {RP WP RT RE : Nat → Prop}
    {SP ST SE : SemWX} (hI : InvOKH hb p Inv)
    (hP : EVHwS KL C pc lp p nl Inv hb E0 RP WP 2 (oW SP)) (cP : CapW KL C pc p nl Inv hb E0 RP SP)
    (hH : At C (pc + lp) (ifHeadG cmp lt))
    (cT : CapW KL C (pc + lp + 5) p nl Inv hb E0 RT ST) (cE : CapW KL C (pc + lp + 6 + lt) p nl Inv hb E0 RE SE)
    (sT : ∀ k, RT k → ¬ WP k) (sE : ∀ k, RE k → ¬ WP k) (hCl : pc + lp + 6 + lt < C.length)
    (hC18 : C.length < 2 ^ 18) :
    CapW KL C pc p nl Inv hb E0 (fun k => RP k ∨ RT k ∨ RE k) (ifF cmp SP ST SE) where
  stable := fun env env' sp H h => by
    simp only [ifF]
    rw [cP.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SP env' sp H with
    | error e => rfl
    | ok r =>
      simp only [Except.bind]
      rw [cT.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inl hk))),
        cE.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inr hk)))]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [ifF] at hS
    rcases bind_cap hS with h1 | ⟨⟨ab, H1⟩, hSP, h2⟩
    · exact cP.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, A1, m1⟩ :=
      hP.run s env H ab H1 I0 z0 F0 O0 R0 L0 A0 (by simp [oW, hSP])
    match ab, l1, h2, v1 with
    | [a, b], _, h2, v1 =>
    have lt64 := (s.x 31).toNat_lt
    have sp1 := hrel_sp R1
    have va : s1.m ((s.x 31).toNat - 8) = a := by simpa using v1 0 (by omega)
    have vb : s1.m ((s.x 31).toNat - 8 - 8) = b := by
      have := v1 1 (by omega); rw [show (s.x 31).toNat - 8 * (1 + 1) = (s.x 31).toNat - 8 - 8 by omega] at this
      simpa using this
    dsimp only at h2
    obtain ⟨s2, st2, I2, z2, x31, x8, _, _, F2, O2, R2, L2⟩ :=
      ifHeadS hI hH hCl hC18 s s1 env1 H1 a b O0 L0 I1 z1 p1 va vb e81 F1 R1 r1.star.b
    by_cases hc : cmpF cmp a b
    · rw [if_pos hc] at h2 st2
      have hST : ST env1 (s2.x 31).toNat H1 = .error .cap := by
        rw [x31, cT.stable env1 env _ _ (fun k hk => ag1 k (sT k hk))]; exact h2
      obtain ⟨s3, r3, I3, z3⟩ := cT.cap s2 env1 H1 I2 z2 F2 O2 R2 L2 A1 hST
      exact ⟨s3, r1.trans (st2.trans r3), I3, z3⟩
    · rw [if_neg hc] at h2 st2
      have hSE : SE env1 (s2.x 31).toNat H1 = .error .cap := by
        rw [x31, cE.stable env1 env _ _ (fun k hk => ag1 k (sE k hk))]; exact h2
      obtain ⟨s3, r3, I3, z3⟩ := cE.cap s2 env1 H1 I2 z2 F2 O2 R2 L2 A1 hSE
      exact ⟨s3, r1.trans (st2.trans r3), I3, z3⟩

end Templates
