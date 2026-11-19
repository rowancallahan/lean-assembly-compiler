/- Opus box E: the capacity exit as SAFE runs.  `bpush_capS`: BPUSH on a full buffer reaches the cap stub (word 6)
on safe steps, memory untouched. -/
import Nano.V2Self.Proof.SemX
import Nano.V2Self.Proof.EVSFin
import Nano.V2Self.Proof.EVSComp
import Nano.V2Self.Proof.EVSTail
import Nano.V2Self.Proof.EVSLoop
import Nano.V2Self.Proof.EVSCall
namespace Templates
open CallProbe SimW SafeRun

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
structure CapW (fk : Fail) (tg : Nat) (KL : LayW) (C : List J) (pc p nl : Nat) (Inv G : St → Prop) (hb E0 : Nat) (R : Nat → Prop)
    (S : SemWX) : Prop where
  cap : ∀ (s : St) (env : Env) (H : Hp), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s → HRel hb s H →
    Lay KL hb E0 p s → HAl H → S env (s.x 31).toNat H = .error fk →
    ∃ s', SStarX KL C (pc, s) (tg, s') ∧ G s' ∧ s'.x 0 = 0
  stable : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H

theorem bind_cap {α β : Type} {fk : Fail} {x : Except Fail α} {f : α → Except Fail β} (h : x.bind f = .error fk) :
    x = .error fk ∨ ∃ a, x = .ok a ∧ f a = .error fk := by
  cases x with
  | error e => left; simpa [Except.bind] using h
  | ok a => right; exact ⟨a, rfl, h⟩

theorem pairCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc la p nl hb E0 wa : Nat} {Inv : St → Prop} {G : St → Prop}
    {RA WA RB : Nat → Prop} {SA SB : SemWX}
    (hA : EVHwS KL C pc la p nl Inv hb E0 RA WA wa (oW SA)) (cA : CapW fk tg KL C pc p nl Inv G hb E0 RA SA)
    (cB : CapW fk tg KL C (pc + la) p nl Inv G hb E0 RB SB) (sB : ∀ k, RB k → ¬ WA k) :
    CapW fk tg KL C pc p nl Inv G hb E0 (fun k => RA k ∨ RB k) (pairF wa SA SB) where
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
      have hSB1 : SB env1 (s1.x 31).toNat H1 = .error fk := by
        rw [p1, cB.stable env1 env _ _ (fun k hk => ag1 k (sB k hk))]; exact h3
      obtain ⟨s2, r2, I2, z2⟩ := cB.cap s1 env1 H1 I1 z1 F1 ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩ R1 L1 A1 hSB1
      exact ⟨s2, r1.trans r2, I2, z2⟩
    · exact absurd h4 (by simp)

theorem map_cap {α β : Type} {fk : Fail} {x : Except Fail α} {f : α → β} (h : x.map f = .error fk) : x = .error fk := by
  cases x with
  | error e => simpa [Except.map] using h
  | ok a => simp [Except.map] at h

/-- a semantics that never fails with `cap` -/
theorem noCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc p nl hb E0 : Nat} {Inv : St → Prop} {G : St → Prop} {R : Nat → Prop} {S : SemWX}
    (hn : ∀ env sp H, S env sp H ≠ .error fk)
    (hs : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H) :
    CapW fk tg KL C pc p nl Inv G hb E0 R S :=
  ⟨fun s env H _ _ _ _ _ _ _ h => absurd h (hn _ _ _), hs⟩

/-- the two-operand closing at the capacity exit -/
def Fin2CapS (fk : Fail) (tg : Nat) (KL : LayW) (C : List J) (q : Nat) (Inv G : St → Prop) (hb E0 : Nat)
    (F : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : Prop :=
  ∀ (s2 : St) (H2 : Hp), Inv s2 → s2.x 0 = 0 → HRel hb s2 H2 → (s2.x 31).toNat + 16 < 2 ^ 63 →
    StkOK KL hb E0 2 s2 → HAl H2 →
    F (s2.m ((s2.x 31).toNat + 8)) (s2.m (s2.x 31).toNat) (s2.x 31).toNat H2 = .error fk →
    ∃ s3 : St, SStarX KL C (q, s2) (tg, s3) ∧ G s3 ∧ s3.x 0 = 0

theorem ofO_ne_cap {α : Type} {fk : Fail} (hk : fk ≠ .stuck) (o : Option α) : ofO .stuck o ≠ .error fk := by
  cases o <;> simp [ofO]; exact fun e => hk e.symm
theorem map_ne_cap {α β : Type} {fk : Fail} {x : Except Fail α} (f : α → β) (h : x ≠ .error fk) : x.map f ≠ .error fk :=
  fun e => h (map_cap e)


theorem fin2Cap_ofO {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {q : Nat} {Inv : St → Prop} {G : St → Prop} {hb E0 : Nat}
    (hk : fk ≠ .stuck) (F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) :
    Fin2CapS fk tg KL C q Inv G hb E0 (fun a b sp H => ofO .stuck (F a b sp H)) := by
  intro s2 H2 _ _ _ _ _ _ h
  exact absurd h (ofO_ne_cap hk _)

theorem fin2Cap_bpush {KL : LayW} {C : List J} {q : Nat} {Inv : St → Prop} {G : St → Prop} {hb E0 pI : Nat} (hI : InvOKH hb pI Inv)
    (hG : ∀ s, Inv s → G s) (hC : At C q (bpushT 6 q)) (h6 : 6 < C.length) (hC18 : C.length < 2 ^ 18)
    (he : E0 < 2 ^ 62) :
    Fin2CapS .cap 6 KL C q Inv G hb E0 (bpushFF hb) := by
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
      refine ⟨s3, st3, hG _ <| hI s2 s3 I2 (x3 8 (by decide) (by decide) (by decide) (by decide) (by decide))
        (x3 28 (by decide) (by decide) (by decide) (by decide) (by decide))
        (x3 29 (by decide) (by decide) (by decide) (by decide) (by decide)) b3 (fun a _ => by rw [m3]), z3⟩

theorem fin2Cap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc lp p nl hb E0 : Nat} {Inv : St → Prop} {G : St → Prop} {R W : Nat → Prop} {SP : SemWX}
    {F : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)}
    (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 2 (oW SP)) (cP : CapW fk tg KL C pc p nl Inv G hb E0 R SP)
    (hU : Fin2CapS fk tg KL C (pc + lp) Inv G hb E0 F) :
    CapW fk tg KL C pc p nl Inv G hb E0 R (fin2F SP F) where
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
    have hF' : F (s1.m ((s1.x 31).toNat + 8)) (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = .error fk := by
      rw [va, vb, p1, show (s.x 31).toNat - 8 * 2 = (s.x 31).toNat - 16 by omega]; exact hF
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    obtain ⟨s3, st3, I3, z3⟩ := hU s1 H1 I1 z1 R1 (by rw [p1]; have := O0.1; have := O0.2.2; omega)
      ⟨L0.lo, L0.hi, by rw [p1]; have := L0.top; have := O0.1; have := R1.1; have := R1.2.1; have := R1.2.2.1; rw [p1] at *; omega, L1.a31⟩ A1 hF'
    exact ⟨s3, r1.trans st3, I3, z3⟩

/-- a closing that never fails with `cap`: the cap comes from the operands -/
theorem finCap_of {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc lp p nl hb E0 w : Nat} {Inv : St → Prop} {G : St → Prop} {R W : Nat → Prop}
    {SP : SemWX} {Gk : Nat → (List UInt64 × Hp) → Except Fail (List UInt64 × Hp)}
    (hP : EVHwS KL C pc lp p nl Inv hb E0 R W w (oW SP)) (cP : CapW fk tg KL C pc p nl Inv G hb E0 R SP)
    (hG : ∀ sp r, Gk sp r ≠ .error fk) :
    CapW fk tg KL C pc p nl Inv G hb E0 R (fun env sp H => (SP env sp H).bind (Gk sp)) where
  stable := fun env env' sp H h => by
    show (SP env sp H).bind (Gk sp) = (SP env' sp H).bind (Gk sp); rw [cP.stable env env' sp H h]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    rcases bind_cap hS with h1 | ⟨r, _, h2⟩
    · exact cP.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    · exact absurd h2 (hG _ r)

theorem fin1Cap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc lp p nl hb E0 : Nat} {Inv : St → Prop} {G : St → Prop} {R W : Nat → Prop} {SP : SemWX}
    {F : UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 1 (oW SP)) (cP : CapW fk tg KL C pc p nl Inv G hb E0 R SP)
    (hk : fk ≠ .stuck) :
    CapW fk tg KL C pc p nl Inv G hb E0 R (fin1F SP (fun a sp H => ofO .stuck (F a sp H))) :=
  finCap_of hP cP (fun sp r => by
    obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp only [] <;>
      first | exact map_ne_cap _ (ofO_ne_cap hk _) | (intro e; injection e with e; exact hk e.symm))

theorem fin3Cap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc lp p nl hb E0 : Nat} {Inv : St → Prop} {G : St → Prop} {R W : Nat → Prop} {SP : SemWX}
    {F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)}
    (hP : EVHwS KL C pc lp p nl Inv hb E0 R W 3 (oW SP)) (cP : CapW fk tg KL C pc p nl Inv G hb E0 R SP)
    (hk : fk ≠ .stuck) :
    CapW fk tg KL C pc p nl Inv G hb E0 R (fin3F SP (fun a b c sp H => ofO .stuck (F a b c sp H))) :=
  finCap_of hP cP (fun sp r => by
    obtain ⟨l, H'⟩ := r; rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;> simp only [] <;>
      first | exact map_ne_cap _ (ofO_ne_cap hk _) | (intro e; injection e with e; exact hk e.symm))

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

theorem ifCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc lp lt p nl hb E0 cmp : Nat} {Inv : St → Prop} {G : St → Prop} {RP WP RT RE : Nat → Prop}
    {SP ST SE : SemWX} (hI : InvOKH hb p Inv)
    (hP : EVHwS KL C pc lp p nl Inv hb E0 RP WP 2 (oW SP)) (cP : CapW fk tg KL C pc p nl Inv G hb E0 RP SP)
    (hH : At C (pc + lp) (ifHeadG cmp lt))
    (cT : CapW fk tg KL C (pc + lp + 5) p nl Inv G hb E0 RT ST) (cE : CapW fk tg KL C (pc + lp + 6 + lt) p nl Inv G hb E0 RE SE)
    (sT : ∀ k, RT k → ¬ WP k) (sE : ∀ k, RE k → ¬ WP k) (hCl : pc + lp + 6 + lt < C.length)
    (hC18 : C.length < 2 ^ 18) :
    CapW fk tg KL C pc p nl Inv G hb E0 (fun k => RP k ∨ RT k ∨ RE k) (ifF cmp SP ST SE) where
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
      have hST : ST env1 (s2.x 31).toNat H1 = .error fk := by
        rw [x31, cT.stable env1 env _ _ (fun k hk => ag1 k (sT k hk))]; exact h2
      obtain ⟨s3, r3, I3, z3⟩ := cT.cap s2 env1 H1 I2 z2 F2 O2 R2 L2 A1 hST
      exact ⟨s3, r1.trans (st2.trans r3), I3, z3⟩
    · rw [if_neg hc] at h2 st2
      have hSE : SE env1 (s2.x 31).toNat H1 = .error fk := by
        rw [x31, cE.stable env1 env _ _ (fun k hk => ag1 k (sE k hk))]; exact h2
      obtain ⟨s3, r3, I3, z3⟩ := cE.cap s2 env1 H1 I2 z2 F2 O2 R2 L2 A1 hSE
      exact ⟨s3, r1.trans (st2.trans r3), I3, z3⟩

/-! ## LET: the value's words into the slots, as a lemma -/

theorem letMidS {KL : LayW} {C : List J} {q p nl hb E0 k0 w : Nat} {Inv : St → Prop} (hI : InvOKH hb p Inv)
    (hS : At C q (popN p k0 w)) (hk0 : k0 + w ≤ nl) (hnl : nl < 251)
    (s s1 : St) (env1 : Env) (H1 : Hp) (u : List UInt64) (O0 : FrameOK p nl s) (L0 : Lay KL hb E0 p s)
    (I1 : Inv s1) (z1 : s1.x 0 = 0) (p1 : (s1.x 31).toNat = (s.x 31).toNat - 8 * w) (lu : u.length = w)
    (v1 : ∀ i, i < w → s1.m ((s.x 31).toNat - 8 * (i + 1)) = u.getD i 0) (e81 : s1.x 8 = s.x 8)
    (F1 : Frame p nl s1 env1) (R1 : HRel hb s1 H1) (eb : s1.b = s.b) :
    ∃ s2, SStarX KL C (q, s1) (q + 3 * w, s2) ∧ Inv s2 ∧ s2.x 0 = 0 ∧
      (s2.x 31).toNat = (s.x 31).toNat ∧ s2.x 8 = s.x 8 ∧ s2.b = s.b ∧ Frame p nl s2 (setW env1 k0 w u) ∧
      FrameOK p nl s2 ∧ HRel hb s2 H1 ∧ Lay KL hb E0 p s2 ∧
      (∀ a, (∀ j, j < w → a ≠ slotAddr p (s.x 8).toNat (k0 + j)) → s2.m a = s1.m a) := by
  obtain ⟨o1, o2, o3⟩ := O0
  have lt64 := (s.x 31).toNat_lt
  have sp1 := hrel_sp R1
  have T1 : (s1.x 31).toNat + 8 * w = (s.x 31).toNat := by rw [p1]; have := R1.2.2.1; omega
  obtain ⟨s2, r2, p2, e82, ex2, eb2, ms2, mo2⟩ := popN_run (p := p) (k0 := k0) w q s1 hS (by omega)
    (fun j j' hj hj' e => by have := slotAddr_inj (nl := nl) (by rw [e81]; omega) (by omega) (by omega) e; omega)
    (fun j i hj hi => by
      rw [e81]; have := slotAddr_ge (T := (s.x 31).toNat) (k := k0 + j) (by omega) o2 (by omega); omega)
  have L1 : Lay KL hb E0 p s1 := L0.post e81 eb p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
  have ss2 : SStarX KL C (q, s1) (q + 3 * w, s2) := SStarX.of (popN_srun w q s1 hS (by omega)
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
  have L2 : Lay KL hb E0 p s2 := L0.post' x8 (by rw [eb2, eb]) x31
  exact ⟨s2, ss2, I2, z2, x31, x8, by rw [eb2, eb], F2, ⟨by rw [x31, x8]; omega, o2, by rw [x8]; omega⟩, R2, L2,
    fun a ha => mo2 a (fun j hj e => ha j hj e)⟩

theorem letCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc lv p nl hb E0 k0 w : Nat} {Inv : St → Prop} {G : St → Prop} {Rv Wv Rb : Nat → Prop}
    {SV SB : SemWX} (hI : InvOKH hb p Inv)
    (hv : EVHwS KL C pc lv p nl Inv hb E0 Rv Wv w (oW SV)) (cv : CapW fk tg KL C pc p nl Inv G hb E0 Rv SV)
    (hS : At C (pc + lv) (popN p k0 w)) (cb : CapW fk tg KL C (pc + lv + 3 * w) p nl Inv G hb E0 Rb SB)
    (hk0 : k0 + w ≤ nl) (hsc : ∀ k, Rb k → ¬ (k0 ≤ k ∧ k < k0 + w) → ¬ Wv k) (hnl : nl < 251) :
    CapW fk tg KL C pc p nl Inv G hb E0 (fun k => Rv k ∨ (Rb k ∧ ¬ (k0 ≤ k ∧ k < k0 + w))) (letF k0 w SV SB) where
  stable := fun env env' sp H h => by
    simp only [letF]
    rw [cv.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SV env' sp H with
    | error e => rfl
    | ok r =>
      simp only [Except.bind]
      apply cb.stable; intro k hk
      unfold setW
      split
      · rfl
      · rename_i hk'; exact h k (Or.inr ⟨hk, hk'⟩)
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS' => by
    simp only [letF] at hS'
    rcases bind_cap hS' with h1 | ⟨⟨u, H1⟩, hSV, h2⟩
    · exact cv.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    obtain ⟨s1, env1, r1, I1, z1, p1, lu, v1, e81, F1, ag1, R1, A1, m1⟩ :=
      hv.run s env H u H1 I0 z0 F0 O0 R0 L0 A0 (by simp [oW, hSV])
    obtain ⟨s2, ss2, I2, z2, x31, x8, _, F2, O2, R2, L2, _⟩ :=
      letMidS hI hS hk0 hnl s s1 env1 H1 u O0 L0 I1 z1 p1 lu v1 e81 F1 R1 r1.star.b
    have hSB2 : SB (setW env1 k0 w u) (s2.x 31).toNat H1 = .error fk := by
      rw [x31]; rw [← h2]; apply cb.stable; intro k hk
      simp only [setW]
      by_cases e : k0 ≤ k ∧ k < k0 + w
      · simp [e]
      · simp only [e, if_false]; exact ag1 k (hsc k hk e)
    obtain ⟨s3, r3, I3, z3⟩ := cb.cap s2 _ H1 I2 z2 F2 O2 R2 L2 A1 hSB2
    exact ⟨s3, (r1.trans ss2).trans r3, I3, z3⟩

/-! ## tail mode -/

/-- **CapT** (tail-mode semantics) -/
structure CapT (fk : Fail) (tg : Nat) (KL : LayW) (C : List J) (pc p nl : Nat) (Inv G : St → Prop) (hb E0 : Nat) (R : Nat → Prop)
    (S : SemTX) : Prop where
  cap : ∀ (s : St) (env : Env) (H : Hp), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s → HRel hb s H →
    Lay KL hb E0 p s → HAl H → S env (s.x 31).toNat H = .error fk →
    ∃ s', SStarX KL C (pc, s) (tg, s') ∧ G s' ∧ s'.x 0 = 0
  stable : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H

theorem exitCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc p nl hb E0 : Nat} {Inv : St → Prop} {G : St → Prop} {R : Nat → Prop} {S : SemWX}
    (c : CapW fk tg KL C pc p nl Inv G hb E0 R S) : CapT fk tg KL C pc p nl Inv G hb E0 R (exitF S) where
  stable := fun env env' sp H h => by simp only [exitF]; rw [c.stable env env' sp H h]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => c.cap s env H I0 z0 F0 O0 R0 L0 A0 (map_cap hS)

theorem contCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc p nl hb E0 : Nat} {Inv : St → Prop} {G : St → Prop} {R : Nat → Prop} {S : SemWX}
    (c : CapW fk tg KL C pc p nl Inv G hb E0 R S) : CapT fk tg KL C pc p nl Inv G hb E0 R (contF S) where
  stable := fun env env' sp H h => by simp only [contF]; rw [c.stable env env' sp H h]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => c.cap s env H I0 z0 F0 O0 R0 L0 A0 (map_cap hS)

theorem ifTCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc lp lt p nl hb E0 cmp : Nat} {Inv : St → Prop} {G : St → Prop} {RP WP RT RE : Nat → Prop}
    {SP : SemWX} {ST SE : SemTX} (hI : InvOKH hb p Inv)
    (hP : EVHwS KL C pc lp p nl Inv hb E0 RP WP 2 (oW SP)) (cP : CapW fk tg KL C pc p nl Inv G hb E0 RP SP)
    (hH : At C (pc + lp) (ifHeadG cmp lt))
    (cT : CapT fk tg KL C (pc + lp + 5) p nl Inv G hb E0 RT ST) (cE : CapT fk tg KL C (pc + lp + 6 + lt) p nl Inv G hb E0 RE SE)
    (sT : ∀ k, RT k → ¬ WP k) (sE : ∀ k, RE k → ¬ WP k) (hCl : pc + lp + 6 + lt < C.length)
    (hC18 : C.length < 2 ^ 18) :
    CapT fk tg KL C pc p nl Inv G hb E0 (fun k => RP k ∨ RT k ∨ RE k) (ifTF cmp SP ST SE) where
  stable := fun env env' sp H h => by
    simp only [ifTF]
    rw [cP.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SP env' sp H with
    | error e => rfl
    | ok r =>
      simp only [Except.bind]
      rw [cT.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inl hk))),
        cE.stable env env' sp r.2 (fun k hk => h k (Or.inr (Or.inr hk)))]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [ifTF] at hS
    rcases bind_cap hS with h1 | ⟨⟨ab, H1⟩, hSP, h2⟩
    · exact cP.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    obtain ⟨s1, env1, r1, I1, z1, p1, l1, v1, e81, F1, ag1, R1, A1, m1⟩ :=
      hP.run s env H ab H1 I0 z0 F0 O0 R0 L0 A0 (by simp [oW, hSP])
    match ab, l1, h2, hSP with
    | [a, b], _, h2, hSP =>
    dsimp only at h2
    obtain ⟨s2, env2, st2, I2, z2, x31, x8, F2, O2, R2, L2, A2, ag2, _⟩ :=
      ifPreS hI hP hH s env H a b H1 I0 z0 F0 O0 R0 L0 A0 (by simp [oW, hSP]) hCl hC18
    by_cases hc : cmpF cmp a b
    · rw [if_pos hc] at h2 st2
      have hST : ST env2 (s2.x 31).toNat H1 = .error fk := by
        rw [x31, cT.stable env2 env _ _ (fun k hk => ag2 k (sT k hk))]; exact h2
      obtain ⟨s3, r3, I3, z3⟩ := cT.cap s2 env2 H1 I2 z2 F2 O2 R2 L2 A2 hST
      exact ⟨s3, st2.trans r3, I3, z3⟩
    · rw [if_neg hc] at h2 st2
      have hSE : SE env2 (s2.x 31).toNat H1 = .error fk := by
        rw [x31, cE.stable env2 env _ _ (fun k hk => ag2 k (sE k hk))]; exact h2
      obtain ⟨s3, r3, I3, z3⟩ := cE.cap s2 env2 H1 I2 z2 F2 O2 R2 L2 A2 hSE
      exact ⟨s3, st2.trans r3, I3, z3⟩

theorem letTCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc lv p nl hb E0 k0 w : Nat} {Inv : St → Prop} {G : St → Prop} {Rv Wv Rb : Nat → Prop}
    {SV : SemWX} {SB : SemTX} (hI : InvOKH hb p Inv)
    (hv : EVHwS KL C pc lv p nl Inv hb E0 Rv Wv w (oW SV)) (cv : CapW fk tg KL C pc p nl Inv G hb E0 Rv SV)
    (hS : At C (pc + lv) (popN p k0 w)) (cb : CapT fk tg KL C (pc + lv + 3 * w) p nl Inv G hb E0 Rb SB)
    (hk0 : k0 + w ≤ nl) (hsc : ∀ k, Rb k → ¬ (k0 ≤ k ∧ k < k0 + w) → ¬ Wv k) (hnl : nl < 251) :
    CapT fk tg KL C pc p nl Inv G hb E0 (fun k => Rv k ∨ (Rb k ∧ ¬ (k0 ≤ k ∧ k < k0 + w))) (letTF k0 w SV SB) where
  stable := fun env env' sp H h => by
    simp only [letTF]
    rw [cv.stable env env' sp H (fun k hk => h k (Or.inl hk))]
    cases SV env' sp H with
    | error e => rfl
    | ok r =>
      simp only [Except.bind]
      apply cb.stable; intro k hk
      unfold setW
      split
      · rfl
      · rename_i hk'; exact h k (Or.inr ⟨hk, hk'⟩)
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS' => by
    simp only [letTF] at hS'
    rcases bind_cap hS' with h1 | ⟨⟨u, H1⟩, hSV, h2⟩
    · exact cv.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    obtain ⟨s2, env1, st2, I2, z2, x31, x8, F2, O2, R2, L2, A2, ag1, _⟩ :=
      letPreS hI hv hS hk0 hnl s env H u H1 I0 z0 F0 O0 R0 L0 A0 (by simp [oW, hSV])
    have hSB2 : SB (setW env1 k0 w u) (s2.x 31).toNat H1 = .error fk := by
      rw [x31]; rw [← h2]; apply cb.stable; intro k hk
      simp only [setW]
      by_cases e : k0 ≤ k ∧ k < k0 + w
      · simp [e]
      · simp only [e, if_false]; exact ag1 k (hsc k hk e)
    obtain ⟨s3, r3, I3, z3⟩ := cb.cap s2 _ H1 I2 z2 F2 O2 R2 L2 A2 hSB2
    exact ⟨s3, st2.trans r3, I3, z3⟩

/-! ## LOOP -/

theorem loopCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {h S len p nl hb E0 w : Nat} {Inv : St → Prop} {G : St → Prop} {RZ WZ RS WS : Nat → Prop}
    {SZ SS : SemTX} (hI : InvOKH hb p Inv)
    (hH : At C h (loopHead p ((S : Int) - ((h + 2 : Nat) : Int)))) (hD : At C S (loopDec p))
    (hSt : EVHtS KL C (S + 2) p nl Inv hb E0 RS WS w (h + len) h (oT SS))
    (cZ : CapT fk tg KL C (h + 3) p nl Inv G hb E0 RZ SZ) (cS : CapT fk tg KL C (S + 2) p nl Inv G hb E0 RS SS)
    (hk : fk ≠ .stuck) (hp : 1 ≤ p) (hpn : p ≤ nl) (hWp : ∀ k, (WZ k ∨ WS k) → p ≤ k) (hsc : ∀ k, (RZ k ∨ RS k) → ¬ (WZ k ∨ WS k))
    (hnl : nl < 251) (hSC : S + 2 ≤ C.length) (hhC : h + 3 ≤ C.length) (hC18 : C.length < 2 ^ 18) :
    ∀ n (env_s env_m : Env) (s : St) (H : Hp), Inv s → s.x 0 = 0 →
      Frame p nl s env_m → FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → HAl H →
      (∀ k, ¬ (WZ k ∨ WS k) → env_m k = env_s k) →
      loopGoF p SZ SS (s.x 31).toNat n env_s H = .error fk →
      ∃ s', SStarX KL C (h, s) (tg, s') ∧ G s' ∧ s'.x 0 = 0 := by
  have c0 := hH.at 0 (by simp [loopHead]); have c1 := hH.at 1 (by simp [loopHead])
  have c2 := hH.at 2 (by simp [loopHead])
  have d0 := hD.at 0 (by simp [loopDec]); have d1 := hD.at 1 (by simp [loopDec])
  simp only [loopHead, loopDec, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 d0 d1
  have n0 : ¬ (WZ 0 ∨ WS 0) := fun h0 => by have := hWp 0 h0; omega
  -- facts about writing t0 (x5)
  have w5 : ∀ (s : St) (v : UInt64), Inv s → Inv (CallProbe.wr s 5 v) ∧ (CallProbe.wr s 5 v).x 0 = s.x 0 ∧ (CallProbe.wr s 5 v).x 8 = s.x 8 ∧
      (CallProbe.wr s 5 v).x 31 = s.x 31 ∧ (CallProbe.wr s 5 v).x 30 = s.x 30 ∧ (CallProbe.wr s 5 v).m = s.m ∧ (CallProbe.wr s 5 v).x 5 = v := by
    intro s v I
    have e : CallProbe.wr s 5 v = { s with x := upd s.x 5 v } := by simp [CallProbe.wr]
    rw [e]
    exact ⟨hI s _ I (by simp [upd]) (by simp [upd]) (by simp [upd]) rfl (fun _ _ => rfl), by simp [upd], by simp [upd],
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
  have zc : ∀ (env_s env_m : Env) (s : St) (H : Hp), Inv s → s.x 0 = 0 →
      Frame p nl s env_m → FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → HAl H →
      (∀ k, ¬ (WZ k ∨ WS k) → env_m k = env_s k) →
      env_s 0 = 0 → (SZ env_s (s.x 31).toNat H).bind exitOnlyF = .error fk →
      ∃ s', SStarX KL C (h, s) (tg, s') ∧ G s' ∧ s'.x 0 = 0 := by
    intro env_s env_m s H I0 z0 F0 O0 R0 L0 A0 ag hz hS
    rcases bind_cap hS with hS | ⟨⟨r, H1⟩, _, e⟩
    rotate_left
    · rcases r with u | u <;> simp [exitOnlyF] at e; exact (hk e.symm).elim
    have e0 : env_m 0 = 0 := by rw [ag 0 n0, hz]
    obtain ⟨I1, z1, x81, x311, x301, m1, x51⟩ := w5 s (env_m 0) I0
    have st1 : CallProbe.step C (h, s) = some (h + 1, CallProbe.wr s 5 (env_m 0)) := by
      simp [CallProbe.step, c0, fuel s env_m F0]
    have x50 : (CallProbe.wr s 5 (env_m 0)).x 5 = (CallProbe.wr s 5 (env_m 0)).x 0 := by rw [x51, z1, z0, e0]
    have st2 : CallProbe.step C (h + 1, CallProbe.wr s 5 (env_m 0)) = some (h + 3, CallProbe.wr s 5 (env_m 0)) := by
      simp [CallProbe.step, c1, x50]; omega
    have F1 : Frame p nl (CallProbe.wr s 5 (env_m 0)) env_m := by intro k hk; rw [m1, x81]; exact F0 k hk
    have O1 : FrameOK p nl (CallProbe.wr s 5 (env_m 0)) := by unfold FrameOK; rw [x81, x311]; exact O0
    have R1 : HRel hb (CallProbe.wr s 5 (env_m 0)) H :=
      HRel_stack R0 x301 (by rw [x311]; exact R0.2.2.1) (fun a _ _ => by rw [m1])
    have hS' : SZ env_m ((CallProbe.wr s 5 (env_m 0)).x 31).toNat H = .error fk := by
      rw [x311, cZ.stable env_m env_s _ _ (fun k hk => ag k (hsc k (Or.inl hk)))]; exact hS
    have L1 : Lay KL hb E0 p (CallProbe.wr s 5 (env_m 0)) := L0.post' x81 (wr_b _ _ _) (by rw [x311])
    obtain ⟨s', r', I', z'⟩ := cZ.cap _ env_m H I1 (by rw [z1, z0]) F1 O1 R1 L1 A0 hS'
    exact ⟨s', .head (sx1 s H O0 R0 L0) st1 (.head (sx2 _) st2 r'), I', z'⟩
  intro n
  induction n with
  | zero =>
    intro env_s env_m s H I0 z0 F0 O0 R0 L0 A0 ag hS
    by_cases hz : env_s 0 = 0
    · simp only [loopGoF, hz, if_true] at hS
      exact zc env_s env_m s H I0 z0 F0 O0 R0 L0 A0 ag hz hS
    · simp [loopGoF, hz] at hS; exact (hk hS.symm).elim
  | succ n ih =>
    intro env_s env_m s H I0 z0 F0 O0 R0 L0 A0 ag hS
    by_cases hz : env_s 0 = 0
    · simp only [loopGoF, hz, if_true] at hS
      exact zc env_s env_m s H I0 z0 F0 O0 R0 L0 A0 ag hz hS
    simp only [loopGoF, hz, if_false] at hS
    have sx1' := sx1 s H O0 R0 L0
    have e0 : env_m 0 = env_s 0 := ag 0 n0
    have hz' : env_m 0 ≠ 0 := by rw [e0]; exact hz
    obtain ⟨o1, o2, o3⟩ := O0
    have lt64 := (s.x 31).toNat_lt
    have sp0 := hrel_sp R0
    -- head and decrement
    obtain ⟨I1, z1, x81, x311, x301, m1, x51⟩ := w5 s (env_m 0) I0
    have st1 : CallProbe.step C (h, s) = some (h + 1, CallProbe.wr s 5 (env_m 0)) := by simp [CallProbe.step, c0, fuel s env_m F0]
    have x50 : (CallProbe.wr s 5 (env_m 0)).x 5 ≠ (CallProbe.wr s 5 (env_m 0)).x 0 := by rw [x51, z1, z0]; exact hz'
    have st2 : CallProbe.step C (h + 1, CallProbe.wr s 5 (env_m 0)) = some (h + 2, CallProbe.wr s 5 (env_m 0)) := by
      simp [CallProbe.step, c1, x50]
    have st3 : CallProbe.step C (h + 2, CallProbe.wr s 5 (env_m 0)) = some (S, CallProbe.wr s 5 (env_m 0)) := by
      simp [CallProbe.step, c2, CallProbe.wr]; omega
    let v := env_m 0 - 1
    let a0 := slotAddr p (s.x 8).toNat 0
    let s4 : St := ⟨upd s.x 5 v, upd s.m a0 v, s.b⟩
    have ev : UInt64.ofNat (ea ((CallProbe.wr s 5 (env_m 0)).x 5) (-1)) = v := by rw [x51]; exact ea_dec _ hz'
    have st45 : CallProbe.run C 2 (S, CallProbe.wr s 5 (env_m 0)) = some (S + 2, s4) := by
      have q : ea ((CallProbe.wr (CallProbe.wr s 5 (env_m 0)) 5 v).x 8) (slotOff p 0) = a0 := by
        simp [CallProbe.wr, upd]; rfl
      simp only [CallProbe.run, CallProbe.step, d0, d1, ev, Option.bind_some, q]
      simp [CallProbe.wr, s4, LoopT.upd2, upd_same]
    have a0lo : (s.x 31).toNat ≤ a0 := slotAddr_ge (T := (s.x 31).toNat) o1 o2 (by omega)
    have a0hi : a0 < (s.x 8).toNat + 8 * p + 16 := slotAddr_lt (nl := nl) (by omega) (by omega)
    have I4 : Inv s4 := hI s s4 I0 (by simp [s4, upd]) (by simp [s4, upd]) (by simp [s4, upd]) rfl (fun a ha => by
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
    have sx3 : SafeX KL C (h + 2, CallProbe.wr s 5 (env_m 0)) := by simp only [SafeX, c2]; simp; omega
    have s45 : SStarX KL C (S, CallProbe.wr s 5 (env_m 0)) (S + 2, s4) := sstarX_of_run st45 (fun j hj c hc => by
      rcases j with _ | _ | j
      · simp [CallProbe.run] at hc; subst hc; simp only [SafeX, d0]; rw [x51]
        exact ⟨by decide, by decide, by decide, by decide, by omega, by omega⟩
      · simp [CallProbe.run, CallProbe.step, d0, ev] at hc; subst hc; simp only [SafeX, d1]
        refine ⟨by decide, by decide, g2, g3, ?_, ?_⟩
        · simpa [CallProbe.wr, upd] using g4
        · have q : ea ((CallProbe.wr (CallProbe.wr s 5 (env_m 0)) 5 v).x 8) (slotOff p 0) = slotAddr p (s.x 8).toNat 0 := by
            simp [CallProbe.wr, upd]; rfl
          rw [q]; exact g1
      · omega)
    have pre : SStarX KL C (h, s) (S + 2, s4) := .head sx1' st1 (.head (sx2 _) st2 (.head sx3 st3 s45))
    have L4 : Lay KL hb E0 p s4 := L0.post' x84 rfl (by rw [x314])
    have mm4 : ∀ a, a ≠ a0 → s4.m a = s.m a := fun a ha => by simp [s4, upd, ha]
    have agd : ∀ k, ¬ (WZ k ∨ WS k) → decE env_m k = decE env_s k := by
      intro k hk; simp only [decE]; split
      · rw [e0]
      · exact ag k hk
    rcases bind_cap hS with hSS | ⟨⟨r, H1⟩, hSS, hS⟩
    · have hSS' : SS (decE env_m) (s4.x 31).toNat H = .error fk := by
        rw [x314, cS.stable (decE env_m) (decE env_s) _ _ (fun k hk => agd k (hsc k (Or.inr hk)))]; exact hSS
      obtain ⟨s', r', I', z'⟩ := cS.cap s4 _ H I4 z4 F4 O4 R4 L4 A0 hSS'
      exact ⟨s', pre.trans r', I', z'⟩
    · have hSS' : oT SS (decE env_m) (s4.x 31).toNat H = some (r, H1) := by
        rw [x314]; show toO (SS _ _ _) = _
        rw [cS.stable (decE env_m) (decE env_s) _ _ (fun k hk => agd k (hsc k (Or.inr hk))), hSS]; rfl
      match r, hS, hSS' with
      | .inl u, hS, _ => simp at hS
      | .inr st, hS, hSS' =>
        obtain ⟨s5, env5, r5, I5, z5, p5, l5, e85, F5, ag5, R5, A5, m5⟩ :=
          hSt.cont s4 _ H st H1 I4 z4 F4 O4 R4 L4 A0 hSS'
        rw [x314] at p5; rw [x84] at e85
        have O5 : FrameOK p nl s5 := ⟨by rw [p5, e85]; exact o1, o2, by rw [e85]; exact o3⟩
        have ag5' : ∀ k, ¬ (WZ k ∨ WS k) → setW env5 1 (p - 1) st k = setW (decE env_s) 1 (p - 1) st k := by
          intro k hk; simp only [setW]; split
          · rfl
          · rw [ag5 k (fun w => hk (Or.inr w))]; exact agd k hk
        have hS5 : loopGoF p SZ SS (s5.x 31).toNat n (setW (decE env_s) 1 (p - 1) st) H1 = .error fk := by
          rw [p5]; exact hS
        have L5 : Lay KL hb E0 p s5 := L4.post' (by rw [e85, x84]) r5.star.b (by rw [p5, x314])
        obtain ⟨s', r', I', z'⟩ :=
          ih (setW (decE env_s) 1 (p - 1) st) (setW env5 1 (p - 1) st) s5 H1 I5 z5 F5 O5 R5 L5 A5 ag5' hS5
        exact ⟨s', (pre.trans r5).trans r', I', z'⟩


theorem loopGoF_stable {p : Nat} {SZ SS : SemTX} {R : Nat → Prop} {sp : Nat}
    (hZ : ∀ env env' sp H, (∀ k, R k → env k = env' k) → SZ env sp H = SZ env' sp H)
    (hS : ∀ env env' sp H, (∀ k, R k → env k = env' k) → SS env sp H = SS env' sp H) :
    ∀ n env env' H, (∀ k, (R k ∨ k = 0) → env k = env' k) →
      loopGoF p SZ SS sp n env H = loopGoF p SZ SS sp n env' H := by
  intro n
  induction n with
  | zero =>
    intro env env' H h
    simp only [loopGoF]; rw [h 0 (Or.inr rfl), hZ env env' sp H (fun k hk => h k (Or.inl hk))]
  | succ n ih =>
    intro env env' H h
    have hd : ∀ k, (R k ∨ k = 0) → decE env k = decE env' k := by
      intro k hk; simp only [decE]; split
      · rw [h 0 (Or.inr rfl)]
      · exact h k hk
    simp only [loopGoF]; rw [h 0 (Or.inr rfl), hS (decE env) (decE env') sp H (fun k hk => hd k (Or.inl hk))]
    split
    · rw [hZ env env' sp H (fun k hk => h k (Or.inl hk))]
    · cases SS (decE env') sp H with
      | error e => rfl
      | ok r =>
        simp only [Except.bind]
        split
        · rfl
        · apply ih; intro k hk; simp only [setW]; split
          · rfl
          · exact hd k hk

theorem loopWCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {h S len p nl hb E0 w : Nat} {Inv : St → Prop} {G : St → Prop} {RZ WZ RS WS : Nat → Prop}
    {SZ SS : SemTX} (hI : InvOKH hb p Inv)
    (hH : At C h (loopHead p ((S : Int) - ((h + 2 : Nat) : Int)))) (hD : At C S (loopDec p))
    (hSt : EVHtS KL C (S + 2) p nl Inv hb E0 RS WS w (h + len) h (oT SS))
    (cZ : CapT fk tg KL C (h + 3) p nl Inv G hb E0 RZ SZ) (cS : CapT fk tg KL C (S + 2) p nl Inv G hb E0 RS SS)
    (hk : fk ≠ .stuck) (hp : 1 ≤ p) (hpn : p ≤ nl) (hWp : ∀ k, (WZ k ∨ WS k) → p ≤ k) (hsc : ∀ k, (RZ k ∨ RS k) → ¬ (WZ k ∨ WS k))
    (hnl : nl < 251) (hSC : S + 2 ≤ C.length) (hhC : h + 3 ≤ C.length) (hC18 : C.length < 2 ^ 18) :
    CapW fk tg KL C h p nl Inv G hb E0 (fun k => RZ k ∨ RS k ∨ k = 0) (loopF p SZ SS) where
  stable := fun env env' sp H hk => by
    simp only [loopF]; rw [hk 0 (Or.inr (Or.inr rfl))]
    exact loopGoF_stable (R := fun k => RZ k ∨ RS k)
      (fun e e' sp H h => cZ.stable e e' sp H (fun k q => h k (Or.inl q)))
      (fun e e' sp H h => cS.stable e e' sp H (fun k q => h k (Or.inr q))) _ env env' H
      (fun k q => hk k (q.elim (fun q => q.elim (fun q => Or.inl q) (fun q => Or.inr (Or.inl q))) (fun q => Or.inr (Or.inr q))))
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS =>
    loopCap hI hH hD hSt cZ cS hk hp hpn hWp hsc hnl hSC hhC hC18 _ env env s H I0 z0 F0 O0 R0 L0 A0 (fun _ _ => rfl) hS


/-! ## DEF and CALL -/

/-- **CapD**: a def's semantics fails with `cap` ⇒ from its entry (as `DefXS`) a safe run to the cap stub, `IG` kept -/
structure CapD (fk : Fail) (tg : Nat) (KL : LayW) (C : List J) (f p : Nat) (IG : St → Prop) (hb E0 : Nat) (Sd : SemDX) : Prop where
  cap : ∀ (s : St) (args : List UInt64) (H : Hp) (ret : Nat), IG s → s.x 0 = 0 →
    HRel hb s H → args.length = p → (∀ i, i < p → s.m ((s.x 31).toNat + 8 * (p - 1 - i)) = args.getD i 0) →
    (s.x 31).toNat + 8 * p ≤ E0 → E0 < 2 ^ 62 → s.x 1 = UInt64.ofNat (s.b + 4 * ret) → s.b + 4 * ret < 2 ^ 64 →
    KL.lo ≤ hb → E0 ≤ KL.hi → s.b = KL.base → (s.x 31).toNat % 8 = 0 → HAl H →
    Sd args (s.x 31).toNat H = .error fk → ∃ s', SStarX KL C (f, s) (tg, s') ∧ IG s' ∧ s'.x 0 = 0

theorem defCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {f p nl hb E0 : Nat} {IG : St → Prop} {Rb : Nat → Prop} {Sb : SemWX}
    (hIG : IGOK hb E0 IG) (hP : At C f (proA 1 f (nl - p)))
    (hB : CapW fk tg KL C (f + 12) p nl (IGp IG E0 p) IG hb E0 Rb Sb)
    (hkr : fk ≠ .room) (hpn : p ≤ nl) (hR : ∀ k, Rb k → k < p) (hnl : nl < 251) :
    CapD fk tg KL C f p IG hb E0 (defSF p nl Sb) where
  cap := fun s args H ret I0 z0 R0 hl ha hE0 hE62 hx1 hret hlo hhi hbase ha31 A0 hS => by
    unfold defSF at hS
    split at hS
    rotate_left; · simp at hS; exact (hkr hS.symm).elim
    rename_i hc
    have lt64 := (s.x 31).toNat_lt
    have top0 : (s.x 30).toNat = H.top := R0.2.2.2.2.1
    have hbt : hb ≤ H.top := R0.2.1
    have wk : ∀ a, hb ≤ a → a + 8 ≤ E0 → a % 8 = 0 → wok KL a := fun a h1 h2 h3 => ⟨by omega, by omega, h3⟩
    obtain ⟨s1, hr1, h31, h8, hx, hm1⟩ := pro_srun (K := KL) (s := s) hP (by omega) (by rw [top0]; exact hc) (by omega)
      (wk _ (by omega) (by omega) (by omega)) (wk _ (by omega) (by omega) (by omega))
    -- the frame
    let env1 : Env := fun k => s1.m (slotAddr p ((s.x 31).toNat - 16) k)
    have F1 : Frame p nl s1 env1 := by intro k hk; show s1.m (slotAddr p (s1.x 8).toNat k) = _; rw [h8]
    have O1 : FrameOK p nl s1 := ⟨by rw [h31, h8]; omega, hpn, by rw [h8]; omega⟩
    have m1 : ∀ a, a ≠ (s.x 31).toNat - 8 → a ≠ (s.x 31).toNat - 16 → s1.m a = s.m a := by
      intro a h1 h2; rw [hm1, upd_other _ _ h2, upd_other _ _ h1]
    have b1 : s1.b = s.b := hr1.star.b
    have I1 : IGp IG E0 p s1 := by
      refine ⟨hIG s s1 I0 (hx 28 (by decide) (by decide)) (hx 29 (by decide) (by decide)) b1 (fun a ha => ?_), ?_⟩
      · apply m1 <;> intro e <;> apply ha <;> have := R0.2.1 <;> omega
      · rw [h8]; omega
    have z1 : s1.x 0 = 0 := by rw [hx 0 (by decide) (by decide), z0]
    have R1 : HRel hb s1 H := HRel_stack R0 (hx 30 (by decide) (by decide)) (by rw [h31]; omega)
      (fun a _ h2 => m1 a (by omega) (by omega))
    have L1 : Lay KL hb E0 p s1 :=
      ⟨hlo, hhi, by rw [b1, hbase], by rw [h8]; omega, by rw [h31]; omega, by rw [h8]; omega⟩
    have hS1 : Sb env1 (s1.x 31).toNat H = .error fk := by
      rw [h31, ← hS]; apply hB.stable; intro k hk
      have hkp := hR k hk
      simp only [env1, argEnv, hkp, if_true]
      rw [slotAddr_param hkp, m1 _ (by omega) (by omega), ← ha k hkp]; congr 1; omega
    obtain ⟨s2, r2, I2, z2⟩ := hB.cap s1 env1 H I1 z1 F1 O1 R1 L1 A0 hS1
    exact ⟨s2, (SStarX.of hr1).trans r2, I2, z2⟩

theorem callCap {KL : LayW} {fk : Fail} {tg : Nat} {C : List J} {pc la p nl pa f hb E0 : Nat} {IG : St → Prop} {RA WA : Nat → Prop}
    {SA : SemWX} {Sd : SemDX} {off : Int}
    (hIG : IGOK hb E0 IG) (hA : EVHwS KL C pc la p nl (IGp IG E0 p) hb E0 RA WA pa (oW SA))
    (cA : CapW fk tg KL C pc p nl (IGp IG E0 p) IG hb E0 RA SA)
    (hj : C[pc + la]? = some (.jal 1 off)) (hf : ((pc + la : Nat) : Int) + off = (f : Int))
    (hD : CapD fk tg KL C f pa IG hb E0 Sd) (hE62 : E0 < 2 ^ 62)
    (hcb : ∀ s, IG s → s.b + 4 * (pc + la + 1) < 2 ^ 64) (hfl : f < C.length) (hC18 : C.length < 2 ^ 18) :
    CapW fk tg KL C pc p nl (IGp IG E0 p) IG hb E0 RA (callF pa SA Sd) where
  stable := fun env env' sp H h => by
    simp only [callF]; rw [cA.stable env env' sp H h]
  cap := fun s env H I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [callF] at hS
    rcases bind_cap hS with h1 | ⟨⟨u, H1⟩, hSA, hSd⟩
    · exact cA.cap s env H I0 z0 F0 O0 R0 L0 A0 h1
    obtain ⟨s1, env1, r1, I1, z1, p1, lu, v1, e81, F1, ag1, R1, A1, m1⟩ :=
      hA.run s env H u H1 I0 z0 F0 O0 R0 L0 A0 (by simp [oW, hSA])
    obtain ⟨o1, o2, o3⟩ := O0
    have sp1 : 16 ≤ (s1.x 31).toNat := hrel_sp R1
    have hpcl : pc + la < C.length := by
      rcases Nat.lt_or_ge (pc + la) C.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hj; cases hj
    have hf' : (((pc + la : Nat) : Int) + off).toNat = f := by rw [hf]; simp
    let sj := CallProbe.wr s1 1 (UInt64.ofNat (s1.b + 4 * (pc + la + 1)))
    have stj : CallProbe.step C (pc + la, s1) = some (f, sj) := by rw [s_jal hj, hf']
    have saj : SafeX KL C (pc + la, s1) := by
      simp only [SafeX, hj]; refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> omega
    have ej : sj = { s1 with x := upd s1.x 1 (UInt64.ofNat (s1.b + 4 * (pc + la + 1))) } := by simp [sj, CallProbe.wr]
    have jx : ∀ i, i ≠ 1 → sj.x i = s1.x i := by intro i hi; rw [ej]; simp [upd, hi]
    have jm : sj.m = s1.m := by rw [ej]
    have jb : sj.b = s1.b := by rw [ej]
    have b1 : s1.b = s.b := r1.star.b
    have L1 : Lay KL hb E0 p s1 := L0.post e81 b1 p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    have Ij : IG sj := hIG s1 sj I1.1 (jx 28 (by decide)) (jx 29 (by decide)) jb (fun a _ => by rw [jm])
    have Rj : HRel hb sj H1 := HRel_stack R1 (jx 30 (by decide)) (by rw [jx 31 (by decide)]; exact R1.2.2.1)
      (fun a _ _ => by rw [jm])
    have j31 : (sj.x 31).toNat = (s.x 31).toNat - 8 * pa := by rw [jx 31 (by decide), p1]
    have hargs : ∀ i, i < pa → sj.m ((sj.x 31).toNat + 8 * (pa - 1 - i)) = u.getD i 0 := by
      intro i hi; rw [jm, j31, show (s.x 31).toNat - 8 * pa + 8 * (pa - 1 - i) = (s.x 31).toNat - 8 * (i + 1) by omega]
      exact v1 i hi
    have htop : (sj.x 31).toNat + 8 * pa ≤ E0 := by have := I0.2; rw [j31]; omega
    have hx1 : sj.x 1 = UInt64.ofNat (sj.b + 4 * (pc + la + 1)) := by rw [ej]; simp [upd]
    have hret : sj.b + 4 * (pc + la + 1) < 2 ^ 64 := by rw [jb, b1]; exact hcb s I0.1
    have hSd' : Sd u (sj.x 31).toNat H1 = .error fk := by rw [j31]; exact hSd
    have ja : (sj.x 31).toNat % 8 = 0 := by rw [jx 31 (by decide)]; exact L1.a31
    obtain ⟨s', st', I', z'⟩ :=
      hD.cap sj u H1 (pc + la + 1) Ij (by rw [jx 0 (by decide), z1]) Rj lu hargs htop hE62 hx1 hret L0.lo L0.hi
        (by rw [jb, b1, L0.base]) ja A1 hSd'
    exact ⟨s', r1.trans (.head saj stj st'), I', z'⟩

end Templates
