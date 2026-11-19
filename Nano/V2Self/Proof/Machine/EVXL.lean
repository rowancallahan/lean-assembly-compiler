/- Machine bridge (Opus box E): the LOOP node (Gen's CG.loop, only at a def's root) under the heap contract.
Layout: HEAD h: ld t0, fuel(s0); beq t0, x0, +2; jal STEP; zero arm Z (tail) …; STEP S: t0 −= 1; sd t0, fuel(s0);
step arm (tail).  Exits of both arms go to X = h + len (the epilogue start), CONTINUE goes back to h.
Semantics `loopS`: by recursion on the fuel (slot 0); the result is an `EVHw` value contract for the whole node. -/
import Nano.V2Self.Proof.Machine.EVXT
import Nano.V2Self.Proof.Machine.Loop
namespace Templates
open CallProbe

/-- the fuel decrement -/
def decE (env : Env) : Env := fun k => if k = 0 then env 0 - 1 else env k

def exitOnly (r : TRes × Hp) : Option (List UInt64 × Hp) :=
  match r.1 with | .inl vs => some (vs, r.2) | .inr _ => none

def loopGo (p : Nat) (SZ SS : SemT) (sp : Nat) : Nat → Env → Hp → Option (List UInt64 × Hp)
  | n, env, H =>
    if env 0 = 0 then (SZ env sp H).bind exitOnly
    else match n with
      | 0 => none
      | n + 1 => (SS (decE env) sp H).bind fun r => match r.1 with
        | .inl vs => some (vs, r.2)
        | .inr st => loopGo p SZ SS sp n (setW (decE env) 1 (p - 1) st) r.2

def loopS (p : Nat) (SZ SS : SemT) : SemW := fun env sp H => loopGo p SZ SS sp (env 0).toNat env H

def loopHead (p : Nat) (dS : Int) : List J := [.ld 5 8 (slotOff p 0), .beq 5 0 2, .jal 0 dS]
def loopDec (p : Nat) : List J := [.addi 5 5 (-1), .sd 5 8 (slotOff p 0)]

theorem loopGo_stable {p : Nat} {SZ SS : SemT} {R : Nat → Prop} {sp : Nat}
    (hZ : ∀ env env' sp H, (∀ k, R k → env k = env' k) → SZ env sp H = SZ env' sp H)
    (hS : ∀ env env' sp H, (∀ k, R k → env k = env' k) → SS env sp H = SS env' sp H) :
    ∀ n env env' H, (∀ k, (R k ∨ k = 0) → env k = env' k) → loopGo p SZ SS sp n env H = loopGo p SZ SS sp n env' H := by
  intro n
  induction n with
  | zero =>
    intro env env' H h
    simp only [loopGo]; rw [h 0 (Or.inr rfl), hZ env env' sp H (fun k hk => h k (Or.inl hk))]
  | succ n ih =>
    intro env env' H h
    have hd : ∀ k, (R k ∨ k = 0) → decE env k = decE env' k := by
      intro k hk; simp only [decE]; split
      · rw [h 0 (Or.inr rfl)]
      · exact h k hk
    simp only [loopGo]; rw [h 0 (Or.inr rfl), hS (decE env) (decE env') sp H (fun k hk => hd k (Or.inl hk))]
    split
    · rw [hZ env env' sp H (fun k hk => h k (Or.inl hk))]
    · cases SS (decE env') sp H with
      | none => rfl
      | some r =>
        simp only [Option.bind_some]
        split
        · rfl
        · apply ih; intro k hk; simp only [setW]; split
          · rfl
          · exact hd k hk

theorem ea_dec (v : UInt64) (h : v ≠ 0) : UInt64.ofNat (ea v (-1)) = v - 1 := by
  have : v.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  have lt := v.toNat_lt
  apply UInt64.toNat.inj
  have e : ea v (-1) = v.toNat - 1 := by simp [ea]; omega
  rw [e, UInt64.toNat_sub_of_le _ _ (show (1 : UInt64) ≤ v from by
    rw [UInt64.le_iff_toNat_le]; simp; omega)]
  simp; omega

/-- one loop pass from HEAD, by induction on the recursion bound `n`; `env_m` (the machine frame) agrees with the
semantic environment `env_s` off the arms' lets -/
theorem loop_pass {C : List J} {h S len p nl hb w : Nat} {Inv : St → Prop} {RZ WZ RS WS : Nat → Prop} {SZ SS : SemT}
    (hI : InvOKH hb p Inv)
    (hH : At C h (loopHead p ((S : Int) - ((h + 2 : Nat) : Int)))) (hD : At C S (loopDec p))
    (hZ : EVHt C (h + 3) p nl Inv hb RZ WZ w (h + len) h SZ)
    (hSt : EVHt C (S + 2) p nl Inv hb RS WS w (h + len) h SS)
    (hp : 1 ≤ p) (hpn : p ≤ nl) (hWp : ∀ k, (WZ k ∨ WS k) → p ≤ k) (hsc : ∀ k, (RZ k ∨ RS k) → ¬ (WZ k ∨ WS k)) :
    ∀ n (env_s env_m : Env) (s : St) (H : Hp) (vs : List UInt64) (H' : Hp), Inv s → s.x 0 = 0 →
      Frame p nl s env_m → FrameOK p nl s → HRel hb s H → (∀ k, ¬ (WZ k ∨ WS k) → env_m k = env_s k) →
      loopGo p SZ SS (s.x 31).toNat n env_s H = some (vs, H') →
      ∃ s' env', Star C (h, s) (h + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
        vs.length = w ∧ (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
        Frame p nl s' env' ∧ (∀ k, ¬ (WZ k ∨ WS k ∨ k < p) → env' k = env_m k) ∧ HRel hb s' H' ∧
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
    exact ⟨hI s _ I (by simp [upd]) (by simp [upd]) (by simp [upd]) rfl (fun _ _ => rfl), by simp [upd], by simp [upd],
      by simp [upd], by simp [upd], rfl, by simp [upd]⟩
  have fuel : ∀ (s : St) (env : Env), Frame p nl s env → s.m (ea (s.x 8) (slotOff p 0)) = env 0 := by
    intro s env F; exact F 0 (by omega)
  -- the zero arm
  have zc : ∀ (env_s env_m : Env) (s : St) (H : Hp) (vs : List UInt64) (H' : Hp), Inv s → s.x 0 = 0 →
      Frame p nl s env_m → FrameOK p nl s → HRel hb s H → (∀ k, ¬ (WZ k ∨ WS k) → env_m k = env_s k) →
      env_s 0 = 0 → (SZ env_s (s.x 31).toNat H).bind exitOnly = some (vs, H') →
      ∃ s' env', Star C (h, s) (h + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
        vs.length = w ∧ (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
        Frame p nl s' env' ∧ (∀ k, ¬ (WZ k ∨ WS k ∨ k < p) → env' k = env_m k) ∧ HRel hb s' H' ∧
        ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → (WZ k ∨ WS k ∨ k < p) → a ≠ slotAddr p (s.x 8).toNat k) →
          s'.m a = s.m a := by
    intro env_s env_m s H vs H' I0 z0 F0 O0 R0 ag hz hS
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
    obtain ⟨s', env', r', I', z', p', l', v', e8', F', ag', R', m'⟩ := hZ.exit _ env_m H vs H' I1 (by rw [z1, z0]) F1 O1 R1 hS'
    rw [x311] at p' v'; rw [x81] at e8'
    refine ⟨s', env', ((Star.one st1).tail st2).trans r', I', z', p', l', v', e8', F', ?_, R', ?_⟩
    · intro k hk; simp only [not_or] at hk; exact ag' k hk.1
    · intro a ha hW
      rw [m' a (by rw [x311]; exact ha) (fun k hk wk => by rw [x81]; exact hW k hk (Or.inl wk)), m1]
  intro n
  induction n with
  | zero =>
    intro env_s env_m s H vs H' I0 z0 F0 O0 R0 ag hS
    by_cases hz : env_s 0 = 0
    · simp only [loopGo, hz, if_true] at hS
      exact zc env_s env_m s H vs H' I0 z0 F0 O0 R0 ag hz hS
    · simp [loopGo, hz] at hS
  | succ n ih =>
    intro env_s env_m s H vs H' I0 z0 F0 O0 R0 ag hS
    by_cases hz : env_s 0 = 0
    · simp only [loopGo, hz, if_true] at hS
      exact zc env_s env_m s H vs H' I0 z0 F0 O0 R0 ag hz hS
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
    let s4 : St := ⟨upd s.x 5 v, upd s.m a0 v, s.b⟩
    have ev : UInt64.ofNat (ea ((wr s 5 (env_m 0)).x 5) (-1)) = v := by rw [x51]; exact ea_dec _ hz'
    have st45 : run C 2 (S, wr s 5 (env_m 0)) = some (S + 2, s4) := by
      have q : ea ((wr (wr s 5 (env_m 0)) 5 v).x 8) (slotOff p 0) = a0 := by
        simp [wr, upd]; rfl
      simp only [run, step, d0, d1, ev, Option.bind_some, q]
      simp [wr, s4, LoopT.upd2, upd_same]
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
    have pre : Star C (h, s) (S + 2, s4) := (((Star.one st1).tail st2).tail st3).trans (run_star st45)
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
      obtain ⟨s', env', r', I', z', p', l', v', e8', F', ag', R', m'⟩ := hSt.exit s4 _ H vs H' I4 z4 F4 O4 R4 hSS'
      rw [x314] at p' v'; rw [x84] at e8'
      refine ⟨s', env', pre.trans r', I', z', p', l', v', e8', F', ?_, R', ?_⟩
      · intro k hk; simp only [not_or] at hk
        rw [ag' k hk.2.1]; simp only [decE, show k ≠ 0 by omega, if_false]
      · intro a ha hW
        rw [m' a (by rw [x314]; exact ha) (fun k hk wk => by rw [x84]; exact hW k hk (Or.inr (Or.inl wk)))]
        exact mm4 a (hW 0 (by omega) (Or.inr (Or.inr hp)))
    | .inr st, hS, hSS' =>
      obtain ⟨s5, env5, r5, I5, z5, p5, l5, e85, F5, ag5, R5, m5⟩ := hSt.cont s4 _ H st H1 I4 z4 F4 O4 R4 hSS'
      rw [x314] at p5; rw [x84] at e85
      have O5 : FrameOK p nl s5 := ⟨by rw [p5, e85]; exact o1, o2, by rw [e85]; exact o3⟩
      have ag5' : ∀ k, ¬ (WZ k ∨ WS k) → setW env5 1 (p - 1) st k = setW (decE env_s) 1 (p - 1) st k := by
        intro k hk; simp only [setW]; split
        · rfl
        · rw [ag5 k (fun w => hk (Or.inr w))]; exact agd k hk
      have hS5 : loopGo p SZ SS (s5.x 31).toNat n (setW (decE env_s) 1 (p - 1) st) H1 = some (vs, H') := by
        rw [p5]; exact hS
      obtain ⟨s', env', r', I', z', p', l', v', e8', F', ag', R', m'⟩ :=
        ih (setW (decE env_s) 1 (p - 1) st) (setW env5 1 (p - 1) st) s5 H1 vs H' I5 z5 F5 O5 R5 ag5' hS5
      rw [p5] at p' v'; rw [e85] at e8'
      refine ⟨s', env', (pre.trans r5).trans r', I', z', p', l', v', e8', F', ?_, R', ?_⟩
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
theorem loopX {C : List J} {h S len p nl hb w : Nat} {Inv : St → Prop} {RZ WZ RS WS : Nat → Prop} {SZ SS : SemT}
    (hI : InvOKH hb p Inv)
    (hH : At C h (loopHead p ((S : Int) - ((h + 2 : Nat) : Int)))) (hD : At C S (loopDec p))
    (hZ : EVHt C (h + 3) p nl Inv hb RZ WZ w (h + len) h SZ)
    (hSt : EVHt C (S + 2) p nl Inv hb RS WS w (h + len) h SS)
    (hp : 1 ≤ p) (hpn : p ≤ nl) (hWp : ∀ k, (WZ k ∨ WS k) → p ≤ k) (hsc : ∀ k, (RZ k ∨ RS k) → ¬ (WZ k ∨ WS k)) :
    EVHw C h len p nl Inv hb (fun k => RZ k ∨ RS k ∨ k = 0) (fun k => WZ k ∨ WS k ∨ k < p) w (loopS p SZ SS) where
  stable := fun env env' sp H hk => by
    simp only [loopS]; rw [hk 0 (Or.inr (Or.inr rfl))]
    exact loopGo_stable (R := fun k => RZ k ∨ RS k)
      (fun e e' sp H h => hZ.stable e e' sp H (fun k q => h k (Or.inl q)))
      (fun e e' sp H h => hSt.stable e e' sp H (fun k q => h k (Or.inr q))) _ env env' H
      (fun k q => hk k (q.elim (fun q => q.elim (fun q => Or.inl q) (fun q => Or.inr (Or.inl q))) (fun q => Or.inr (Or.inr q))))
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS =>
    loop_pass hI hH hD hZ hSt hp hpn hWp hsc _ env env s H vs H' I0 z0 F0 O0 R0 (fun _ _ => rfl) hS

end Templates
