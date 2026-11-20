/- LOOP / CONTINUE (Astra-11, Opus box): Gen's fuel loop on the abstract machine J, by induction on the fuel.
Layout (g36 LOOP + g37 items 11/10): HEAD: ld t0, fuel(s0); beq t0, x0, +2; jal STEP; zero arm …(exits to E);
STEP: addi t0, t0, −1; sd t0, fuel(s0); step arm …(exits to E, or CONTINUE: new state into the slots, jal HEAD).
Everything about the arms is abstract: `P env s` is the loop-head invariant (frame holds env, fuel cell = env 0,
x0 = 0, …), the arms' results are relations `QZ`, `QS`, and CONTINUE's state change is a relation `Cont` that keeps
the (already decremented) fuel.  The result `LoopR` is the loop's semantics as an inductive relation. -/
import Nano.V2Self.Proof.Machine.Call

namespace LoopT
open CallProbe

abbrev Env := Nat → UInt64

theorem upd2 {α} (f : Nat → α) (k : Nat) (a b : α) : upd (upd f k a) k b = upd f k b := by
  funext i; by_cases h : i = k <;> simp [upd, h]

/-- the fuel decrement STEP performs -/
def dec (env : Env) : Env := upd env 0 (UInt64.ofNat (ea (env 0) (-1)))

inductive LoopR (QZ QS : Env → St → Prop) (Cont : Env → Env → Prop) : Env → St → Prop
  | zero {env s'} : env 0 = 0 → QZ env s' → LoopR QZ QS Cont env s'
  | exit {env s'} : env 0 ≠ 0 → QS (dec env) s' → LoopR QZ QS Cont env s'
  | cont {env env' s'} : env 0 ≠ 0 → Cont (dec env) env' → LoopR QZ QS Cont env' s' → LoopR QZ QS Cont env s'

def head (off0 : Int) (dS : Int) : List J := [.ld 5 8 off0, .beq 5 0 2, .jal 0 dS]
def stepPre (off0 : Int) : List J := [.addi 5 5 (-1), .sd 5 8 off0]

/-- **the loop**: from HEAD with the invariant, the loop reaches E with `LoopR` -/
theorem loop_ok {C : List J} {H S E : Nat} {off0 dS : Int} {P : Env → St → Prop} {QZ QS : Env → St → Prop}
    {Cont : Env → Env → Prop}
    (hH : At C H (head off0 dS)) (hdS : ((H : Int) + 2 + dS).toNat = S) (hP : At C S (stepPre off0))
    (fuel : ∀ env s, P env s → s.m (ea (s.x 8) off0) = env 0 ∧ s.x 0 = 0)
    (hDec : ∀ env s, P env s → env 0 ≠ 0 →
      P (dec env) ⟨upd s.x 5 (UInt64.ofNat (ea (env 0) (-1))), upd s.m (ea (s.x 8) off0) (UInt64.ofNat (ea (env 0) (-1))), s.b, s.wk⟩)
    (hZ : ∀ env s, P env s → env 0 = 0 → ∃ s', Star C (H + 3, wr s 5 (env 0)) (E, s') ∧ QZ env s')
    (hS : ∀ env s, P env s → ∃ s', (Star C (S + 2, s) (E, s') ∧ QS env s') ∨
      ∃ env', Star C (S + 2, s) (H, s') ∧ Cont env env' ∧ P env' s')
    (hC : ∀ env env', Cont env env' → env' 0 = env 0) :
    ∀ k env s, P env s → (env 0).toNat = k → ∃ s', Star C (H, s) (E, s') ∧ LoopR QZ QS Cont env s' := by
  intro k
  induction k with
  | zero =>
    intro env s hp hk
    have h0 : env 0 = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    obtain ⟨hf, hx0⟩ := fuel env s hp
    have c0 := hH.at 0 (by simp [head]); have c1 := hH.at 1 (by simp [head])
    simp [head] at c0 c1
    have r1 : step C (H, s) = some (H + 1, wr s 5 (env 0)) := by simp [step, c0, hf]
    have r2 : step C (H + 1, wr s 5 (env 0)) = some (H + 3, wr s 5 (env 0)) := by
      simp [step, c1, wr, upd, hx0, h0]; try omega
    obtain ⟨s', rz, qz⟩ := hZ env s hp h0
    exact ⟨s', ((Star.one r1).tail r2).trans rz, .zero h0 qz⟩
  | succ k ih =>
    intro env s hp hk
    have h0 : env 0 ≠ 0 := fun e => by rw [e] at hk; simp at hk
    obtain ⟨hf, hx0⟩ := fuel env s hp
    have c0 := hH.at 0 (by simp [head]); have c1 := hH.at 1 (by simp [head]); have c2 := hH.at 2 (by simp [head])
    simp [head] at c0 c1 c2
    have d0 := hP.at 0 (by simp [stepPre]); have d1 := hP.at 1 (by simp [stepPre])
    simp [stepPre] at d0 d1
    let s1 := wr s 5 (env 0)
    have r1 : step C (H, s) = some (H + 1, s1) := by simp [step, c0, hf, s1]
    have r2 : step C (H + 1, s1) = some (H + 2, s1) := by
      simp [step, c1, s1, wr, upd, hx0, h0]
    let s2 := wr s1 0 (UInt64.ofNat (s1.b + s1.w * (H + 2 + 1)))
    have w2 : s2 = s1 := by simp [s2, wr]
    have r3 : step C (H + 2, s1) = some (S, s1) := by
      have := (show step C (H + 2, s1) = some (((H + 2 : Nat) : Int) + dS |>.toNat, s2) by simp [step, c2, s2])
      rw [w2] at this; rw [this]; congr 2; try omega
    let v := UInt64.ofNat (ea (env 0) (-1))
    let s4 : St := ⟨upd s.x 5 v, upd s.m (ea (s.x 8) off0) v, s.b, s.wk⟩
    have r45 : run C 2 (S, s1) = some (S + 2, s4) := by
      simp [run, step, d0, d1, s1, wr, s4, v, upd_same, upd_other _ _ (show (8:Nat) ≠ 5 by decide), upd2]
    have hp4 := hDec env s hp h0
    have hk4 : ((dec env) 0).toNat = k := by
      have : (env 0).toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
      have := (env 0).toNat_lt
      simp [dec, upd, ea]; omega
    have pre : Star C (H, s) (S + 2, s4) := (((Star.one r1).tail r2).tail r3).trans (run_star r45)
    obtain ⟨s', hs⟩ := hS (dec env) s4 hp4
    rcases hs with ⟨rs, qs⟩ | ⟨env', rs, cont, hp'⟩
    · exact ⟨s', pre.trans rs, .exit h0 qs⟩
    · obtain ⟨s'', r'', lr⟩ := ih env' s' hp' (by rw [hC _ _ cont]; exact hk4)
      exact ⟨s'', (pre.trans rs).trans r'', .cont h0 cont lr⟩

end LoopT
