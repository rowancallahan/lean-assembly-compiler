/- LOOP / CONTINUE (Astra-11, Opus box): Gen's fuel loop on the abstract machine J, by induction on the fuel.
Layout (g36 LOOP + g37 items 11/10): HEAD: ld t0, fuel(s0); beq t0, x0, +2; jal STEP; zero arm …(exits to E);
STEP: addi t0, t0, −1; sd t0, fuel(s0); step arm …(exits to E, or CONTINUE: new state into the slots, jal HEAD).
Everything about the arms is abstract: `P env s` is the loop-head invariant (frame holds env, fuel cell = env 0,
x0 = 0, …), the arms' results are relations `QZ`, `QS`, and CONTINUE's state change is a relation `Cont` that keeps
the (already decremented) fuel.  The result `LoopR` is the loop's semantics as an inductive relation. -/
import Nano.Run.Call

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

end LoopT
