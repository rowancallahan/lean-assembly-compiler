/- Machine bridge (Opus box E): the LOOP node (Gen's CG.loop, only at a def's root), semantics and templates.
Layout: HEAD h: ld t0, fuel(s0); beq t0, x0, +2; jal STEP; zero arm Z (tail) …; STEP S: t0 −= 1; sd t0, fuel(s0);
step arm (tail).  Exits of both arms go to X = h + len (the epilogue start), CONTINUE goes back to h.
Semantics `loopS`: by recursion on the fuel (slot 0).  The run theorem is `loopXS` (EVSLoop.lean). -/
import Nano.Run.EVXT
import Nano.Run.Loop
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

end Templates
