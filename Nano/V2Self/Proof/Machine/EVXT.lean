/- Machine bridge (Opus box E): TAIL mode (loop arms, Gen's CT), semantics only.  A tail fragment either EXITS
(`.inl vs`: pushes the result words and jumps to the def's epilogue) or CONTINUEs (`.inr st`: new loop state, jump to the
loop head).  Here: the result type `TRes`/`SemT` and the semantics combinators `exitS`, `contS`, `ifTS`, `letTS`.
The run theorems are the safe ones in EVSTail.lean (`valT`, `contT`, `ifT`, `letT`; contract `EVHtS` in EVSDefs.lean). -/
import Nano.V2Self.Proof.Machine.EVX
namespace Templates
open CallProbe

/-- a tail result: `.inl vs` exit with vs, `.inr st` continue with the new state st -/
abbrev TRes := List UInt64 ⊕ List UInt64
abbrev SemT := Env → Nat → Hp → Option (TRes × Hp)

def exitS (S : SemW) : SemT := fun env sp H => (S env sp H).map fun r => (.inl r.1, r.2)
def contS (S : SemW) : SemT := fun env sp H => (S env sp H).map fun r => (.inr r.1, r.2)

def ifTS (cmp : Nat) (SP : SemW) (ST SE : SemT) : SemT :=
  fun env sp H => (SP env sp H).bind fun r => match r.1 with
    | [a, b] => if cmpF cmp a b then ST env sp r.2 else SE env sp r.2
    | _ => none

def letTS (k0 w : Nat) (SV : SemW) (SB : SemT) : SemT :=
  fun env sp H => (SV env sp H).bind fun r => SB (setW env k0 w r.1) sp r.2

theorem setW_agree {env env1 : Env} {k0 w : Nat} {u : List UInt64} {Rb Wv : Nat → Prop}
    (ag1 : ∀ k, ¬ Wv k → env1 k = env k) (hsc : ∀ k, Rb k → ¬ (k0 ≤ k ∧ k < k0 + w) → ¬ Wv k) :
    ∀ k, Rb k → setW env1 k0 w u k = setW env k0 w u k := by
  intro k hk; simp only [setW]
  by_cases e : k0 ≤ k ∧ k < k0 + w
  · simp [e]
  · simp only [e, if_false]; exact ag1 k (hsc k hk e)

end Templates
