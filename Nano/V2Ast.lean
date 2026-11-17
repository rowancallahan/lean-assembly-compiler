/- nano v2, increments 1 and 2: the AST and meaning (DRAFT spec, owner confirms).  v1's `Ex` plus ONE construct:
`if a ⋈ b then t else e` with `⋈` one of `==`, `<`, `<=`; `<`/`<=` are unsigned in a `UInt64` file and signed in an
`Int64` file (the elaborator picks the kind).  Values stay 64-bit words; a comparison is never a value.
Increment 2: `&&&`, `|||`, `^^^` and shifts by a numeral `< 64` (Lean's `UInt64` operations). -/
import Nano.Ast

namespace Nano.V2

/-- the comparison of an `if` -/
inductive Cmp where
  | eq | ltu | leu | lts | les
  deriving DecidableEq, Repr

/-- Lean's meaning of the comparison on the words (`lts`/`les`: on the `Int64` with the same bits) -/
def Cmp.test : Cmp → UInt64 → UInt64 → Bool
  | .eq, a, b => a == b
  | .ltu, a, b => decide (a < b)
  | .leu, a, b => decide (a ≤ b)
  | .lts, a, b => decide (a.toInt64 < b.toInt64)
  | .les, a, b => decide (a.toInt64 ≤ b.toInt64)

/-- bitwise operations (increment 2) -/
inductive BOp where
  | and | or | xor
  deriving DecidableEq, Repr

def BOp.app : BOp → UInt64 → UInt64 → UInt64
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

inductive E where
  | num (n : UInt64) | var (i : Nat)
  | add (a b : E) | sub (a b : E) | mul (a b : E)
  | let_ (v b : E)
  | call (body args : E)
  | anil | acons (e rest : E)
  | ite (k : Cmp) (a b t e : E)
  | bit (o : BOp) (a b : E)               -- increment 2: `&&&`, `|||`, `^^^`
  | sh (left : Bool) (k : Nat) (a : E)    -- increment 2: `a <<< k`, `a >>> k`, `k` a numeral `< 64`
  deriving DecidableEq, Repr

abbrev Prog := Nat × E

mutual
def den : E → List UInt64 → UInt64
  | .num n, _ => n
  | .var i, env => env.getD i 0
  | .add a b, env => den a env + den b env
  | .sub a b, env => den a env - den b env
  | .mul a b, env => den a env * den b env
  | .let_ v b, env => den b (den v env :: env)
  | .call b as, env => den b (denA as env).reverse
  | .anil, _ => 0
  | .acons _ _, _ => 0
  | .ite k a b t e, env => if k.test (den a env) (den b env) then den t env else den e env
  | .bit o a b, env => o.app (den a env) (den b env)
  | .sh l k a, env => if l then den a env <<< k.toUInt64 else den a env >>> k.toUInt64
def denA : E → List UInt64 → List UInt64
  | .acons e r, env => den e env :: denA r env
  | _, _ => []
end

def Prog.eval (p : Prog) (args : List UInt64) : Option UInt64 :=
  if args.length = p.1 then some (den p.2 args.reverse) else none

/-! ## v1 embeds -/

def ofEx : Nano.Ex → E
  | .num n => .num n | .var i => .var i
  | .add a b => .add (ofEx a) (ofEx b) | .sub a b => .sub (ofEx a) (ofEx b) | .mul a b => .mul (ofEx a) (ofEx b)
  | .let_ v b => .let_ (ofEx v) (ofEx b) | .call b as => .call (ofEx b) (ofEx as)
  | .anil => .anil | .acons e r => .acons (ofEx e) (ofEx r)

mutual
theorem den_ofEx : ∀ (e : Nano.Ex) (env : List UInt64), den (ofEx e) env = Nano.den e env
  | .num _, _ => rfl
  | .var _, _ => rfl
  | .add a b, env => by simp only [ofEx, den, Nano.den, den_ofEx a, den_ofEx b]
  | .sub a b, env => by simp only [ofEx, den, Nano.den, den_ofEx a, den_ofEx b]
  | .mul a b, env => by simp only [ofEx, den, Nano.den, den_ofEx a, den_ofEx b]
  | .let_ v b, env => by simp only [ofEx, den, Nano.den, den_ofEx v, den_ofEx b]
  | .call b as, env => by simp only [ofEx, den, Nano.den, denA_ofEx as, den_ofEx b]
  | .anil, _ => rfl
  | .acons _ _, _ => rfl
theorem denA_ofEx : ∀ (e : Nano.Ex) (env : List UInt64), denA (ofEx e) env = Nano.denA e env
  | .acons e r, env => by simp only [ofEx, denA, Nano.denA, den_ofEx e, denA_ofEx r]
  | .num _, _ => rfl | .var _, _ => rfl | .add _ _, _ => rfl | .sub _ _, _ => rfl | .mul _ _, _ => rfl
  | .let_ _ _, _ => rfl | .call _ _, _ => rfl | .anil, _ => rfl
end

/-- **v1 programs mean the same in v2** -/
theorem eval_ofEx (p : Nano.Prog) (args : List UInt64) : Prog.eval (p.1, ofEx p.2) args = p.eval args := by
  simp [Prog.eval, Nano.Prog.eval, den_ofEx]

end Nano.V2
