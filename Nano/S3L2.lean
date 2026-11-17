/- **nano → S3, link 2: A-normal form** (`Testing/notes/NANO_S3.md`).

L2 = L1 where the operands of an arithmetic operation are variables: `num`, `var`, `bin o i j` (`o` ∈ add/sub/mul,
operands variables `i`, `j`), `let_`.  The ONE construct changed: compound operands become `let`-bound intermediates
(the three operator constructors become one `bin` over variables).  `tr2 (a ⊕ b) = let x := a; let y := b↑; x ⊕ y`.
Theorem: `tr2_eval : (tr2P p).eval args = p.eval args`. -/
import Nano.S3L1

namespace Nano.S3

inductive Bop where | add | sub | mul
  deriving DecidableEq, Repr

def Bop.eval : Bop → UInt64 → UInt64 → UInt64
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

inductive A where
  | num (n : UInt64) | var (i : Nat)
  | bin (o : Bop) (i j : Nat)
  | let_ (v b : A)
  deriving DecidableEq, Repr

def den2 : A → List UInt64 → UInt64
  | .num n, _ => n
  | .var i, env => env.getD i 0
  | .bin o i j, env => o.eval (env.getD i 0) (env.getD j 0)
  | .let_ v b, env => den2 b (den2 v env :: env)

abbrev Prog2 := Nat × A

def Prog2.eval (p : Prog2) (args : List UInt64) : Option UInt64 :=
  if args.length = p.1 then some (den2 p.2 args.reverse) else none

def shv (d c i : Nat) : Nat := if i < c then i else i + d

/-- variables `≥ c` move up by `d` -/
def A.shift (d : Nat) : Nat → A → A
  | _, .num n => .num n
  | c, .var i => .var (shv d c i)
  | c, .bin o i j => .bin o (shv d c i) (shv d c j)
  | c, .let_ v b => .let_ (v.shift d c) (b.shift d (c + 1))

/-- `let x := a; let y := b↑; x ⊕ y` -/
def binA (o : Bop) (a b : A) : A := .let_ a (.let_ (b.shift 1 0) (.bin o 1 0))

/-- **link 2** -/
def tr2 : E1 → A
  | .num n => .num n
  | .var i => .var i
  | .add a b => binA .add (tr2 a) (tr2 b)
  | .sub a b => binA .sub (tr2 a) (tr2 b)
  | .mul a b => binA .mul (tr2 a) (tr2 b)
  | .let_ v b => .let_ (tr2 v) (tr2 b)

def tr2P (p : Prog1) : Prog2 := (p.1, tr2 p.2)

theorem getD_shv (l₁ m l₂ : List UInt64) (i : Nat) :
    (l₁ ++ m ++ l₂).getD (shv m.length l₁.length i) 0 = (l₁ ++ l₂).getD i 0 := getD_shift l₁ m l₂ i

theorem den2_shift (m : List UInt64) : ∀ (e : A) (l₁ l₂ : List UInt64),
    den2 (e.shift m.length l₁.length) (l₁ ++ m ++ l₂) = den2 e (l₁ ++ l₂)
  | .num _, _, _ => rfl
  | .var i, l₁, l₂ => getD_shv l₁ m l₂ i
  | .bin o i j, l₁, l₂ => by simp only [A.shift, den2, getD_shv]
  | .let_ v b, l₁, l₂ => by
    simp only [A.shift, den2, den2_shift m v]
    have := den2_shift m b (den2 v (l₁ ++ l₂) :: l₁) l₂
    simpa using this

theorem den2_binA (o : Bop) (a b : A) (env : List UInt64) :
    den2 (binA o a b) env = o.eval (den2 a env) (den2 b env) := by
  simp only [binA, den2]
  have := den2_shift [den2 a env] b [] env
  simp only [List.length_nil, List.length_singleton, List.nil_append] at this
  rw [show den2 a env :: env = [den2 a env] ++ env from rfl, this]; rfl

theorem den2_tr2 : ∀ (e : E1) (env : List UInt64), den2 (tr2 e) env = den1 e env
  | .num _, _ => rfl
  | .var _, _ => rfl
  | .add a b, env => by simp only [tr2, den2_binA, den2_tr2 a, den2_tr2 b, den1, Bop.eval]
  | .sub a b, env => by simp only [tr2, den2_binA, den2_tr2 a, den2_tr2 b, den1, Bop.eval]
  | .mul a b, env => by simp only [tr2, den2_binA, den2_tr2 a, den2_tr2 b, den1, Bop.eval]
  | .let_ v b, env => by simp only [tr2, den2, den2_tr2 v, den2_tr2 b, den1]

/-- **link 2, programs**: for every program and every argument list -/
theorem tr2_eval (p : Prog1) (args : List UInt64) : (tr2P p).eval args = p.eval args := by
  simp [Prog2.eval, Prog1.eval, tr2P, den2_tr2]

end Nano.S3
