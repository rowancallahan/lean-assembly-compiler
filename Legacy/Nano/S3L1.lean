/- **nano → S3, link 1: call-free nano** (`Testing/notes/NANO_S3.md`).

L1 = nano's `Ex` without `call`/`anil`/`acons`: `num`, `var`, `add`, `sub`, `mul`, `let_`, same meaning (`den1`, an
out-of-range variable is `0`).  The ONE construct removed: the call with its own environment.  `tr1` replaces
`call b [e₁ … eₙ]` by `let a₁ := e₁; …; let aₙ := eₙ; b'`, where argument `k` is shifted past the `k` earlier lets
(`shift`) and the body only sees its parameters (`cut`: a body variable `≥ n` is `0`, as `den` on the argument list
gives).  Theorem: `tr1_eval : (tr1P p).eval args = p.eval args` for every program and argument list. -/
import Legacy.Nano.Ast

namespace Nano.S3
open Nano

inductive E1 where
  | num (n : UInt64) | var (i : Nat)
  | add (a b : E1) | sub (a b : E1) | mul (a b : E1)
  | let_ (v b : E1)
  deriving DecidableEq, Repr

def den1 : E1 → List UInt64 → UInt64
  | .num n, _ => n
  | .var i, env => env.getD i 0
  | .add a b, env => den1 a env + den1 b env
  | .sub a b, env => den1 a env - den1 b env
  | .mul a b, env => den1 a env * den1 b env
  | .let_ v b, env => den1 b (den1 v env :: env)

abbrev Prog1 := Nat × E1

def Prog1.eval (p : Prog1) (args : List UInt64) : Option UInt64 :=
  if args.length = p.1 then some (den1 p.2 args.reverse) else none

/-! ## the translation -/

/-- variables `≥ c` move up by `d` -/
def E1.shift (d : Nat) : Nat → E1 → E1
  | _, .num n => .num n
  | c, .var i => if i < c then .var i else .var (i + d)
  | c, .add a b => .add (a.shift d c) (b.shift d c)
  | c, .sub a b => .sub (a.shift d c) (b.shift d c)
  | c, .mul a b => .mul (a.shift d c) (b.shift d c)
  | c, .let_ v b => .let_ (v.shift d c) (b.shift d (c + 1))

/-- variables `≥ c + n` become `0` -/
def E1.cut (n : Nat) : Nat → E1 → E1
  | _, .num k => .num k
  | c, .var i => if i < c + n then .var i else .num 0
  | c, .add a b => .add (a.cut n c) (b.cut n c)
  | c, .sub a b => .sub (a.cut n c) (b.cut n c)
  | c, .mul a b => .mul (a.cut n c) (b.cut n c)
  | c, .let_ v b => .let_ (v.cut n c) (b.cut n (c + 1))

/-- `let e₁; …; let eₙ; b` -/
def lets : List E1 → E1 → E1
  | [], b => b
  | e :: es, b => .let_ e (lets es b)

/-- the number of arguments of an argument chain -/
def argc : Ex → Nat
  | .acons _ r => argc r + 1
  | _ => 0

mutual
/-- **link 1** -/
def tr1 : Ex → E1
  | .num n => .num n
  | .var i => .var i
  | .add a b => .add (tr1 a) (tr1 b)
  | .sub a b => .sub (tr1 a) (tr1 b)
  | .mul a b => .mul (tr1 a) (tr1 b)
  | .let_ v b => .let_ (tr1 v) (tr1 b)
  | .call b as => lets (tr1A as 0) ((tr1 b).cut (argc as) 0)
  | .anil => .num 0
  | .acons _ _ => .num 0
/-- the arguments, argument `j` shifted past the `k + j` lets before it -/
def tr1A : Ex → Nat → List E1
  | .acons e r, k => (tr1 e).shift k 0 :: tr1A r (k + 1)
  | .num _, _ => []
  | .var _, _ => []
  | .add _ _, _ => []
  | .sub _ _, _ => []
  | .mul _ _, _ => []
  | .let_ _ _, _ => []
  | .call _ _, _ => []
  | .anil, _ => []
end

def tr1P (p : Prog) : Prog1 := (p.1, tr1 p.2)

/-! ## correctness -/

theorem getD_shift (l₁ m l₂ : List UInt64) (i : Nat) :
    (l₁ ++ m ++ l₂).getD (if i < l₁.length then i else i + m.length) 0 = (l₁ ++ l₂).getD i 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · next h => rw [List.append_assoc, List.getElem?_append_left h, List.getElem?_append_left h]
  · next h =>
    rw [List.append_assoc, List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    congr 2; omega

theorem den1_shift (m : List UInt64) : ∀ (e : E1) (l₁ l₂ : List UInt64),
    den1 (e.shift m.length l₁.length) (l₁ ++ m ++ l₂) = den1 e (l₁ ++ l₂)
  | .num _, _, _ => rfl
  | .var i, l₁, l₂ => by
    have := getD_shift l₁ m l₂ i
    simp only [E1.shift]; split <;> simp_all [den1]
  | .add a b, l₁, l₂ => by simp only [E1.shift, den1, den1_shift m a, den1_shift m b]
  | .sub a b, l₁, l₂ => by simp only [E1.shift, den1, den1_shift m a, den1_shift m b]
  | .mul a b, l₁, l₂ => by simp only [E1.shift, den1, den1_shift m a, den1_shift m b]
  | .let_ v b, l₁, l₂ => by
    simp only [E1.shift, den1, den1_shift m v]
    have := den1_shift m b (den1 v (l₁ ++ l₂) :: l₁) l₂
    simpa using this

theorem den1_cut (n : Nat) : ∀ (e : E1) (l₁ l₂ : List UInt64),
    den1 (e.cut n l₁.length) (l₁ ++ l₂) = den1 e (l₁ ++ l₂.take n)
  | .num _, _, _ => rfl
  | .var i, l₁, l₂ => by
    simp only [E1.cut]
    split
    · next h =>
      simp only [den1, List.getD_eq_getElem?_getD]
      by_cases h1 : i < l₁.length
      · rw [List.getElem?_append_left h1, List.getElem?_append_left h1]
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), List.getElem?_take,
          if_pos (by omega)]
    · next h =>
      simp only [den1, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)]; rfl
  | .add a b, l₁, l₂ => by simp only [E1.cut, den1, den1_cut n a, den1_cut n b]
  | .sub a b, l₁, l₂ => by simp only [E1.cut, den1, den1_cut n a, den1_cut n b]
  | .mul a b, l₁, l₂ => by simp only [E1.cut, den1, den1_cut n a, den1_cut n b]
  | .let_ v b, l₁, l₂ => by
    simp only [E1.cut, den1, den1_cut n v]
    have := den1_cut n b (den1 v (l₁ ++ l₂.take n) :: l₁) l₂
    simpa using this

/-- the environment after the lets -/
def evals : List E1 → List UInt64 → List UInt64
  | [], env => env
  | e :: es, env => evals es (den1 e env :: env)

theorem den1_lets : ∀ (es : List E1) (b : E1) (env : List UInt64), den1 (lets es b) env = den1 b (evals es env)
  | [], _, _ => rfl
  | e :: es, b, env => den1_lets es b (den1 e env :: env)

theorem argc_denA : ∀ (as : Ex) (env : List UInt64), (denA as env).length = argc as
  | .acons _ r, env => by simp [denA, argc, argc_denA r env]
  | .num _, _ => rfl
  | .var _, _ => rfl
  | .add _ _, _ => rfl
  | .sub _ _, _ => rfl
  | .mul _ _, _ => rfl
  | .let_ _ _, _ => rfl
  | .call _ _, _ => rfl
  | .anil, _ => rfl

/-- **link 1 is correct**, expressions and argument chains together -/
theorem tr1_ok (e : Ex) : (∀ env, den1 (tr1 e) env = den e env) ∧
    (∀ k (pre env : List UInt64), pre.length = k → evals (tr1A e k) (pre ++ env) = (denA e env).reverse ++ pre ++ env) := by
  induction e with
  | num n => exact ⟨fun _ => by simp [tr1, den1, den], fun _ _ _ _ => by simp [tr1A, evals, denA]⟩
  | var i => exact ⟨fun _ => by simp [tr1, den1, den], fun _ _ _ _ => by simp [tr1A, evals, denA]⟩
  | add a b iha ihb => exact ⟨fun _ => by simp [tr1, den1, den, iha.1, ihb.1], fun _ _ _ _ => by simp [tr1A, evals, denA]⟩
  | sub a b iha ihb => exact ⟨fun _ => by simp [tr1, den1, den, iha.1, ihb.1], fun _ _ _ _ => by simp [tr1A, evals, denA]⟩
  | mul a b iha ihb => exact ⟨fun _ => by simp [tr1, den1, den, iha.1, ihb.1], fun _ _ _ _ => by simp [tr1A, evals, denA]⟩
  | let_ v b ihv ihb => exact ⟨fun _ => by simp [tr1, den1, den, ihv.1, ihb.1], fun _ _ _ _ => by simp [tr1A, evals, denA]⟩
  | anil => exact ⟨fun _ => by simp [tr1, den1, den], fun _ _ _ _ => by simp [tr1A, evals, denA]⟩
  | acons e r ihe ihr =>
    refine ⟨fun _ => by simp [tr1, den1, den], fun k pre env hk => ?_⟩
    simp only [tr1A, evals]
    have h1 : den1 ((tr1 e).shift k 0) (pre ++ env) = den e env := by
      have := den1_shift pre (tr1 e) [] env
      rw [hk] at this; simpa [ihe.1] using this
    rw [h1, show den e env :: (pre ++ env) = [den e env] ++ pre ++ env by simp,
      ihr.2 (k + 1) ([den e env] ++ pre) env (by simp [hk])]
    simp [denA]
  | call b as ihb ihas =>
    refine ⟨fun env => ?_, fun _ _ _ _ => by simp [tr1A, evals, denA]⟩
    simp only [tr1, den1_lets, den]
    have := ihas.2 0 [] env rfl
    simp only [List.nil_append, List.append_nil] at this
    rw [this]
    have hc := den1_cut (argc as) (tr1 b) [] ((denA as env).reverse ++ env)
    simp only [List.length_nil, List.nil_append] at hc
    rw [hc, ← argc_denA as env, List.take_left' (by simp), ihb.1]

theorem den1_tr1 (e : Ex) (env : List UInt64) : den1 (tr1 e) env = den e env := (tr1_ok e).1 env

/-- **link 1, programs**: for every program and every argument list -/
theorem tr1_eval (p : Prog) (args : List UInt64) : (tr1P p).eval args = p.eval args := by
  simp [Prog1.eval, Prog.eval, tr1P, den1_tr1]

end Nano.S3
