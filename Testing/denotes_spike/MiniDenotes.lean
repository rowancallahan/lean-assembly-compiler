/- MiniDenotes: a standalone, trimmed copy of con-leche's `Denotes` (dwijayuda/con-leche @ 3b37939) and a tiny
theorem: a tiny evaluator agrees with `Denotes`.  No imports.  Sources of what is copied:
* `Expr`: ConLeche/Kernel/Expr.lean:328 — only `bvar`, `const`, `app`, `lit` kept; no computed `data` field,
  no level lists (all constants here are level-free), `Name` replaced by `String`.
* `Literal.natVal`: ConLeche/Kernel/Expr.lean:107.
* `natLitToConstructor`: ConLeche/Kernel/CoreDefs.lean:123 (verbatim modulo names).
* `push`: ConLeche/Denotes.lean:118 (verbatim).
* `Denotes`: ConLeche/Denotes.lean:134 — rules `bvar` (137), `const` (144, env lookup and level assignment
  dropped: a constant denotes `cval n`), `app` (151), `natLit` (184).  Other rules omitted (unused).
* the set theory: only `app : V → V → V` is used (ConLeche/SetTheory/Derive/Graphs.lean:53), taken as a variable.
Model facts are HYPOTHESES of the theorem (`hadd`, `hite`): what the stored theorems + `eq_equality` would give
(DENOTES_SPIKE.md §2). -/
namespace MiniDenotes

inductive Literal | natVal (n : Nat)

inductive Expr
  | bvar (i : Nat)
  | const (n : String)
  | app (f a : Expr)
  | lit (l : Literal)

def natLitToConstructor (n : Nat) : Expr :=
  match n with
  | 0 => .const "Nat.zero"
  | k + 1 => .app (.const "Nat.succ") (.lit (.natVal k))

variable {V : Type} (app : V → V → V)

def push (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

inductive Denotes (cval : String → V) : (Nat → V) → Expr → V → Prop
  | bvar {ρ i} : Denotes cval ρ (.bvar i) (ρ i)
  | const {ρ n} : Denotes cval ρ (.const n) (cval n)
  | app {ρ f a F X} : Denotes cval ρ f F → Denotes cval ρ a X → Denotes cval ρ (.app f a) (app F X)
  | natLit {ρ n X} : Denotes cval ρ (natLitToConstructor n) X → Denotes cval ρ (.lit (.natVal n)) X

/-! ## the tiny language -/
inductive T | lit (n : Nat) | add (a b : T) | ite (a b t e : T)

def tinyEval : T → Nat
  | .lit n => n
  | .add a b => tinyEval a + tinyEval b
  | .ite a b t e => if tinyEval a = tinyEval b then tinyEval t else tinyEval e

/-- the emitted term: `Nat.add a b`; `iteEq a b t e` stands for `ite (a = b) t e` (one head, its arguments) -/
def tr : T → Expr
  | .lit n => .lit (.natVal n)
  | .add a b => .app (.app (.const "Nat.add") (tr a)) (tr b)
  | .ite a b t e => .app (.app (.app (.app (.const "iteEq") (tr a)) (tr b)) (tr t)) (tr e)

/-- canonical encoding: what `succ^n zero` denotes -/
def enc (cval : String → V) : Nat → V
  | 0 => cval "Nat.zero"
  | n + 1 => app (cval "Nat.succ") (enc cval n)

theorem lit_denotes (cval : String → V) (ρ : Nat → V) :
    ∀ n, Denotes app cval ρ (.lit (.natVal n)) (enc app cval n)
  | 0 => .natLit .const
  | n + 1 => .natLit (.app .const (lit_denotes cval ρ n))

/-- **The tiny theorem.**  Hypotheses = what the model gives: `Nat.add` acts as `+` on encodings, `iteEq`
selects by equality of the decoded numbers. -/
theorem tiny_denotes (cval : String → V) (ρ : Nat → V)
    (hadd : ∀ a b, app (app (cval "Nat.add") (enc app cval a)) (enc app cval b) = enc app cval (a + b))
    (hite : ∀ a b t e, app (app (app (app (cval "iteEq") (enc app cval a)) (enc app cval b)) t) e =
      if a = b then t else e) :
    ∀ e v, tinyEval e = v → Denotes app cval ρ (tr e) (enc app cval v) := by
  intro e
  induction e with
  | lit n => intro v h; subst h; exact lit_denotes app cval ρ n
  | add a b iha ihb =>
    intro v h; subst h
    have := Denotes.app (Denotes.app (Denotes.const (n := "Nat.add")) (iha _ rfl)) (ihb _ rfl)
    rwa [hadd] at this
  | ite a b t e iha ihb iht ihe =>
    intro v h; subst h
    have := Denotes.app (Denotes.app (Denotes.app (Denotes.app (Denotes.const (n := "iteEq")) (iha _ rfl)) (ihb _ rfl)) (iht _ rfl))
      (ihe _ rfl)
    rw [hite] at this
    simp only [tinyEval]
    split <;> rename_i hc <;> simp only [hc, ite_true, ite_false] at this <;> exact this

end MiniDenotes

#print axioms MiniDenotes.tiny_denotes
