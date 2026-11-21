/- Harvest/H9/Match: nano-style candidate rules for `match` / `fun |` alternatives on Nat/UInt64 literals, `n+k`,
wildcard, as-patterns, tuples, Option, against Lean's own compiled `match` (the matcher is `casesOn`-based; the
THEOREMS are about the semantics Lean gives to each shape, since `match` elaboration itself is partial/elaborator-only).
Candidate model: first-match-wins list of (pattern, rhs). Standalone: Init only. -/
namespace H9

/-- candidate pattern language: wildcard/var `_`, literal `k`, successor-offset `p+1` (`n+2` = succ (succ var)),
as-pattern `x@p` (binds the whole scrutinee as well) -/
inductive P | any | lit (k : Nat) | succ (p : P) | as (p : P)

/-- bindings produced, in order (variables bind the matched value; `as` binds the whole value first) -/
def P.m : P → Nat → Option (List Nat)
  | .any, n => some [n]
  | .lit k, n => if n = k then some [] else none
  | .succ _, 0 => none
  | .succ p, n + 1 => p.m n
  | .as p, n => (p.m n).map (n :: ·)

/-- first-match-wins; `f` is the rhs applied to the bindings -/
def evalAlts (alts : List (P × (List Nat → α))) (n : Nat) : Option α :=
  alts.findSome? fun (p, f) => (p.m n).map f

/-- a candidate exhaustiveness rule: some alternative is irrefutable (nano can require a final `_`/var alt) -/
def P.irref : P → Bool | .any => true | .as p => p.irref | _ => false
def covers (alts : List (P × (List Nat → α))) : Bool := alts.any (·.1.irref)

theorem irref_m : ∀ p : P, p.irref = true → ∀ n, (p.m n).isSome
  | .any, _, n => rfl
  | .as p, h, n => by simpa [P.m] using irref_m p h n
  | .lit _, h, _ => by simp [P.irref] at h
  | .succ _, h, _ => by simp [P.irref] at h

/-- candidate-accepted (covering) alt lists never fall off the end -/
theorem covers_total (alts : List (P × (List Nat → α))) (h : covers alts = true) (n : Nat) :
    (evalAlts alts n).isSome := by
  induction alts with
  | nil => simp [covers] at h
  | cons a as ih =>
    obtain ⟨p, f⟩ := a
    simp only [evalAlts, List.findSome?_cons, List.head!, List.getD]
    cases hm : p.m n with
    | some v => simp
    | none =>
      simp only [Option.map_none]
      have : covers as = true := by
        simp [covers, List.any_cons] at h
        rcases h with h | h
        · have := irref_m p h n; simp [hm] at this
        · simpa [covers] using h
      exact ih this

/-! ### Lean's meaning of each shape (the `match` is Lean's own; `#print axioms` below) -/

/-- `match n with | 0 => a | n+1 => f n`: literal + `n+1` (Nat.casesOn) -/
theorem succ_shape (a : α) (f : Nat → α) (n : Nat) :
    evalAlts [(.lit 0, fun _ => a), (.succ .any, fun l => f l.head!)] n
      = some (match n with | 0 => a | m+1 => f m) := by
  cases n <;> simp [evalAlts, P.m, List.findSome?_cons, List.head!, List.getD]

/-- `match n with | 0 => a | 1 => b | _ => c` (literal chain, wildcard fallthrough) -/
theorem lits_shape (a b c : α) (n : Nat) :
    evalAlts [(.lit 0, fun _ => a), (.lit 1, fun _ => b), (.any, fun _ => c)] n
      = some (match n with | 0 => a | 1 => b | _ => c) := by
  match n with
  | 0 | 1 | n + 2 => simp [evalAlts, P.m, List.findSome?_cons, List.head!, List.getD]

/-- `match n with | n+2 => f n | _ => d`: offset ≥ 2 -/
theorem succ2_shape (f : Nat → α) (d : α) (n : Nat) :
    evalAlts [(.succ (.succ .any), fun l => f l.head!), (.any, fun _ => d)] n
      = some (match n with | n+2 => f n | _ => d) := by
  match n with
  | 0 | 1 | n + 2 => simp [evalAlts, P.m, List.findSome?_cons, List.head!, List.getD]

/-- as-pattern: `match n with | 0 => a | m@(k+1) => f m k`, `m = k+1` -/
theorem as_shape (a : α) (f : Nat → Nat → α) (n : Nat) :
    evalAlts [(.lit 0, fun _ => a), (.as (.succ .any), fun l => f l.head! (l.getD 1 0))] n
      = some (match n with | 0 => a | m@(k+1) => f m k) := by
  cases n <;> simp [evalAlts, P.m, List.findSome?_cons, List.head!, List.getD]

/-- UInt64 literal patterns are Lean's `x = k` decisions (`match x with | 0 => a | _ => b`) -/
theorem u64_lit_shape (a b : α) (x : UInt64) :
    (if x = 0 then a else b) = (match x with | 0 => a | _ => b) := by
  by_cases h : x = 0 <;> simp [h]

/-- tuple pattern `match p with | (a, b) => f a b` is projections (structure eta) -/
theorem prod_shape (f : Nat → Nat → α) (p : Nat × Nat) :
    (match p with | (a, b) => f a b) = f p.1 p.2 := rfl

/-- Option patterns: `match o with | none => d | some x => f x` is `Option.casesOn`/`getD`-style -/
theorem option_shape (d : α) (f : Nat → α) (o : Option Nat) :
    (match o with | none => d | some x => f x) = (o.map f).getD d := by cases o <;> rfl

/-- `fun | p => e` (matchAlts as `fun` body, Lean/Parser/Term.lean:387) is `fun x => match x with | p => e` -/
theorem fun_alts_shape (a : α) (f : Nat → α) :
    (fun | 0 => a | n+1 => f n) = (fun x : Nat => match x with | 0 => a | n+1 => f n) := rfl

/-- multi-discriminant alternatives `| p, q => e` ≡ nested first-match over pairs -/
theorem two_disc_shape (a b c : α) (m n : Nat) :
    (match m, n with | 0, _ => a | _+1, 0 => b | _+1, _+1 => c)
      = (match m with | 0 => a | _+1 => (match n with | 0 => b | _+1 => c)) := by
  cases m <;> cases n <;> rfl

end H9
