# Lean 4 elaborator essentials (tag v4.34.1) — what decides program meaning for nano

Paths are relative to `src/Lean/` unless noted (`Init/...` = `src/Init/`). Line numbers are for v4.34.1.

## 1. Plain-language explanation

The parser only produces syntax trees. The **elaborator** turns them into typed kernel terms and decides what the
program *means*. Nothing is typed in the source, so it has to fill in types, instances and conversions.
Five decisions matter for nano:

* **Numerals are overloaded.** `1` means `OfNat.ofNat ?α 1` with `?α` unknown. If nothing else pins `?α`, a
  *default instance* fires, and the lowest-priority one is `instOfNatNat`, so `?α := Nat`. This happens *late*:
  only after everything else is stuck.
* **Operators go through `binop%`.** `a + b` is `binop% HAdd.hAdd a b`. The elaborator collects the leaves of the
  whole operator tree, finds the "biggest" leaf type, and inserts coercions at the leaves. It then picks `HAdd`
  instances. So `n + i` with `n : Nat`, `i : Int` becomes `↑n + i`.
* **`if c then t else e`** is `ite c t e` and needs a `Decidable c` instance. `c` may be a `Prop` or a `Bool`
  (the `Bool` is coerced to `b = true`).
* **`match`** is compiled to an auxiliary *matcher* function (a `casesOn` tree). The compilation checks that the
  cases are exhaustive (else "Missing cases") and that no alternative is redundant (else error). Overlapping
  patterns use first-match-wins.
* **Recursive `def`s** are compiled by trying structural recursion (`brecOn`) first, then well-founded
  recursion (a measure guessed by `guessLex`, proofs by `decreasing_tactic`). `partial def` becomes an *opaque
  constant* plus an unsafe/implemented-by implementation. It has no equations, and it needs `Inhabited`.

**Worked example: `def f (x : Nat) := x + 1`**
1. Header: `x : Nat`. The return type is a metavariable `?r`.
2. Body: `x + 1` is a `binop%` tree with leaves `x : Nat` and `1 : ?α` (from `elabNumLit`, `Elab/BuiltinTerm.lean:210`).
3. `analyze` (`Elab/Extra.lean:256`): the max type is `Nat`. The leaf `1` has an unknown type, so there is nothing
   to coerce. `applyCoe` unifies `?α := Nat`, because `HAdd` has no heterogeneous default instance for `Nat`.
4. `mkBinOp` elaborates `HAdd.hAdd x 1`. The instance is `instHAdd` + `instAddNat`, the `OfNat Nat 1` instance is
   `instOfNatNat 1`, and `?r := Nat`.
5. `addPreDefinitions` (`Elab/PreDefinition/Main.lean:288`): the body is non-recursive, so `addAndCompileNonRec`.
   The kernel term is `fun x => HAdd.hAdd x (OfNat.ofNat 1)`.
   Its meaning is `Nat.add x 1`, an unbounded natural number.

## 2. File map

| What | Where | Notes |
|---|---|---|
| Numeral elab | `Elab/BuiltinTerm.lean:210` `elabNumLit` | `OfNat.ofNat ?α (rawNatLit n) ?inst`. The instance is an instance mvar. Errors if the expected type is a Prop. |
| `OfNat`, default instance | `Init/Notation.lean:~270-280`, `instOfNatNat` @ `:~280` `@[default_instance 100]` | `class OfNat α (n : Nat)`. Only Nat has the default. |
| Default-instance loop | `Elab/SyntheticMVars.lean:113` `synthesizeUsingDefaultPrio`, `:215` `synthesizeUsingDefault`, `:625-640` main loop, `:653` loop-until-fixpoint | Order: (1) resolve pending with postponement, (2) **default instances by priority (highest prio first)**, (3) resolve without postponement, (4) run tactics. |
| Operator notation | `Init/Notation.lean:284-313` (`infixl:65 " + "` ...; `macro_rules \| `($x + $y) => `(binop% HAdd.hAdd $x $y)`), `:390-393` `binrel% LT.lt`, `binrel% Eq` | `^` is `rightact%`, unary minus is `unop% Neg.neg`. `&&`/`\|\|` are plain `and`/`or` notation (not binop%, unverified here); `<\|>` is `binop_lazy%`. |
| binop% elaborator | `Elab/Extra.lean:475` `elabOp`; `toTree` (:~190), `analyze` (:256), `applyCoe` (:~420), `toExprCore` (:325), `hasHomogeneousInstance` (:387), `hasHeterogeneousDefaultInstances` (:367) | Design doc in the comment at `:~60-130`. |
| binrel% | `Elab/Extra.lean:497` `elabBinRelCore` | Uses `withSynthesizeLight`, i.e. **no default instances** before unifying the sides. |
| if/then/else | `Init/Prelude.lean:~1075-1100` (`ite`, `dite`), `Init/Notation.lean:470-495` | `ite c t e` needs `[Decidable c]`. |
| Decidable Nat | `Init/Prelude.lean:1873` `Nat.decEq` (via `Nat.beq`), `Nat.decLe`/`Nat.ble` @ :1893 | `Nat.ble`/`Nat.beq` are the kernel/compiler primitives. |
| match elab | `Elab/Match.lean:1266` `elabMatchCore`, `:1117` `elabMatchAux`, `:919` `elabMatchAltViews`, `:368` `elabPatterns`, `:605` `toPattern`, `:1024` `mkMatcher` wrapper, `:1043` `reportMatcherResultErrors` | `reportMatcherResultErrors` emits "Missing cases" and `lean.redundantMatchAlt`. |
| match compilation | `Meta/Match/Match.lean:960` `process` (state machine), `:470` `processLeaf`, `:549` `processConstructor`, `:668` `processValue`, `:738` `expandNatValuePattern`, `:1172` `mkMatcher` | Result has `counterExamples` (:213) and `unusedAltIdxs`. |
| Pattern types | `Meta/Match/Basic.lean` | `Pattern`: `inaccessible/var/ctor/val/arrayLit/as`. |
| def dispatch | `Elab/PreDefinition/Main.lean:288` `addPreDefinitions`, `:15-36` `addAndCompilePartial` | See the decision order in §3. |
| structural rec | `Elab/PreDefinition/Structural/Main.lean:183`, `FindRecArg.lean:256`, `BRecOn.lean:125` (`replaceRecApps`) | `brecOn` encoding. |
| WF rec | `Elab/PreDefinition/WF/Main.lean:23` `wfRecursion`, `GuessLex.lean:800` `guessLex`, `Fix.lean:289` `mkFix`, `:250` `solveDecreasingGoals` | `decreasing_tactic` is a macro-extensible tactic (`Init/WFTactics.lean`: `omega`, `simp +arith`, `assumption`...). |
| Name resolution | `ResolveName.lean:194` `resolveGlobalName`; helpers `:134` `resolveQualifiedName`, `:146` `resolveUsingNamespace`, `:154` `resolveExact`, `:165` `resolveOpenDecls`; `Elab/Open.lean` (`open` commands) | |

## 3. Facts that matter for nano

**Numerals**
* A literal with no other type information becomes `Nat`, via `instOfNatNat`, priority 100. This is the only
  `default_instance` for `OfNat`.
* `OfNat` instances exist for `Nat`, `Int`, `Fin (n+1)`, `UInt8/16/32/64`, `USize`, `BitVec w` and others.
  Literals are *never* range-checked at the type level: `(300 : UInt8)` is `UInt8.ofNat 300 = 44` (wraps, no
  error). nano must reproduce this wrap if it admits `UInt8` literals.
* Default instances only fire when elaboration is otherwise stuck. `let x := 5` gives `Nat`. In `a + 1` with
  `a : UInt8`, `1 : UInt8` comes from unification *before* defaulting.
* `binrel%` (`<`, `=`, `≤`, `≠`...) does not apply defaults before the sides are unified (`Extra.lean:~505`
  comment). A comparison `a ≥ 0` where `a`'s type is still unknown behaves differently from `Nat` defaulting.
  **Edge case for the fuzzer: lambda parameters with no annotation.**

**Arithmetic (`binop%`)**
* Algorithm: collect leaves, take the max type under "there is a coercion `α → β`", insert the coercions
  *at the leaves*, then synthesize instances. Whole-tree, left-to-right. If two leaf types are uncomparable, no
  coercions are inserted and plain unification applies, which usually errors.
* With **only Nat leaves**, nothing special happens and the result is `Nat` with unbounded arithmetic:
  `a - b` is truncated subtraction (`0` if `b > a`), `a / 0 = 0`, `a % 0 = a`. These Lean conventions are part of
  nano's required semantics. Nano's subset may reject mixed types, but must not accept a mixed program and compute
  something different. `↑n + i` is `Int.ofNat n + i`.
* `x ^ n` is `rightact%`: `n` is **not** coerced to `x`'s type. `2 ^ 64` with no context is `Nat`.
* `==` is `binrel_no_prop%`. For `Nat`, `BEq` comes from `instBEqOfDecidableEq` (priority 500) over `Nat.decEq`.
  `a = b` as a `Prop` in `if` uses `instDecidableEqNat`. Both are semantically equal to `Nat.beq`.
* Precedence/associativity come from the notation table (`Init/Notation.lean:284-313`). Ours must match exactly:
  `+ -` 65, `* / %` 70, `^` 75 right-assoc, comparisons 50, `&&` 35, `||` 30.

**if/then/else**
* `if c then t else e` ⇒ `ite c t e` with `[Decidable c]`. For `c : Bool`, the elaborator coerces `c` to
  `c = true`, and the `Decidable` instance is `instDecidableEqBool`. Both branches are *lazily* evaluated in compiled
  code (the compiler special-cases `ite`/`dite`). In the kernel it is just a function applied to both, so only
  `partial def` and recursion behaviour care.
* `if h : c then ..` is `dite`. Hypotheses are usable in `t`/`e`, which matters for well-founded recursion proofs.
* The `let_mvar%`/`wait_if_type_mvar%` wrapper (`Notation.lean:470-480`) delays elaboration until `c`'s type is known.

**match**
* Semantics: first matching alternative wins. A pattern is a constructor application, variable, wildcard `_`,
  literal (`Nat`, `Int`, `Fin`, `BitVec`, `Char`, `String`, array literal) or `x@p`.
* **Nat literal patterns** are rewritten to `Nat.zero`/`Nat.succ` (`Match.lean:738` `expandNatValuePattern`):
  `| 0 | 1 | n+2` is a nest of constructor matches. **Literal patterns in other types use `decEq` chains**
  (`processValue`, `CaseValues.lean`), i.e. sequential `if x = v then ..`.
* Exhaustiveness: the algorithm closes each leaf with `contradiction`. If a leaf has no alternative and
  `contradiction` fails, it records a counterexample, and elaboration reports "Missing cases" as an **error**.
  Redundancy: an alternative never reaching a leaf is an **error** too (`unusedAltIdxs`, `match.ignoreUnusedAlts`
  can silence it). nano must reject the same programs or a strict subset.
* Subtlety: exhaustiveness is *semantic*. It uses the dependent-type `contradiction` closer, so a match on
  `Fin 2` with cases `0`, `1` is exhaustive, but a nano checker that only counts patterns may disagree on indexed
  families, `Nat` literals mixed with `n+k`, or `Fin`/`UInt8` literal sets (`UInt8` literals never exhaust).
  nano's subset should stay on plain ADTs + `Nat` + `Bool`, where syntactic checking is complete.
* `match` on multiple discriminants is all-at-once. Alternatives are compiled left-to-right, with a "move first
  refutable var to front" step (`firstRefutablePattern`, line 833), controlled by `backward.match.rowMajor`.

**Definitions**
* Decision order (`Main.lean:288-345`): non-recursive ⇒ plain def. `unsafe` ⇒ unsafe. `partial` ⇒ `opaque` +
  implementation (`:15`), which needs an `Inhabited` witness (`mkInhabitantFor`). Else `termination_by structural`
  ⇒ structural. `partial_fixpoint` ⇒ lattice. `termination_by` ⇒ WF. **No hint ⇒ try structural, then WF
  (`orelseMergeErrors`)**.
* Structural: searches for a recursion argument (`FindRecArg.lean`) of inductive type where every recursive call
  is on a strict subterm; the term is compiled to `brecOn`. The *compiled code* uses the original recursive
  definition (the kernel term is only for proofs/defeq), so runtime behaviour is the obvious recursion.
* WF: `guessLex` tries lexicographic combinations of measures (arguments of type Nat, sizeOf, ...), with
  `decreasing_tactic` closing `x < y` goals (`omega`, `simp +arith`). Failure ⇒ "fail to show termination". It
  is not complete. nano needs its own, simpler and decidable, termination check.
* `partial def`: *any* recursion allowed, but the function is **opaque** (no equations, cannot be proven about) and
  requires the result type to be `Inhabited`/`Nonempty`. nano's invariant 1 is satisfied only if nano accepts
  `partial` only when Lean would, so the same Inhabited requirement applies. Since nano proves things about its
  programs, `partial` defs are exactly what the proofs cannot unfold in Lean's logic.
* Mutual blocks, `where`, `let rec` become auxiliary top-level defs (`betaReduceLetRecApps`, `Main.lean:~300`).

**Name resolution** (`ResolveName.lean:194`)
Order for an identifier `id` in namespace `ns` (e.g. `A.B`): (1) `ns.id`, then enclosing namespaces `A.id`, then root,
the first non-empty set winning (`resolveUsingNamespace`); (2) exact/`_root_`; (3) `open` declarations (`resolveOpenDecls`),
all opens combined; (4) aliases. **More than one candidate ⇒ overloaded**; the elaborator tries all and keeps the
ones that typecheck, erroring on ambiguity. Protected names (`Nat.add`) are not found through `open Nat` as `add`.
Dotted suffixes `x.f` are field/projection notation resolved after the head. nano: namespaces + `open` can be
implemented as a pure function over a list of declared names, but must replicate "innermost namespace wins,
opens add to ambiguity".

## 4. Reuse assessment for nano

Legend: (a) blueprint, (b) test oracle, (c) copy as-is. The "proof" column is whether nano could prove its version.

| Idea | Mode | Provable in our setting? | Effort (rough) |
|---|---|---|---|
| Numeral → `Nat` default + `OfNat` instance lookup | (a) | Yes. Nano can have a fixed instance table: type of literal = expected type, else `Nat`. Proof: erasure to `Nat.ofNat`/`UIntN.ofNat`. | small (days) |
| binop% max-type + leaf coercions | (a) | Partly. The *full* algorithm needs `isDefEq`, type classes, `CoeT` search, not provable. A nano subset with a fixed ordering (`Nat < Int`, same-type otherwise) and a flat unifier is a ~100-line total function. | 1-2 weeks incl. proof |
| `binrel%` "no defaults first" rule | (a) | Yes as a simple rule: unify sides before defaulting. | small |
| Instances `Add/Sub/Mul/Div/Mod Nat`, `Nat.decEq/decLe` | (a)/(b) | Yes: nano defines the semantics, e.g. in Lean `Nat.sub`, `Nat.div`, `Nat.mod`, which are total. | small |
| Matcher compilation (`process`, `processConstructor`, `processValue`) | (a) | The *design* (Maranget-style problem = vars × alts, transitions, leaf = alt or counterexample) is portable and provable for plain ADTs: define as a total function (recursion on a fuel/size measure), prove "result tree semantics = first-match semantics". The Lean code (1300 lines) uses `MVarId`, `cases` tactic, `contradiction`, so **no copy**. | 2-4 weeks for ADT + Nat-literal + Bool patterns |
| Exhaustiveness / redundancy via leaves | (a) + (b) | Yes: a leaf with empty alt list = missing case. An alt never at a leaf = redundant. Both are decidable for ADTs; proof: coverage ⇒ the match never falls through. | included above |
| Nat literal → `zero/succ` pattern expansion | (a) | Yes, simple. `n+k` patterns and literals share the encoding. | small |
| Structural recursion detection (strict-subterm check) | (a) | Yes: a recursive call is accepted only if the argument is a pattern-bound subterm of a discriminant. Soundness proof: measure = size of the ADT value. | 1-2 weeks |
| `guessLex` / `decreasing_tactic` | (a) light | Do not copy. nano should accept only (i) structural, (ii) an explicit user-supplied `termination_by` with a decidable check (a Nat expression strictly decreasing under `<`), or (iii) FUEL (already the owner's pattern). Subset of Lean's cases, so invariant 1 holds. | 1-2 weeks |
| `partial def` | (a) | Semantics = opaque; nano can *reject* it or give it a fuel-based total reading. A program that uses `partial` computes the same value on inputs where it terminates; the machine result is only provable with a termination premise. | design call |
| Name resolution (namespaces/open) | (a) | Yes: a pure function on `List Name` + current namespace + open list, ~50 lines, easy to prove idempotent/shadowing properties. | small |
| `elabNumLit`/`binop%` source as code | (c) | **No.** The code runs in `TermElabM` (mutable mctx, tactic framework, 100k+ lines of dependencies, many `partial`). Not self-hostable and not provable. | n/a |
| **Whole elaborator as test oracle** | (b) | Yes, the best use: for fuzz programs, run real Lean and compare nano's result. Also assert on `#print`: literal types, inserted `↑`, unused/missing-alternative error messages. | ongoing |

Honest caveats:
* The elaborator is not a closed algorithm. Behaviour depends on instance resolution, postponement order and
  the default-instance loop. nano's invariant "accepts ⇒ Lean accepts and agrees" is best guaranteed by a
  **restrictive** subset: every literal annotated or `Nat`, same-type arithmetic, plain ADTs, structural recursion.
  Wherever nano is more liberal than that, add a fuzz test first.
* Silent semantic traps to put in the fuzzer: Nat truncated subtraction; `x / 0 = 0`; `x % 0 = x`; `UIntN` literal
  wraparound; `Int` `/` and `%` rounding convention (check against `Init/Data/Int` before trusting any model); `a - 1 + 1` vs
  `a + 1 - 1`; unannotated lambda comparison types; `if` on `Bool` vs `Prop`.
* Match compilation errors (missing/redundant) are *errors* in Lean, so nano must reject exactly these programs
  or a superset. Rejecting more is fine. Accepting less-checked programs breaks invariant 1.
