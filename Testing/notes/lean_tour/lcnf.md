# Lean 4 compiler tour: LCNF (the middle end)

Source: `leanprover/lean4` tag `v4.34.1`, `src/Lean/Compiler/LCNF/` (~20.7k lines incl. Simp/).
Paths below are relative to that directory. Line numbers are for v4.34.1.
Read for nano's invariants: nano ⊆ Lean (same results) and self-hosting (compiler in nano's subset).

**Version note (verified in `Passes.lean`):** in v4.34.1 the *new* compiler is the default pipeline and LCNF now has
THREE phases, not two: `base` → `mono` → `impure`. The old C++ compiler and the separate IR optimiser are replaced:
reset/reuse, borrow inference, boxing, RC insertion are now LCNF passes in the `impure` phase (`ToImpure.lean`,
`ResetReuse.lean`, `InferBorrow.lean`, `ExplicitBoxing.lean`, `ExplicitRC.lean`, ...). `Main.lean:200-210` then calls
`IR.toIR` + `IR.compile` (the older `Lean/Compiler/IR/*` is only the last step: IR checks + EmitC/LLVM; not my area).
Older write-ups (2022 LCNF = 2 phases, "base/mono") are out of date.

## 1. Plain-language explanation

LCNF = "Lambda-Compiled Normal Form". After Lean has checked a definition, the compiler takes its kernel term
(with types, proofs, `match` compiled to `casesOn`, type-class dictionaries) and turns it into a small
**A-normal-form** language: every intermediate result is named by a `let`, control flow is `cases`, local functions
are `fun`, and *join points* (`jp`/`jmp`) are local, non-escaping continuations (basically labelled blocks with
arguments = SSA phi nodes). Then ~40 passes make it fast:

* **Erase** what has no runtime meaning (types, proofs, `Decidable` evidence becomes `Bool`, `Nat.succ n` patterns
  become `n-1` tests).
* **Inline / simplify** small functions, constant-fold, resolve `cases` on a known constructor, remove dead code.
* **Specialize** higher-order / type-class-polymorphic functions at call sites with known instance/function arguments
  (so `List.foldl (· + ·) 0 xs` over `Nat` becomes a first-order loop). This is THE big win for idiomatic Lean.
* **Lambda-lift** remaining closures into top-level functions; **extract closed terms** into global constants
  computed once.
* **Impure phase**: make allocation, projections, reference counts and boxing explicit; reuse memory of a dying
  constructor for a new one of the same shape (`reset/reuse`, "Counting Immutable Beans").

### Worked example `def f (x : Nat) := x + 1` (shape, from reading the passes; not run here)
1. `toDecl` (`ToDecl.lean:130`) takes `fun x => HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) x 1`, erases the type
   args, `toLCNF` gives (`ToLCNF.lean:486`) roughly
   `let _x.1 := instAddNat; let _x.2 := instHAdd ◾ _x.1; let _x.3 := 1; let _x.4 := HAdd.hAdd ◾◾◾ _x.2 x _x.3; return _x.4`
   (`◾` = erased argument).
2. `pullInstances`, `simp` (base): instances are structures of closures; `inlineProjInst?` (`Simp/InlineProj.lean`) and
   inlining of `[inline]`/small instance projections reduce it to `let _x.1 := Nat.add x 1; return _x.1`.
   `Nat.add` is `@[extern "lean_nat_add"]`, so it stays a call; constant folding (`Simp/ConstantFold.lean`) would
   fold `Nat.add 2 1` but not this.
3. base→mono (`ToMono`): nothing to erase here; Nat stays `Nat` (boxed bignum-or-scalar in Lean's runtime).
4. impure: `Nat.add` becomes `fap Nat.add [x, 1]`; `x` is a borrowed param (infer-borrow), result owned. No reset/reuse
   (no ctor). Final IR/EmitC: `lean_nat_add(x, lean_box(1))`.
If instead `f (x : UInt64) := x + 1`, ConstantFold/inlining reach `UInt64.add x 1` → unboxed C `x + 1`.

## 2. File map (v4.34.1)
Data structures
* `Basic.lean:36` `Purity` (`pure`|`impure`; types are indexed by it only via erased proofs). `:104` `Arg` (erased | fvar | type).
  `:161` `LetValue`: lit, erased, proj, const, fvar-app; impure-only: ctor, oproj, uproj, sproj, fap, pap, reset, reuse, box, unbox, isShared.
  `:359` `Alt`, `:364` `FunDecl`, `:367` `Cases`, `:371` `Code` = let | fun | jp | jmp | cases | return | unreach.
  `:144` `CtorInfo` (name, cidx, #obj fields, #usize, #scalar bytes) — the memory layout decision lives here.
* `CompilerM.lean` (monad, local context, phase), `PhaseExt.lean` (per-phase decl storage across modules),
  `Check.lean` (type/scope checker run between passes with `compiler.check`), `PrettyPrinter.lean`.
Driver
* `Main.lean:122` `run`: toDecl → `markRecDecls` → base passes → mono passes → `splitScc` → (per SCC) `monoPassesNoLambda` → impure passes → `IR.toIR`.
  `Main.lean:216` `runPassManagerPart`.  `Passes.lean:92` `builtinPassManager` = THE pass list (below).
* `PassManager.lean` (`PassInstaller`, `@[cpass]` attribute: user-installable passes — Lean lets you insert passes!)
Front: kernel term → LCNF
* `ToDecl.lean:130` `toDecl` (macro_inline, matcher inlining `:41`, extern/init handling, eta-expand).
* `ToLCNF.lean:486` `toLCNF`. `visitCases :621` (casesOn → `cases`), `visitCtor :679`, `visitProjFn :802`,
  `visitEqRec :713`, `visitNoConfusion :756`, `visitFalseRec :731`, `visitQuotLift :697`, `visitLit :524`.
* `Types.lean`, `MonoTypes.lean`, `Irrelevant.lean` (what is computationally relevant; "trivial structure" = 1 ctor, 1 relevant field → unwrapped), `InferType.lean`.
Passes (`file:line` of the `Pass` def)
* `PullLetDecls.lean:124` `pullInstances` (hoist instance lets so they are visible to simp/specialize).
* `CSE.lean:126` `cse`. `Simp.lean:64` `simp` driven by `Simp/Main.lean:218` (`simp`), with
  `Simp/InlineCandidate.lean:39` (inline decision), `Simp/SimpValue.lean` (proj/ctor/app-app), `Simp/ConstantFold.lean:701`,
  `Simp/JpCases.lean`, `Simp/DiscrM.lean` (knows "x is ctor C a b" in this branch), `Simp/Config.lean`/`ConfigOptions.lean`.
* `FloatLetIn.lean:340` (sink lets into the one `cases` arm that uses them).
* `JoinPoints.lean:648` `findJoinPoints` (turn local `fun` that are only tail-called into `jp`), `:658` `extendJoinPointContext`, `:669` `commonJoinPointArgs`;
  `ReduceJpArity.lean:77`; `PullFunDecls.lean:183`.
* `Specialize.lean:557` (+ `SpecInfo.lean`: `SpecParamInfo` fixedInst/fixedHO/fixedNeutral/user/other; `FixedParams.lean`).
* `LambdaLifting.lean:199` `lambdaLifting`, `:213` `eagerLambdaLifting` (lifts local fns taking instance params *before* specialization).
* `ToMono.lean:447` `toMono` (+ `StructProjCases.lean:135`, `ReduceArity.lean:189`, `ElimDeadBranches.lean:677`).
* `SplitSCC.lean` (re-split mutual blocks after lifting), `ExtractClosed.lean:252`, `Visibility.lean` (public/private for modules).
* Impure: `ToImpure.lean`, `ToImpureType.lean`, `PushProj.lean`, `ResetReuse.lean`, `SimpCase.lean`, `InferBorrow.lean`, `ExplicitBoxing.lean`,
  `ExplicitRC.lean`, `ExpandResetReuse.lean`, `CoalesceRC.lean`, `SimpleGroundExpr.lean`, `Toposort.lean`, `EmitC.lean` (LCNF-level C emitter, 1189 lines).

### The pass order (`Passes.lean:92-150`)
BASE: init, pullInstances, cse, simp, floatLetIn, findJoinPoints, pullFunDecls, reduceJpArity,
simp{etaPoly,inlinePartial,implementedBy}, eagerLambdaLifting, checkTemplateVisibility, **specialize**, findJoinPoints,
simp, cse, saveBase, inferVisibility, **toMono**.
MONO: simp, reduceJpArity, structProjCases, extendJoinPointContext, floatLetIn, reduceArity, commonJoinPointArgs, simp,
floatLetIn, **lambdaLifting**.
(split into SCCs) MONO-no-lambda: extendJoinPointContext, simp, **elimDeadBranches**, cse, saveMono, inferVisibility, **extractClosed**, **toImpure**.
IMPURE: pushProj, **insertResetReuse**, elimDeadVars, simpCase, **inferBorrow**, **explicitBoxing**, **explicitRc**, expandResetReuse,
coalesceRC, pushProj, detectSimpleGround, inferVisibility, toposort, saveImpure → `IR.toIR` → IR checks → EmitC.
Observation: `simp` runs 6 times; it is the workhorse, other passes mostly enable it (e.g. floatLetIn/jp passes expose more).

## 3. Facts that matter for nano (exact semantics / edge cases)
1. **Inline decision** (`Simp/InlineCandidate.lean:39-125`): inline iff not recursive (unless `inline_if_reduce`), and
   `always_inline` ∨ `inline`/`inline_if_reduce` ∨ (¬`noinline` ∧ body `sizeLe smallThreshold`). Default
   `smallThreshold = 1` (`ConfigOptions.lean:23`, option `compiler.small`) — i.e. only *trivial* bodies are inlined without an
   attribute. Requires full application unless `inlinePartial`. `inline_if_reduce` only fires when the `cases`-param arg is a
   constructor application (max 16 recursive unfoldings, `maxRecInlineIfReduce`; plain `inline` recursion max 1).
   Instances marked inline are NOT inlined in the base phase before eager lambda lifting (comment at `:62-90`). So Lean's
   performance depends on user annotations (`@[inline]`, `@[specialize]`) in the stdlib: any nano stdlib port needs the same annotations.
2. **Size**: "size" = number of `let`/`cases` etc. nodes (`Code.size`, `Basic.lean`); threshold counts nodes, not bytes.
3. **Specialization** (`Specialize.lean`, `SpecInfo.lean`): triggers on args in `fixedInst` (type-class instance args, always)
   or `fixedHO` / `user` (functions, only if `@[specialize]`), parameters that are *fixed* across recursive calls. Key = the
   abstracted ground argument expression (`mkKey :288`) → cache so equal instantiations share one copy. Limit `maxRecSpecialize = 64`.
   Specializations are stored for reuse across modules. If a function argument depends on local variables, those get
   closure-converted into extra parameters.
4. **Erasure/mono** (`ToMono.lean`): `Decidable.isTrue/isFalse/decide` ⇒ `Bool.true/false/id` (`:85-90`);
   `cases` on `Decidable` ⇒ `cases` on `Bool` (`:178`); `cases` on `Nat` ⇒ `Nat.decEq x 0` + `Nat.sub x 1` (`:189`); same
   for `Int` via `Int.ofNat`/`Int.natAbs` (`:213-233`); `Array`/`ByteArray` etc `cases` ⇒ accessor calls; trivial structures
   (one relevant field) are represented by the field itself (`trivialStructToMono :347`). Proofs/types become `◾` (erased).
   Consequence: runtime layout is NOT the Lean type; e.g. `Fin n`, `Subtype`, `UInt64` wrapper structs are unboxed/erased.
5. **Constructor layout** (`CtorInfo`, `Basic.lean:144`): objects hold pointer fields first, then USize, then scalar bytes;
   ctors with no fields are boxed scalars (tagged ints). Enums (`Bool`, user enums) are `uint8`/`uint16`/`uint32` by #ctors.
   `cases` on a structure is replaced by projections (`structProjCases`) — structure access never "switches".
6. **Nat literal / big numbers**: literals `< 2^63` are scalars, larger are heap bignums; `ExtractClosed.lean:67` extracts
   a Nat literal as a closed term only if `≥ 2^63` (comment: avoids dependence on `is_scalar`/arch). nano's "arithmetic = bounded" decision
   avoids all of this.
7. **ConstantFold** (`Simp/ConstantFold.lean`) has per-op folders for `Nat/UInt8..64/USize/Char/Bool/String`: arithmetic,
   comparisons, neutral/annihilator laws (`x+0`, `x*1`, `x*0`), `x / 2^k`→shift, `x * 2^k`→shift, `Nat.pow` only if result small
   (`natPowThreshold = 256`, `:464`). USize folding is parametric in 32/64 bit (both computed, only apply if equal). Each folder
   is a semantics-preserving rewrite on literals: a ready-made list of identities to prove for nano's `UInt64` / `BitVec`.
8. **`cases` handling**: `simpCasesOnCtor?` (`Simp/Main.lean:183`) when scrutinee is a known ctor (also literal Nat `0`/`n+1`);
   the *pure* simplifier is deliberately conservative with `cases` so `ResetReuse` still sees them; the liberal clean-up is `SimpCase` (impure).
   `unreach` terminates impossible branches (from `False.elim`, `noConfusion`, dead-branch analysis).
9. **ElimDeadBranches** (`ElimDeadBranches.lean`): whole-program abstract interpretation over values
   (`bot | top | ctor name args | choice [..]`, depth limit `maxValueDepth = 8`, widening at `:175`) with per-function
   result summaries; removes `cases` arms never reachable. Only sound under the closed-world assumption of the module's SCCs
   plus saved summaries of imported decls. Declarations visible to other modules/`@[export]` must assume `top` parameters.
10. **Join points are the loop/CFG construct.** Tail self-recursion stays a recursive call in LCNF; EmitC/IR turn
    self tail-calls into `goto`. Non-self tail calls are NOT guaranteed TCO (`InferBorrow` only preserves tail calls to recursive fns/jps by owning params).
11. **Lambda lifting** (`LambdaLifting.lean:73`): `shouldLift` = size ≥ `minSize` (and, in `eagerLambdaLifting`, only those with
    instance params). The closure becomes `f._lam_N` with captured vars as leading params; the use site becomes a partial application (`pap`).
12. **ExtractClosed** (`ExtractClosed.lean:67-110`): a term is closed if all free vars are themselves extractable; string
    literals always; ctor apps only if some arg relevant; `[never_extract]` honoured; calls into the *current SCC* never extracted
    (avoids init-order cycles); Array/ByteArray literals built by `push` chains extracted as one (`:117`) to avoid quadratic push.
13. **Reset/reuse** (`ResetReuse.lean`; paper arXiv:1908.05647): inserted before RC so that `reset x` (if unique, free fields, keep cell) +
    `reuse` allocation of same size gives in-place update; `ExpandResetReuse` expands to a fast path (`isShared` test, then
    `set` field updates) and slow path. This is where `List.map`/`Array.set!` style code becomes in-place. Needs refcounts at runtime;
    nano has no RC (blocks model, bump allocator) ⇒ only the *analysis* idea is relevant (see §4).
14. **Pipeline order matters for semantics preservation of `@[implemented_by]`/`@[extern]`**: `implementedBy` replacement is done in the
    second `simp` *before* `specialize` (`Passes.lean:105`). Lean's executable semantics ≠ kernel semantics for these; nano ⊆ Lean should
    refuse them (or only accept ones whose spec is proven equal).
15. **`partial`/`unsafe`**: `toDecl` redirects `_unsafe_rec` back to the real name (`ToDecl.lean:131`), so structural/wf recursion is
    compiled from the *pre-definition* (direct recursion), not from `brecOn`/`WellFounded.fix`. Compiled code does NOT follow the kernel
    unfolding; equivalence is by the equation lemmas. nano must do the same (consistent with ROADMAP "kernel-checked equation per function").
16. Debugging oracle: `set_option trace.Compiler true` / `trace.Compiler.result true` prints every pass's LCNF and the final impure form (`Main.lean:56`, `:206`).

## 4. Reuse assessment for nano
Ground truth: every LCNF file is `partial def`/`CoreM`/`MetaM` code over Lean `Expr`, `Environment`, `Name`, `HashMap`,
`Array`, with `panic!`/`unreachable!`, exceptions and trace machinery. None of it is in nano's subset; nano is a *total*, proof-carrying
setting. So **(c) copy-as-is is not available for any pass**: `simp` (`Simp/Main.lean`), `Specialize`, `ElimDeadBranches`
are `partial`, depend on the elaborator (`Meta.isInstance`, `inferType`, `Expr` kernel terms) and on global environment
extensions. Reusing the *implementation* would mean (i) re-architecting around nano's own IR, and (ii) adding fuel/termination arguments
to every fixpoint. Estimates are rough engineering guesses, not measurements.

| Idea | Tag | Notes / proof effort (rough) |
|---|---|---|
| ANF IR with `let / cases / jp / jmp / return` (`Basic.lean:371`) | (a) blueprint | Fits nano's plan; give it big-step semantics, `jp` = local continuation. Defining + interpreter + well-scopedness: small. Lean's IR uses SSA-style fvars; nano can use de Bruijn or flat indexes to make substitution lemmas easier. |
| Phase-indexed purity (`Purity`) | (a) | Good idea: pure phase allows reorder/CSE/float; later phases carry effects/alloc. nano: only needed when memory ops become explicit. |
| Erasure of types/proofs; Decidable→Bool; Nat `cases`→`decEq`/`sub`; trivial-struct unwrapping (`ToMono`) | (a) | Highest value for nano's front end (it already "translates Lean definitions itself"). Each rewrite is a small local equivalence; Nat→`n-1` rewrite is the classic one. Per rule: days to a week once the IR semantics exist. Also (b) oracle: compare to `trace.Compiler.result` for mono shapes. |
| `simpCasesOnCtor`, `elimVar`, dead-`let` removal, beta/inlining with `inline`/`small` heuristic | (a) | Proof = substitution/inlining lemma for the IR (the core "inlining is semantics-preserving" theorem; 1–3 weeks to get right, reused by all later passes). Heuristic *policy* (size ≤ 1, attributes) needs no proof; only legality does. |
| ConstantFold identities (`ConstantFold.lean`) | (a)+(b) | Table of ~100 rules is the easiest proof win: each is a lemma on `UInt64`/`BitVec` (neutral, annihilator, shift for 2^k, relations). Skip String/Task/`USize` (32/64 duality). Easily fuzzed against Lean as oracle. |
| CSE (`CSE.lean`, ~130 lines) | (a) | Needs purity (no effects in pure phase) + scoped map. Small; proof is a "let-bound value equal ⇒ replace" lemma. Low speedup alone. |
| FloatLetIn / PullFunDecls / jp-find / jp-arity reduction | (a) | Mostly code motion in a pure language; each 1–2 weeks. Value: enables fewer spills/closures. Lower priority. |
| Specialization (`Specialize.lean`, `SpecInfo.lean`) | (a), biggest speedup | Generic recursion over instance/function arguments is the single largest win in idiomatic Lean (monomorphic loops instead of dictionary/closure calls). **For nano it can be done more cheaply**: if the source subset has no type classes/higher-order args at runtime (or they are always known) then plain inlining of fixed args + a cache achieves it; proof = "specialized copy = original with arg substituted", by induction on the recursion. Lean's `fixedInst/fixedHO` analysis (`FixedParams.lean`) is a clean blueprint. 3–6 weeks incl. termination/cache. |
| Lambda lifting / closure conversion | (a) | Required if nano allows local lambdas/closures; free-variable computation + substitution lemma. 1–2 weeks. Skip if the subset forbids closures. |
| ElimDeadBranches | (a), optional | Abstract interpretation: needs a lattice and soundness proof with widening — heavy (weeks–months) relative to benefit; do only a simple version (known-ctor `cases`, literal tests) via simp. |
| ExtractClosed | (a), optional | Meaningful only when there is a runtime heap + initialisation order. nano's "bytes in → bytes out, no IO" model has no static init; closed constants can be handled as data in the code section. Low priority. |
| ReduceArity (drop unused params) | (a) | Small and easy (unused-param analysis + wrapper). Moderate speedup for register pressure. |
| ResetReuse + borrow + RC (`impure` phase) | (a) only the *idea* | These solve Lean's refcount cost. nano uses blocks + bump allocator and (per ROADMAP) no RC; analogous nano idea = "update in place when the old value is dead" (linearity/last-use analysis, as `ResetReuse` `D`/`S`), which would need an ownership proof — large (months); skip until arrays/lists are real. |
| ExplicitBoxing | (a) later | nano has uniform 64-bit words; boxing mostly unnecessary except for sums/enums; skip. |
| SplitSCC, Toposort | (a) | Trivial graph passes (Tarjan); mutual recursion groups. Needed if mutual recursion is supported. |
| `Check.lean` / `compiler.check` between passes | (a) | Cheap to port as an executable well-formedness checker; prove it sound once, then every pass can be tested by running it. |
| Whole pipeline as (b) test oracle | (b) | Run real Lean on each test program with `trace.Compiler.result` and compare *shape* (e.g. loops became jp, closures eliminated) and run real Lean results as semantics oracle. Zero proof cost, aligns with invariant 1 fuzzing. Cannot be used as-is for byte-exact comparison: nano's IR differs. |

### Which passes give the big speedups in Lean (judged from the design; I did not benchmark)
1. Specialize + inline of instances (removes dictionaries/closures from loops). 2. simp (case-of-known-ctor, inline, const-fold, dead code).
3. Unboxed scalars via mono types (UInt*/Bool/enums not heap objects). 4. Reset/reuse + borrowing (removes alloc/RC traffic). 5. Join points
instead of closures for control flow. 6. Closed-term extraction (avoids recomputation). For nano without RC/GC: 1, 2, 3, 5 matter; 4 and 6 mostly don't.

### Recommended order for nano (opinion)
(1) IR + semantics + well-formedness checker; (2) erasure/Nat-cases/Decidable rewrites; (3) simp = inlining+case-of-ctor+const-fold with ONE
substitution lemma; (4) join-point recognition; (5) specialization of fixed arguments; (6) ReduceArity/CSE/float. Defer everything in the impure phase.

### Open / unverified
* Worked example is derived from reading the passes, not from running Lean (no Lean toolchain used here).
* I did not read `Lean/Compiler/IR/*` (ToIR, EmitC details) or the old-compiler remnants; line numbers for individual functions not listed above were not checked.
