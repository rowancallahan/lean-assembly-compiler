# con-leche assessment, part 2 of 3 (second third by cumulative lines)

Repo `leanprover/con-leche` cloned `--depth 1` (clone worked, no network issue). Tags: **run** = counted by script, **read** = from source text, **uncertain** = not verified.
Paths are relative to the con-leche root.

## 0. Slice definition
`git ls-files '*.lean' | LC_ALL=C sort`: 1145 files, 308 209 lines. A file is in the second third if its starting cumulative offset is in [102 736, 205 472). That gives **268 files, 102 393 lines**, from `ConLeche/Model/Inductives/GenFrameTie.lean` to `ConLeche/Verify/Denote/OpenRevDenote.lean`. `GenClsSem.lean` straddles the first cut and is assigned to part 1 (uncertain: other parts may split differently).
By directory (lines/files): Model/Inductives 33 347/83; Verify/Cached 19 361/42; Model/Rules 8 559/19; Semantics/Tower 6 440/5; Verify/Deep.lean 3 156; SetTheory/Derive 2 707/17; Verify/Denote 2 597/12; Verify/BetaSpine 1 765; Semantics/Inductives 1 570/7; Model/NatEqs 1 514; Verify/BridgeDecl 1 271; Model/NatSem 1 085; SetModel/{Access,Value} 810+646; PinGen.lean+PinGen/{Dump,Prelude} 638+715+580; rest small.

## 1. Size and role (run)
- **4 065 theorem/lemma vs 817 def/abbrev** (about 5:1 by count; by lines the slice is ~95% proof text). 116 inductive/structure/class, 23 instance, 26 `partial def`, 12 `mutual`, 172 `noncomputable`, 0 Mathlib.
- Entry point of the whole program is `Main.lean` (`main` → `ConLeche.Driver.runArgs`, `ConLeche/Driver/Cli.lean`): it reads a lean4export NDJSON file or `.olean` closure and prints `accepted N declarations` / `rejected`. **None of that is in this slice.** The slice is the soundness proof of the checker (the model-existence theorem `model_exists`, `MainTheorem.lean`, README.md:60) plus the pin-generator.
- The slice holds essentially no code that the shipped `con-leche` binary runs. What the slice contains:
  1. `Model/Inductives/*` (83 files): proofs that inductive-type installation (recursor/iota rules, positivity, nested inductives) has a set-theoretic model. Names: Block*, Gen*, Target*, Cont*, PosDeriv*, NestPos*. 1 440 theorems, 225 defs (read: the defs are `Term`/spec-level data and `Prop`s, not the checker).
  2. `Verify/Cached/*` (42 files): simulation proofs relating the cached/fueled checker loops (`inferLamsI`, `defeqBindersInnerI`, …, `ConLeche/Cached/CoreC.lean`) to pure mirrors, as `Std.WP` triples proved by `vcgen`/`grind` (`Verify/Cached/BinderLoopC.lean`, `DiscC5.lean:168`). 1 276 theorems.
  3. `Model/Rules/*`, `Semantics/Tower/*`, `SetModel/*`, `SetTheory/Derive/*`, `Verify/Deep.lean`: set-theory semantics and kernel-rule soundness (`Model/Rules/{InferSound,DefEqSound,IotaSound,RedSound}.lean`).
  4. **Only genuinely executable pieces: `PinGen.lean` + `PinGen/{Dump,Prelude}.lean` (1 933 lines)**: a build-time tool that walks `Lean.Environment` and writes `con-leche-natop-pins` files (`PinGen/Dump.lean:159`, `PinGen.lean:142,154,187,200,237` are `partial def` over `Lean.Expr`/`Name`/`NameSet`, `Except String`). It uses `Lean.*` meta APIs, `String`, `IO`. Not part of checking.
  5. `Term/{Const,Subst}`, `Rules/{Rel,Derived,Rigid}`: small `Term` calculus (Prop-level relations plus `def`s like `natRecAV`, `Model/Rules/Motive.lean:336`).

## 2. Lean features used (run counts over the slice; examples)
| feature | count | needed? | cheapest encoding / comment |
|---|---:|---|---|
| `theorem`/`lemma` | 4 065 | erased at runtime | contribute nothing to codegen; see §7 |
| `List` mentions | 6 202 | mostly in proofs/spec | runtime List of heap objects → tagged Buf nodes (not supported) |
| `Option` | 925 | spec + code | tagged Buf / 0-sentinel |
| `Except` | 139 | PinGen (`toConLeche : … → Except String …`, `PinGen.lean:154`) | drop; fail fast |
| `do`/`StateT`/`IO` | 322 | `Std.WP` triples, PinGen IO | WP triples are proof-only; PinGen IO not needed |
| `String`/`Char` | 99 | PinGen only (file names, format tag `Dump.lean:159,165`) | Buf of bytes |
| `HashMap`/`HashSet` | 59 | cache types in the mirrored loops | Buf-based open addressing; but only appears in theorem statements here |
| `Array` | 112 | spec | Buf |
| `partial def` | 26 | PinGen (`PinGen.lean:142,154,187,200,237`) | all over Lean meta types → needs real meta-runtime; out of scope |
| `mutual` | 10 | proofs | n/a |
| `termination_by`/`decreasing_by` | 48 | proof-level well-founded defs | fuel loop if executable at all |
| Mathlib | 0 | – | – |
| `Int`, `Float`, `ByteArray` | 0 | – | – |
| `unsafe`/`extern`/`implemented_by` | 5 (hits are strings/comments, e.g. `PinGen/Prelude.lean:377,393`) | none | none real (read) |
| macros/notation/`syntax`/`elab` | 19 | proof/spec notation | cannot compile; must be expanded, inapplicable to codegen |
| `Std.WP`, `vcgen`, `grind`, `experimental.vcgen` | throughout `Verify/Cached` | proofs | needs Lean 4.35 toolchain; not codegen |
| imports | `Lean`, `Std.WP`, `Std.Tactic.Do.Syntax`, `Std.Data.String.ToNat`, `Lean.Meta.Tactic.Grind.*`, `import all Init.Data.Nat.Gcd` | – | `module`/`public import` module-system syntax in every file (read) |
No `Float`, no typeclass-polymorphic runtime code other than the `[SetTheory V]` universe-level proof structure (`Model/*`, 7 038 mentions of `V`/`SetTheory`).

## 3. Hard blockers (ranked, for this slice)
1. **Nothing in this slice is a program.** 95% is propositions and proofs; there is no input→output function to compile. Compiling the slice means compiling zero runtime semantics, or "compiling" proofs, which has no meaning in nano v2. The compile-worthy code for con-leche is in `ConLeche/Kernel`, `ConLeche/Cached`, `ConLeche/Frontend`, `ConLeche/Driver` (other parts).
2. Spec-level `noncomputable` defs over `SetTheory V` (172) cannot be compiled by any compiler, by design.
3. PinGen (`partial def` over `Lean.Environment`, `Lean.Expr`, `NameSet`, `IO`): needs the Lean meta runtime; also a build-time tool, so skip.
4. Module-system syntax (`module`, `public import`, `@[expose] public section`) in the front end: the nano parser accepts none of it (read; same as depth note E1).
5. For the real checker that these proofs are about: the earlier probes apply unchanged, translated to nano v2: `Expr` with 10 ctors and 3 recursive fields in `letE`, `Name` with `String`/`Nat` payload, `List`/`Option`/`Array` of heap objects, `Except`/`StateT` monad, record-of-closures `CoreFns`, `HashMap` caches (`CONLECHE_DEPTH.md` §2 rows 1-14). These are not in this slice.

## 4. Runtime needs
Slice-only: none (nothing runs). The PinGen tool's input is a Lean `Environment`; not representable as nano input. Whole-checker figures are in `CONLECHE_S*.md`. Def count of the slice, 817, exceeds the 511 cap if one counted it, but 96% are spec defs and are irrelevant; PinGen alone has 70 defs (35+19+16, read).

## 5. Easy wins
Few, and none in this slice's executable code. Candidates in the slice for isolated, pure, scalar-shaped functions: none found among the top def-bearing files (`Verify/Cached/DiscC5.lean` 36 defs, `Semantics/Tower/SumTower.lean` 33, `SetModel/Value.lean` 26, `Model/Rules/Motive.lean` 23). Reasons (read): their defs are `Prop`s, `Term` builders over `inductive Term`, or WP predicates, not scalar functions. `Model/Rules/Motive.lean:280-406` (`natAV`, `numeralAV : Nat → Term`) build `Term` trees and need a user inductive. For executable easy wins look at the leaves already identified: `bvarOfData`, `fvarOfData`, `lpOfData` (`Kernel/Expr.lean:254-260`, `CONLECHE_DEPTH.md` §1).

## 6. Proof angle (important)
This slice is the proof angle for con-leche. The program does carry its own proofs, but they are about the **Lean-source** definitions of the checker, not about code our compiler emits.
- Top theorem: `model_exists` (`ConLeche/MainTheorem.lean`; README.md:60): `checkDecls … = .ok env → Nonempty (Model V env)`; corollary `no_False_declaration` (`MainTheorem.lean:116`). Related: `Driver.runArgs_accept`, `ConLeche.main_no_False` (`Main.lean` comment), `checkDecls_consts` (`Model/StreamConsts.lean:220`), `Frontend.preparePrelude_perm` (`Verify/Frontend/Prepare.lean:171`).
- In this slice: kernel-rule soundness (`Model/Rules/InferSound.lean`, `DefEqSound.lean`, `IotaSound.lean`, `RedSound.lean`, `Sound.lean`); inductive-type installation models (`Model/Inductives/*`); simulation of the cached loops against pure mirrors (`Verify/Cached/*`, `Verify/BinderLoop.lean`, `Verify/BetaSpine.lean`); depth/shift invariants (`Verify/Deep.lean:3105 whnfCore_depth_inv`, `:3114 whnf_depth_inv`, `:2971 shiftClaims`).
- **Inheritance is not automatic.** These theorems mention Lean's compiled definitions (`checkDecls`, `whnfBody`, …) through Lean's kernel semantics; our nano compiler would compile a re-encoded version over Buf/UInt64. To inherit them one would need a refinement proof from the re-encoded program to the original Lean definitions (large; the Lean defs use `Nat`, `Expr`, `HashMap`, monads). The `Std.WP` triples in `Verify/Cached` are a template for such a bridge, but are in-Lean-monad.
- Trust: `LEAN_ABORT_ON_*`, `Main.lean` plumbing "read, not proved" (Main.lean header); `tests/trust-surface` greps the sources (read). 12 `sorry` mentions in the slice are all in comments/strings (`PinGen/Prelude.lean`, `Model/StreamConsts.lean`; read, not exhaustive).

## 7. Recommendation (slice only)
- Do not target any file of this slice. Mark Model/, Verify/, Semantics/, SetModel/, SetTheory/ as **proof-only**: they must still *build* if con-leche is kept as a Lake project, but they do not enter the compiler input.
- Target the executable part (`Kernel`, `Cached`, `Frontend`, `Driver`, parts 1 and 3) after adding user inductives (`Expr`, `Name`, `Level` as tagged Buf nodes), `List`/`Option` of those, `Except` and a fuel convention for the 103 fuel/mutual functions.
- Uncertain: exact def count per file used regex line matches (`def`/`abbrev` at line start); `instance`-derived defs and `where` auxiliary defs not counted.
