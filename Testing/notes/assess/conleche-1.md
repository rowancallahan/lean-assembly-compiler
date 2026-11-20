# con-leche, part 1 of 3 (assessment SONNET-ASSESS-01)

Source: `leanprover/con-leche` (shallow clone, toolchain `leanprover/lean4:v4.36.0`, `lakefile.lean`; **not built**). Clone was allowed. Read-only.
Evidence: **read** = from source text / grep counts (regex, approximate); the grep counts are lines, not distinct constructs.
Reused (not redone): `CONLECHE_DEPTH.md` (1 093 functions probed with old `frontx`), `CONLECHE_KNOT.md`, `CONLECHE_S0..S3.md`.

## 0. Slice and overview of the whole program

Split: 1 145 `.lean` files, 308 209 lines; thirds at 102 736 / 205 473. Part 1 = files #1..#241 of the C-sorted list, cumulative 101 638 lines, i.e.
`ConLeche.lean`, `ConLeche/{Accepts,Challenge,Complete*,Denotes,MainTheorem,Model*}`, `ConLeche/{Cached,Driver,Frontend,Kernel}/**`, and `ConLeche/Model/**` up to
`Model/Inductives/GenClsRows.lean`. The boundary file `Model/Inductives/GenClsSem.lean` (ends at cum 103 088) goes to part 2 by "end of file is past the cut".
(`Main.lean`, `OleanCompare.lean`, `PinDump.lean` sort after `ConLeche/…`: part 2.) Lines: Model 56 129 (126 files), Frontend 18 106 (34), Kernel 14 989 (50),
Cached 7 792 (13), Driver 2 247 (8), Complete 1 470 (3), rest ~900.

Whole program (README.md, OVERVIEW.md §0):
1. Entry `Main.lean` → `ConLeche.Driver.runArgs` (`Driver/Cli.lean`) → `checkMainG` (`Driver/CheckMain.lean`). Binary `con-leche [--verified|--trusted] [--jobs=n] [--max-nat-size=B] FILE.ndjson` or `--olean --search-path=DIRS MODULE…`.
2. Input: a `lean4export` NDJSON stream (Lean kernel declarations as JSON, tens of MB to GB for Mathlib) or `.olean` files (binary object graphs, read by a hand-written reader in `Frontend/Olean/*`).
3. Pipeline: parse → build index (`Cached/StreamIndex`) → `preparePrelude` → `Cached.checkDecls` (`Cached/Decls.lean:89`, folds `declStep`) → verdict line + exit code 0/1/2/3 (`CheckError.exitCode`, `Driver/CheckMain.lean:37`).
4. Output: one line (`accepted N declarations` / `rejected …` / `declined …`) on stdout; exit code is the verdict.
5. The checker is a Lean-4 kernel re-implementation (whnf/infer/defeq/inductives/Nat accelerators, memo tables, hash-consed `Expr`) **with a machine-checked soundness proof** (set-theoretic model).

## 1. Size (part 1)

| dir | files | lines | `def` | `theorem/lemma` | role |
|---|---:|---:|---:|---:|---|
| Kernel | 50 | 14 989 | ~821 | ~150 | generic checker (`[Monad m]`, `CoreFns m` record) |
| Cached | 13 | 7 792 | ~450 | ~31 | concrete, memoised twin used by the binary (`CheckCM`) |
| Frontend | 34 | 18 106 | ~602 | ~421 | JSON/olean parsers, prelude, verified parse lemmas |
| Driver | 8 | 2 247 | ~95 | ~19 | CLI, thread pool, IO |
| Model (part) | 126 | 56 129 | ~201 | ~1 281 | soundness proof into set theory (proof only, never run) |
| Complete | 3 | 1 470 | 28 | 32 | parked completeness spec (proof only) |

Executable code in part 1 ≈ Kernel+Cached+Frontend+Driver = **105 files, 41 134 lines, ~1 970 `def`** (regex; includes proof-support defs). Same call graph as DEPTH: 1 103 functions reachable from `whnfBody/inferBody/defeqBody/checkDecl/checkDecls`.
Checker code and Model proofs are separate: **the Model (68 % of the lines, 1 281+ theorems) need not be compiled at all.**
27 lines mention `sorry` in the executable dirs (docstring/comments mostly, **uncertain**).

## 2. Lean features used (counts = matching lines in Kernel/Cached/Frontend/Driver)

| feature | Kernel | Cached | Frontend | Driver | example |
|---|---:|---:|---:|---:|---|
| `inductive/structure/class` | 89 | 23 | 86 | 22 | `Name` `Kernel/Name.lean:28` (3 ctors, `String`/`Nat` payload), `Level` `Kernel/Expr.lean:32` (5), `Expr` `Kernel/Expr.lean:428` (10 ctors; `letE` has 3 recursive fields; `lit`, `proj`), `ConstantInfo` `Env.lean:291`, `Declaration` `Env.lean:335`, `Env` `Env.lean:459`, `FEnv` `FEnv.lean:193`, `CState` `StateC.lean:261` |
| `mutual` | 2 | 4 | 1 | 0 | `CoreC.lean:444..2027` one mutual block of ~70 defs (`reduceNatI`, `whnfI`, …) |
| well-founded recursion (`termination_by`) | 9 | 86 | 120 | 2 | `CoreC.lean:500` `termination_by (lv, 1, 0, 0)` lexicographic over a 68-way packed argument |
| fuel | fuel-bounded loops in generic core | | | | `whnfLoopFuel = 2^62` `Kernel/Core.lean:1120` |
| `partial def` | 2 | 0 | 2 | 3 | `Expr.hasStrLitGo` `Kernel/CheckerBase.lean:69`; `ownerLoop`/`roundsLoop` `Driver/OwnerParse.lean:313,457` (IO) |
| `String`/`Char` | 92 | 8 | 129 | 50 | names (`Name.str … "Nat"` literals, ~hundreds), error messages, `Name.render` `Kernel/Name.lean:236` |
| `Nat` unbounded | 620 | 446 | 720 | 143 | de Bruijn indices, literals (`Literal.natVal`), kernel Nat accelerators `natOpResult` `Kernel/CoreDefs.lean:583` (add/sub/mul/**pow**/div/mod/gcd/land/lor/xor/shiftLeft…) on **arbitrary-size** values; cap `maxNatSizeDefault = 128 MiB` `Cached/StateC.lean:145` |
| `UInt64/32/8/USize` | 62 | 5 | 976 | 15 | hashes, packed `Expr.data` word, byte parsing (Frontend) |
| `Array` | 9 | 52 | 251 | 77 | memo tables, decl arrays |
| `List` | 496 | 297 | 719 | 32 | `List Level`, `List Expr`, `List Name`, recursor rules |
| `ByteArray` | 1 | 0 | 473 | 33 | JSON / olean input bytes (**this is the part closest to our model**) |
| `HashMap/HashSet` (Std) | 38 | 38 | 50 | 0 | `Std.HashMap Expr Nat`, `Std.HashSet Expr` memo, name→`ConstantInfo` index |
| `Option` | 160 | 77 | 268 | 24 | `Option Expr`, `Option ConstantInfo` |
| `Except` | 20 | 9 | 138 | 36 | `CheckM := Except CheckError` `Kernel/Error.lean:42` |
| monads/`do` | 348 | 414 | 269 | 161 | `CheckCM := StateT CState CheckM` `Cached/StateC.lean:307`; generic `[Monad m]` in Kernel |
| typeclasses/instances | 18 | 4 | 15 | 3 | `Hashable/BEq/Decidable` instances, `CheckerIO` class `Frontend/CheckerIO.lean` |
| macro/notation/syntax | 46 | 12 | 108 | 0 | mostly `local notation`, docstring hits (**approximate**) |
| `@[computed_field]` | `Level.hashData` `Kernel/Expr.lean:40`, `Expr.data` `Kernel/Expr.lean:442` | | | | per-node hash/bvar-range/fvar-range/hasLP packed in a `UInt64`, computed by `mixHash` |
| `@[extern]/unsafe/implemented_by` | 23 | 1 | 18 | 5 | `lean_is_exclusive_obj` `Kernel/Exclusive.lean:14,107`; `PtrDecEq`; `natHash` extern `Kernel/NatHash.lean` (C file `native/nat_hash.c`); `Runtime.markPersistent` `Driver/CheckPool.lean:67` |
| IO/threads | – | – | `CheckerIO` | thread pool `Driver/CheckPool.lean`, `Run.lean` | `--jobs`, `Task`s, stderr progress |
| Float | 0 | 1 (docs) | 0 | 0 | none |
| Mathlib / Std | none: `lakefile` has NO dependencies; Std (`Std.HashMap`, `Std.Async.System`) and core only. | | | | |

## 3. Needed vs incidental, cheapest encoding

| feature | verdict | encoding into nano v2 |
|---|---|---|
| `Expr`/`Level`/`Name` inductives (n-ary ctors, 3 recursive fields) | **core** | tagged Buf nodes: `[tag, f1, f2, f3, data]` in one `Buf` arena, node id = index (u64). `letE` fits (4 words). Needs a `case` on tag (nested `if`); no new language feature but 10-way dispatch on every function. |
| `Name` with `String` | **core, mostly incidental** | intern names as u64 ids in a table (`Name.str pre s` → hash-cons node `[tag,pre,strId]`); strings become byte ranges in a input Buf. Name *literals* (`natAddName`, …, hundreds in `Kernel/Basis/Names.lean`) become 0-ary constants / table ids filled by a generated prelude. |
| `Nat` as de Bruijn index/level/length | incidental | `UInt64` + `assert < 2^40` (data word saturates anyway: `satRange` `Expr.lean:241`, 15 bits). |
| `Nat` **literals & accelerators** (`natOpResult`) | **core, hard** | bignum arithmetic. No UInt64 encoding is correct: Lean literals `2^k` etc. appear in Init/Mathlib. Needs a bigint library in Buf limbs (add/sub/mul/div/mod/pow/gcd/land/lor/xor/shifts/log2), or *decline* (con-leche itself `declined`s with exit 2, which is a sound but incomplete fallback). |
| `List α` | incidental | cons-cells in the node Buf (`[tag, head, tail]`) or Buf of ids + length. |
| `Option` | incidental | sentinel id (0 = none) or `[flag,val]` pair; asserts. |
| `Except CheckError` / `StateT CState` monads | **core** (all of Core/Cached) | specialise by hand: thread `(state…)` as explicit tuple/Buf and return `(errcode, value)`; errors by early-return code. DEPTH found 951/1 093 signatures covered once monads + data model exist. |
| `Std.HashMap Expr Nat` memo tables | **performance-core, semantically incidental** | open-addressing table in a `Buf`, key = node id (hash-consing makes `Expr` equality an id compare if the arena is hash-consed) or just drop caches: **cost is exponential on real terms** (that is why the memo exists). Keep. |
| `partial def`, `termination_by` WF over tuple measures | **core** | fuel loop + explicit stack for mutual `whnfI/inferI/defeqI`; recursion is *mutually recursive and deep* (no tail calls), so needs real recursion (IR supports calls, `CONLECHE_KNOT.md`) rather than only the `loop n` pattern. Rewriting to an explicit stack is a full re-architecture. |
| mutual block ~70 defs | **core** | accepted by IR; blocked by front end (no `mutual`, no non-fuel recursion). |
| `String` messages | incidental | error code integers; keep one printed verdict line (`accepted N`/`rejected`/`declined` as byte constants). |
| `@[computed_field]`, `mixHash` | **needed for Hash-consing only** | fixed deterministic mix: any u64 mixer works (not required to equal Lean's `mixHash`) if the *compiled* checker only needs consistency; but the con-leche proofs mention Lean's `mixHash`/`natHash` abstractly (hash is a cache key only), so a replaced hash keeps the soundness theorem. **uncertain**: verify no theorem pins hash values. |
| `@[extern]` `lean_is_exclusive_obj`, `PtrDecEq`, `markPersistent` | incidental (RC/perf tricks) | drop. |
| IO/threads (`Driver/CheckPool.lean`, `--jobs`) | incidental | single-threaded; whole program is a pure function bytes→bytes plus output. |
| JSON NDJSON parser (`Frontend/Export*.lean`, 473 `ByteArray` mentions) | **core** | hand-written byte parser: closest to nano (byte input, Buf output, UInt64 scalars). |
| olean reader (`Frontend/Olean/*`) | optional | skip: use the NDJSON path only. |

## 4. Hard blockers, ranked

1. **Mutual, non-tail recursion** (`whnfI/inferI/defeqI/reduceNatI`, 70-def `mutual` `CoreC.lean:444-2027`, WF measures `(lv, k, …)`). Compiler has only the fuel-loop pattern. Needs either IR-level recursion in the front end + proof (KNOT), or a hand rewrite to an explicit work stack.
2. **Heap data model**: `Expr` (10 ctors, `letE` 3 recursive), `Name`, `Level`, `List`, `Option`, structures `Env/FEnv/CState/ConstantInfo/Declaration`, with `@[computed_field]` hash. DEPTH: ~545/1 087 first failures. Must be hand-lowered to Buf nodes.
3. **Monadic state/error plumbing** (`CheckCM`, generic `[Monad m]`, `CoreFns m` record of closures; DEPTH rows 6, 11).
4. **Unbounded `Nat`** for literals and the kernel accelerators (pow/div/mod/gcd/shift/bit ops at up to 128 MiB). A bignum library.
5. **Size**: ≈1 100 reachable functions vs the 511-def cap (and the node cap, §5).
6. **Hash maps/memoisation** (needed for performance, 38+38+50 mentions) and `String` names.
7. Structure `mixHash`/`natHash` externs (small, one C function `lean_nat_big_hash`, **trust surface**).

## 5. Runtime needs (estimates, **uncertain**)

- Input: `lean4export` of a single theorem is KBs; Init ≈ tens of MB; Mathlib ≈ GB. Ours is ≤ 1 MiB input: **only small test files and tiny preludes fit**. con-leche embeds a built-in prelude (`Frontend/Prelude.lean`, `builtinPreludeE`, 69 lines) so tiny inputs are checkable.
- Output: one line; trivial.
- Memory: `Expr` arena + memo tables; 1 GiB work memory is enough for ≤ 1 MiB inputs.
- Def count: ~1 970 `def` lines in the executable dirs, ~1 100 reachable from the checker roots (DEPTH). **2–4× the 511 cap** before any rewrite; a hand-written fuel/stack checker could be 150-300 defs if only Core/ExprOps/Env/Level are kept (my guess: **uncertain**).
- Parser node cap 16 384: `Expr.lean`+`ExprOps.lean`+`Core.lean` alone are ~4 500 lines of Lean; a single function like `whnfI` is hundreds of lines. Likely **exceeded** for the checker core in one program (per-program, not per-def; **uncertain**, cap applies to the whole program text).
- Heavy computation: defeq/whnf on large terms; `Nat.pow` on literals; exponential without memo. Frame ≤ 250 words: `whnfI`-style functions with many `let`s and 68-way packed arguments may overflow (**uncertain**).

## 6. Easy wins (closest to the subset)

- `bvarOfData/fvarOfData/lpOfData` (`Kernel/Expr.lean:254,257,260`): only UInt64 shifts/masks; compile verbatim (DEPTH). `packData`, `satSucc`, `satPred`, `hash32` likewise (**read**, not run).
- `Level.isNeverZero/combining/simplify` (DEPTH, via `frontx_ind` shape; need an inductive with ≤ 5 ctors).
- `Expr.hasFvar`, `numArgs`, `piResult`, `beqRecursive`, `depth`, `isLit` (S0 table) once `Expr` is encoded as tagged nodes: 1-3 line structural functions.
- `Frontend/Export*` / `Driver/StreamParse.lean` byte-level scanning (UInt64, ByteArray indexing, `Nat` bounded by input length): best first module; hundreds of lines of `ByteArray`+`UInt8` code (**read**, not verified purely scalar: also uses `String`, `Except`, `Array` of records).
- `Level` operations in `Kernel/Level.lean` (267 lines): small, no monad.

## 7. Proof angle

Strongest of the four targets: the program carries its own full soundness proof, so *the source-level spec we would prove our compiled code equals is already a theorem about the same functions*.
- `ConLeche.no_False_declaration`, `main_no_False`, `main_oleans_no_False` (`ConLeche/MainTheorem.lean:116-123` and following): an accepted stream never contains `theorem … : False`.
- `ConLeche.Cached.checkDecls_sound` (`Verify/Cached/MainC.lean:34`, part 2/3), `no_proof_of_Empty_cached` (`:44`), `Model.model_exists` (`MainTheorem.lean`), `checkDeclsPure_sound_of`/`no_proof_of_False_pure` (`Model/Fold.lean:373,421`), per-rule soundness `Model/Rules/*Sound.lean` (`DefEq.*_soundU`, `CertsSound.lean`).
- `Driver.runArgs_accept`, `checkMainG_ndjson_accept` (`Driver/CheckMain.lean`): ties the exit-0 verdict to `checkDecls` on the parsed bytes, **up to a stated trust assumption** about IO (`Frontend/CheckerIO.lean`).
- They are about **Lean semantics** (`Nat`, `List`, `HashMap`, WF recursion), over axioms `propext`, `Quot.sound`, `Classical.choice` (set-theory model with inaccessibles, `SetTheory V` class). Inheriting them needs a theorem "our compiled program = the Lean definition `checkDecls` on encoded input", i.e. the full compiler-correctness proof for Lean functions with these features. The compiler's proof side (Lean function ⇒ IR ⇒ RISC-V) exists only for the accepted subset; the inheritance step is the same one-function-at-a-time gap as KNOT.
- Part 1 proofs themselves (`Model/**`, 56 k lines) are Lean 4.36 on `Std`; building them would need `lake build` on Lean 4.36 (this repo uses 4.29: DEPTH found definitions elaborate unchanged, a few proofs fail: `ite_eq_left/right`).

## 8. Recommendation for staging

1. First targets: the byte-parser tier (`Frontend/Export*.lean`, `Driver/StreamParse.lean`) rewritten over Buf; and `Level`/`Expr` utilities after a tagged-node encoding.
2. Language additions that unlock the most (DEPTH §4): n-ary tagged-record inductives with `Option/List` cells → `Except`/state monad specialisation → mutual/non-fuel recursion → hash map → bignum.
3. Realistic scope for "our compiler runs con-leche": a **stripped checker** (no olean, no threads, no strings, small bignum or decline-on-big-Nat) rather than the verbatim 41 k-line program.
