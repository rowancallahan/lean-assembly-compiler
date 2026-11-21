# con-leche proving core: back-end features nano needs (ranked)

Question: which features must nano's planned Expr entry point (elaborated `Expr`: casesOn, recursors, matchers,
projections, instances, Nat literals) support to compile con-leche's **proving core**, and what share of the core
does each one block? Read-only analysis (2026-11-21). Nothing was built or run through Lean.
Tags: **data** = counted from existing probe output; **est.** = regex over source text (an estimate).

## 1. Method

- **The core.** It is the reach set of the depth-2 probe (`CONLECHE_DEPTH2.md`, branch `keep_round1_conleche-depth2`,
  `Testing/conleche-depth2/out/`). Roots: `whnfBody`, `inferBody`, `defeqBody` (`Kernel/Core`), `Expr.instantiate1`,
  `checkDecl`, `Cached.checkDecls`. Source: con-leche @`6810492c1`, the 56 files in the import closure of
  `Kernel/Core` + `Cached/Decls` (`out/F2P.lean`). That is 1 093 resolved names. I dropped 12 pretty-printing and
  message functions (`Display.*`, `Name.render`, `nonStdAxiomMsg`, `divModAttemptReason`), which leaves **N = 1 081**:
  668 in `Kernel/*` (the generic checker, run through the `CoreFns` knot) and 413 in `Cached/*` (the concrete twin
  `CoreC`, plus the inductive passes). The core contains no parsing or IO.
- **Features per function** (est.): regexes over each definition's signature and body, with comments stripped. The
  definitions were re-indexed with the same rule as the branch's `index.py`. Examples: an `Expr|Level|Name|Literal`
  token means "inductive family"; a constructor in result position (`=> .app …`, `mkApp…`, `.str "…"`) means
  "allocates a hashed node"; a self-name in the body means recursion, split into `termination_by` (well-founded),
  `partial`, `mutual` block, or structural. The regexes over-match in some places (for example, any `"` counts as
  String) and miss in others (for example, `==` on `Nat` versus on `Expr`).
- **Baseline = today's nano fragment** (`NANO_V2_SPEC.md` §1, `EXPR.md` §1): `UInt64`; `Nat` as fuel only; `Bool` only
  inside `if` conditions; affine `Buf`/`List UInt8`; pairs; tail-only fuel loops; no `/` or `%`. So any feature
  outside that list blocks a function.
- **Measures** per feature F:
  - *need*: the functions whose text uses F.
  - *sole*: the functions whose only missing feature is F.
  - *last-missing*: the functions still blocked when every feature except F is present, counted through the call
    closure (a function compiles only if all its callees do). The call graph is the name graph from `index.py`. It
    over-approximates and forms one large SCC (`CONLECHE_DEPTH2` §2), so *last-missing* is an **upper bound**.

## 2. Ranked table

| rank | feature (what nano must add) | need (of 1 081) | sole | last-missing (upper bd) | depends on |
|---:|---|---:|---:|---:|---|
| 1 | **Inductives + casesOn + heap**: user inductives with n-ary ctors (`Expr` 10 ctors, up to 3 recursive fields; `Level` 5; `Name` 3; 16 enum-like types), `Option`/`List α`/`Except`/`Prod` of heap values, `Bool` as a value; a *shared* immutable heap (RC or GC; `Buf` is affine today) | 1 030 (95.3%): family 853, others only 156; Bool value 352 | 32 | 97.4% | none (base) |
| 2 | **Structures / projections**: one-ctor records (`Env`, `FEnv`, `ConstantInfo` vals, `ProjTable`, `CState`, `NestCtx`, `BlockShape`, …, 42 structures), `.proj`/accessor constants, `⟨…⟩`, `{ s with }` | 576 (53.3%) | 5 | 72.4% | 1 |
| 3 | **Recursion beyond tail fuel loops**: real calls with a stack (IR `call` exists, `CONLECHE_KNOT.md`); structural recursion through `brecOn` read via equation lemmas, not the `brecOn` term | structural 313 (29.0%, 39 with a fuel argument); well-founded 82 (7.6%, 78 in `Cached`); mutual 78 (7.2%: one 70-def block `Cached/CoreC:404-1961`, 4 `Level`, 4 `ExprOpsC`); partial 1 | 0 | struct. 78.4%, WF 28.6%, mutual 32.3% | 1; WF/mutual after structural |
| 4 | **Computed fields / mixHash**: every `Expr`/`Level`/`Name` allocation runs its `@[computed_field]` (`mixHash`, `hash32`, `packData`, `Hashable Nat`, `String.hash` for `Name.str`) | 248 (22.9%): 243 allocate, 5 read the hash | 0 | 79.2% | 1, UInt64 `/` `%`, 7 (String.hash) |
| 5 | **Nat as a value (bignum)**: indices, counts and fuel constants (`whnfLoopFuel = 2^62`); `Literal.natVal` holds a Nat of any size | 551 (51.0%) use `Nat`; 22 (2.0%) use non-trivial ops | 15 | 75.0% | none |
| 6 | **Type classes / instances**: (a) monads: `[Monad m]` + `CoreFns m` (Kernel), `CheckCM = StateT CState (Except CheckError)` (Cached), `do`/`←`/`throw`; (b) `BEq`/`DecidableEq`/`Hashable` instances on `Expr`/`Name`/`Level` (pointer- and hash-guarded `decEqPtr`) | monad 397 (36.7%); eq/hash inst. 196 (18.1%); union 510 (47.2%) | 0 | monad 45.2%, eq 63.5% | 1, 2, 8 (bind's continuation), specialisation |
| 7 | **Closures / higher-order**: `fun`, `List.map/all/any/foldl`, function parameters, the `CoreFns` record of closures (the Kernel knot) | 332 (30.7%) | 0 | 69.9% | 1, 3 |
| 8 | **Strings / Name literals**: of 271 (25.1%), 200 only build error text, 60 build `Name` literals (`natName.str "add"`), and 11 have `String`/`Char` in the signature; also String equality and `String.hash` | 271 (25.1%) | 0 | 56.3% | 1 |
| 9 | **Core library closure**: `List.length/reverse/zip/++/lookup…`, `min`/`max`, compiled through the same Expr entry or as builtins | 215 (19.9%) | 0 | 55.5% | 1, 3, 7 |
| 10 | **HashMap / HashSet / Array**: `Std.HashMap Expr Nat`, `HashSet Expr`, memo tables (`HTab`, `BTab`, `NTab`, `BeqMap`); `Array Expr` | hashmap 140 (13.0%; 90 in `Cached`), array 56 (5.2%; 47 in `Cached`) | 0 | 60.6% / 34.4% | 1, 2, 4, 6b, 7 |
| 11 | **Erasure**: types, proofs, `Decidable`, `Subtype`/`Squash` (`ResXP`), and 6 type-level defs that have no code | 115 (10.6%) explicit (est.) | 1 | 44.7% | none |
| 12 | **Int** (`Level.leqCore/rest/imaxRules/byCases`: offsets) | 4 (0.4%) | 0 | 30.7% (under `Level.leq`, so sort defeq) | 1, 3 |
| 13 | **RC / pointer primitives**: `withExclusive` (`@[implemented_by]`, refcount = 1), `USize`/`UInt32` addresses (`beqKey`, `withAddr`, `probeHit`, `recordEq`) | 2 + 4 (0.6%) | 0 | 37.9% / 0.6% | 1 (RC heap) |

**Needs per tier** (est.): Kernel (668) vs Cached (413). Inductives 95% / 96%; structures 55% / 50%; Nat 42% / 65%;
monad 28% / 52%; closures 27% / 36%; mixHash 27% / 17%; strings 27% / 22%; HashMap 7% / 22%; WF + mutual 1% / 37%.
So Kernel trades WF/mutual recursion and the HashMap for generic monads and the `CoreFns` closures.

**Greedy order, direct measure** (est.; cumulative functions whose own features are all covered, of 1 081):
inductives 32 → +structures 92 → +Nat 139 → +recursion 204 → +classes 331 → +closures 420 → +other (lib, erasure, Int,
RC) 532 → +strings 682 → +mixHash 896 → +collections 1 081. Under the closure measure, almost nothing unlocks until
the last step (17% after 6 features): this is the over-approximated SCC. The cost is all-or-nothing for the roots
`whnfBody` (closure 248), `Cached.whnfI` (451) and `Cached.checkDecls` (917).

## 3. Nat: which operations (data, from the source text)

- Bignum arithmetic is in one place: literal folding, `natOpResult` (`Kernel/CoreDefs`) and its twin
  `Cached.NatBinOp.result`. They use `- 1` (pred), `+`, truncated `-`, `*`, `^`, `/`, `%`, `Nat.gcd`, `Nat.land`,
  `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`, `=` and `<=` (into `Bool.true/false` consts).
- `checkDivModPin*`, `natSizeBytes` (`log2`) and `natOpRefusal` guard their costs.
- Everywhere else, Nat is small: de Bruijn indices, `max`/`succ` (17 and 26 functions), `toNat`/`ofNat`.
- Suggestion: a tagged word with a bignum fallback. Small-Nat semantics (truncated `-`, no wrap) are needed in 551
  functions. The bignum operations are needed for literal folding only (about 22 functions).

## 4. What compiles with today's fragment

**None of the 1 081** (est., consistent with the data: the only `frontx_compile` passes in the depth-2 probe were
`bvarOfData`, `fvarOfData`, `lpOfData` and `Display.unsafeChar`, all through the Lean-hosted front end, not nano).
The functions closest to the fragment:
- 12 zero-argument `Nat` constants: `whnfLoopFuel`, `defeqLoopFuel`, `whnfCoreLoopFuel`, `checkFuel`, `bindersFuel`,
  `unitLikeFuel`, `peelFuel`, `Level.defaultFuel`, `fuelSlack`, `satRange`, `natCountMax`, `Cached.instCCapC`. They
  need only "Nat as a value" (nano's zero-argument defs are `UInt64` only).
- `bvarOfData`, `fvarOfData` (`UInt64 → UInt64`, `w / 65536 % 32768`); also, outside the reach set, `hashOfData` and
  `hash32`. They need only UInt64 `/` and `%`. `lpOfData` also needs a `Bool` result, `packData` a `Bool` parameter,
  and `natSizeBytes` needs `log2`.
- The `mixHash` port itself (`Legacy/Riscv/Frontx/MixHash.lean`, `MIXHASH_PORT.md`: 1M-pair fuzz, `wa_compile`
  theorem) is pure UInt64 and already in nano's fragment. `String.hash` (MurmurHash64A, seed 11; `MIXHASH.md` §1 on
  branch `keep_round1_mixhash`) has no port yet.

## 5. Suggested order (dependencies first; cheap scalar items early)

1. **Scalar quick wins**: UInt64 `/` `%`, `Bool` values, zero-argument constants, and Nat as a tagged word with a
   bignum fallback (§3). Unlocks the 15 above plus the packed-data readers that the hash fields need.
2. **Shared heap + inductives + casesOn/matchers**, then **structures/projections** (rows 1–2). Together they are the
   data model: 95% / 53% need.
3. **Computed fields** (row 4): `mixHash` (done), `hash32`/`packData`, `Hashable Nat`, then `String.hash` together
   with static string literals (row 8). No `Expr`/`Name`/`Level` can be built without them.
4. **Non-tail and structural recursion** driven by equation lemmas (row 3a). `Expr.instantiate1` (features: inductive,
   Nat, recursion, allocation) is the first target.
5. **Erasure + instance unfolding** (`BEq`/`DecidableEq`/`Hashable`), then the **core library closure** (rows 6b, 9, 11).
6. **Closures** by specialisation or lambda lifting (row 7), then **monads**. Follow `CONLECHE_KNOT.md`: compile
   `Cached/CoreC` first (the monad is fixed, so there is no `CoreFns`), and specialise the generic Kernel later.
7. **WF + mutual recursion** (the 70-def `CoreC` block), **HashMap/Array** (Cached memo tier), then **Int** and the
   **RC primitives** (`withExclusive` needs the heap's refcount to have a stated meaning).

## 6. Cross-check with earlier data, and caveats

- **Earlier probes agree on the order: data model first, then monad, then collections.** `CONLECHE_DEPTH.md` §4
  (frontx, Lean-hosted) covers 951 of 1 093 signatures after Name + Expr + structures + Option + List + Level +
  higher-order + monad. `CONLECHE_DEPTH2.md` §3 puts structures → monad → collections at 757 / 1 101.
  `BLOCKER_YIELD.md` §3: in frontx's greedy, 0-ary constants and translator shape come first, because frontx already
  has inductives (46 functions pass its gate); nano starts lower.
- **Prior art in `Legacy/Riscv/Frontx`**: `ExprExamples.lean` (`Expr` with a 3-child `letE`), `IndExamples.lean`,
  `ConLecheBlk.lean` (Name constants from chunked string literals), `ConLecheHard.lean` (constant-scalar
  specialisation, nested patterns, `Option Expr` results), `ConLecheS1–S3.lean`. All work at the Lean level, and none
  hashes nodes: a function that reads `e.data` is rejected (`ExprExamples.lean` header). That remains the open semantic
  point for row 4.
- **No nested or mutual inductive types** among con-leche's own types: no constructor field is
  `List/Array/Option <Self>` (checked over the 32 `inductive` declarations). "Nested/mutual" matters only for recursion
  (row 3).
- All per-feature counts are regex estimates. Counts of the form "x of 1 093/1 101" from earlier notes are run data.
  Bodies were never compiled, so having every feature in place is necessary, not sufficient. `checkDecl` and
  `Cached/ExprNodes` are outside the source file (`CONLECHE_DEPTH2.md` §2).
