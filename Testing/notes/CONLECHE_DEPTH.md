# con-leche depth probe: the checker core's call graphs through the front ends

Source: `leanprover/con-leche` @ `6810492c1` (Lean 4.35). Compiler: this repo @ `main`, Lean 4.29.0, front ends `frontx_compile` (bytes/scalars)
and `frontx_ind` (user inductives, `Riscv/Frontx/IndCmd.lean`). No compiler source was modified. Companion: `CONLECHE_SURVEY.md` (branch
`conleche-survey`: leaf functions only). Evidence tags: **run** = the front end's own message; **read** = from source text, not run.

## 0. What was done

1. The 56 files in the import closure of `Kernel/Core` and `Cached/Decls` (22 160 lines) were concatenated in import order into one Lean 4.29 file
   (`out/F2.lean.txt`, generator `scripts/gen.py`). Only edit E1: `module` / `public import` / `meta import` / `@[expose] public section`
   lines commented out. All definitions elaborate unchanged on 4.29. A few proofs fail (`ite_eq_right`/`ite_eq_left` unknown, some
   `rewrite`/`unsolved goals` in `Kernel/Inductives`, one `PinGen` `#` command): irrelevant to the functions.
2. Roots: `whnfBody`, `inferBody`, `defeqBody` (`Kernel/Core.lean:1153,1226,1830`), `Expr.instantiate1` (`Kernel/ExprOps.lean:27`),
   `checkDecl` (`Kernel/CheckDecl.lean:169`), `Cached.checkDecls` (`Cached/Decls.lean:89`). Call graph = identifier references between
   non-theorem defs (`scripts/reach.py`, names of ≤ 3 letters dropped). **An over-approximation**: calls through the `CoreFns` record fields are
   invisible, and same-short-name collisions add edges. Result: 1 103 functions.
3. Each one: `frontx_compile ConLeche.f` on the verbatim definition (`scripts/mkprobe2.py`, messages in `out/F2.msgs`). For the 78
   whose first failure names only `Name`/`Level`: also `frontx_ind f on TName|TLevel` (`frontx_ind_type TName := ConLeche.Name` and
   `TLevel := ConLeche.Level` are accepted; `frontx_ind_type TExpr := ConLeche.Expr` is **rejected: `Expr.letE: more than two recursive fields`**).
4. 10 names did not resolve (`beside.Expr.mkApp`, … in `Cached/ExprNodes`): excluded. **1 093 probed.**

## 1. Result

- **6 of 1 093 compile verbatim**: `bvarOfData`, `fvarOfData`, `lpOfData` (`Kernel/Expr.lean:254,257,260`; `frontx_compile`), and `Level.isNeverZero`
  (`Kernel/Level.lean:55`), `Level.combining`, `Level.simplify` (`frontx_ind … on TLevel`: "5 arms, 16/20 locals"). The last three were rejected in the
  survey (before `frontx_ind` existed). I did not run `implements1`/QEMU for them in this probe.
- **The type gate decides.** The translator checks result type, then parameter types, before the body. 1 062 of the 1 087 rejections are
  `unsupported result/parameter type`, so the table is mostly "which type", and later blockers are hidden (`→ read` below).
- The roots themselves fail at once: `whnfBody`, `inferBody`, `defeqBody` at `m Expr` / `m Bool`; `checkDecls` at `Except (CheckError × Nat) Env`;
  `instantiate1` at `Expr`.

## 2. Blocker table (sorted by impact)

"first (run)" = of the 1 093, how many have this class as **first** message. "sig" = functions whose signature mentions it (*read*; includes ones
blocked first by something else). "trans" = functions with a callee in their closure whose signature mentions it (*read*, **upper bound**: the
name graph forms one large SCC). Example = `function file:line` in con-leche.

| # | feature | first (run) | sig | trans | example |
|---|---|---:|---:|---:|---|
| 1 | `Expr`: 10 ctors, `letE` has 3 recursive fields, plus `List/Option/Array Expr` | 232 | 657 | 850 | `Expr.instantiate1` `Kernel/ExprOps.lean:27`; `Expr.liftLooseBVars` `ExprOps.lean:677` |
| 2 | `Name` (`String`/`Nat` payload), incl. `Name.str (…) "Nat"` literals as constants | 26 + 61 | 329 | 820 | `natBeqName` `Kernel/Basis/Names.lean` (`frontx_ind: Name.str has no equations`); `Name.render` `Kernel/Name.lean:236` |
| 3 | `List` of non-bytes (`List Level/Expr/Name/ConstantInfo`) | 18 | 425 | 686 | `checkDeclKind` `Kernel/CheckDecl.lean:29`; `Level.subst` `Level.lean:33` (`List Name`) |
| 4 | multi-field structure/record (`Env`, `FEnv`, `ConstantInfo`, `Declaration`, `ProjTable`, …) | 226 | 553 | 662 | `Env.find?` `Kernel/Env.lean:467`; `mkFEnv` `FEnv.lean:93`; `basisNamesOk` `Basis.lean:144` |
| 5 | `Option` of heap object (`Option Expr`, `Option ConstantInfo`) | 18 | 179 | 607 | `unfoldDefinition` `CoreDefs.lean:105`; `natOpResult` `CoreDefs.lean:583` |
| 6 | higher-order args (`k : Expr → m Expr`, `Name → Option ConstantInfo`, record of closures) | 0 | 60 | 549 | `whnfStep` `Core.lean:1135`; `Cached.memoBI` `CoreC.lean:348`; `coreKnot` `Core.lean:1868` |
| 7 | `Level` outside the `frontx_ind` shape (`Int` index, `List Level`, `PropWhen`) | 2 + 4 | 129 | 517 | `Level.leq` `Level.lean:145` (`Int`); `Level.isEquiv` `:164` (`ite.eq_1 has no constructor pattern`) |
| 8 | `HashMap`/`HashSet`/`CState` caches | 9 | 65 | 500 | `Expr.bvarBoundGo` `ExprOps.lean:153` (`Nat × HashMap Expr Nat`); `Expr.allLevelParamsDefinedXP` `Cached/ExprOpsC.lean:2327` |
| 9 | type-class / universe / dependent: `Type`, `Decidable (a = b)`, `{h // …}`, `Squash`, `[BEq α]` | in 11 | 19 | 451 | `CheckM` `Kernel/Error.lean:42` (result `Type`); `Expr.decEq` `Expr.lean:840`; `Expr.instantiateRevXP` `ExprOpsC.lean:741` |
| 10 | nullary constants (0-ary `def`: fuel, ranges) | 14 | 14 | 435 | `satRange` `Expr.lean:241`; `whnfLoopFuel` `Core.lean:1116` (`introN failed`) |
| 11 | state monad / `Except` / `[Monad m]` (`CheckM`, `CheckCM = StateT CState …`, `CoreFns m`) | 444 (with 9) | 350 | 383 | `whnfBody` `Core.lean:1153` (`m Expr`); `Cached.checkDeclC` `Cached/ParsedC.lean:318` (`CheckCM FEnv`) |
| 12 | `Array` of heap objects | 6 | 39 | 361 | `Expr.instantiateRev` `ExprOpsC.lean:780`; `iotaRecI` `CoreC.lean:961` |
| 13 | `Int` | 4 | 4 | 334 | `Level.rest` `Level.lean:96`, `Level.byCases` `:128` |
| 14 | `String`/`Char` algorithms | 15 | 21 | 308 | `Display.codeEscape` `Name.lean:158` (translator crash `unknown free variable`), `Display.unsafeChar` (`Char`) |
| 15 | `partial def` | 1 | 1 | – | `Expr.hasStrLitGo` (`no unfolding equation`) |
| 16 | `USize` | 1 | – | – | `Expr.beqKey` |

Body features (*read*, grep over probed functions): fuel/mutual 103 functions, `termination_by` 81, big-`Nat` ops (`Nat.div/mod/gcd/pow/shift/land`) 11,
`mixHash`/pointer-equality primitives 1 directly. Every `Name`/`Level`/`Expr` constructor also runs a `@[computed_field]` with `mixHash`
(no Lean definition: survey §0.4), inside the inductive rather than per function.

## 3. Call-graph trees (status = first message, **run**; `→` = next blocker, **read**)

```
whnfBody [Core:1153]                         BLOCKED result m Expr  → [Monad m], record CoreFns m, fuel loop
├─ whnfLoopFuel [Core:1116]                  BLOCKED nullary constant (2^62)
└─ whnfLoop [Core:1147]                      BLOCKED m Expr
   └─ whnfStep [Core:1135]                   BLOCKED m Expr  → k : Expr → m Expr, do-notation over m
      ├─ r.whnfCore / r.whnf (knot fields)   no call edge for the front end; coreKnot [Core:1868] BLOCKED CoreFns m
      ├─ reduceNat [Core:173]                BLOCKED m (Option Expr)
      │  └─ natOpResult [CoreDefs:583]       BLOCKED Option Expr → 16 Name comparisons, big-Nat ops, allocation of Expr.lit
      ├─ unfoldDefinition [CoreDefs:105]     BLOCKED Option Expr → Env lookup, instantiateLevelParams
      └─ Expr.isLit [Core:1119]              BLOCKED parameter Expr (a one-constructor test)

Expr.instantiateRev [ExprOpsC:780]           BLOCKED result Expr (Array Expr arg)
├─ Expr.bvarB [ExprOps:214]                  BLOCKED parameter Expr
│  ├─ Expr.bvarBRaw [Expr:485]               BLOCKED parameter Expr
│  │  └─ bvarOfData [Expr:254]               COMPILES
│  ├─ satRange [Expr:241]                    BLOCKED nullary constant
│  └─ Expr.bvarBoundMemo → bvarBoundGo [ExprOps:153]   BLOCKED Nat × HashMap Expr Nat
├─ Expr.resTerm [ExprOpsC:122]               BLOCKED result Expr
└─ Expr.instantiateRevXP [ExprOpsC:741]      BLOCKED result Squash (ResXP …)  → HashMap memo, dependent result, WF recursion
   ├─ Expr.MemoXP / HTab [ExprOpsC:204,208]  BLOCKED result Type
   └─ Expr.mkApp/mkLam/mkForallE/mkLetE/mkProj [ExprNodes:96-109]   unresolved by my name matching (not probed)

Cached.checkDecls [Decls:89]                 BLOCKED result Except (CheckError × Nat) Env
├─ Env.empty [Env:465]                       BLOCKED result Env
├─ mkFEnv [FEnv:93]                          BLOCKED FEnv
│  ├─ mkIdxGo [FEnv:82]                      BLOCKED HashMap Name ConstantInfo
│  └─ mkTblsGo [FEnv:88]                     BLOCKED HashMap Name ProjTable
└─ Cached.declStep [Decls:52]                BLOCKED Except … (Nat × FEnv)
   ├─ andPinOk [Basis:209]                   BLOCKED parameter Declaration
   └─ Cached.checkDeclStepC [ParsedC:343]    BLOCKED CheckCM FEnv
      ├─ Cached.flushC [StateC:508]          BLOCKED CheckCM Unit
      └─ Cached.checkDeclC [ParsedC:318]     BLOCKED CheckCM FEnv
         ├─ basisNamesOk [Basis:144]         BLOCKED parameter Declaration  → List ConstantInfo, Name equality
         └─ Cached.checkDeclKindC [ParsedC:255]   BLOCKED CheckCM FEnv
            ├─ natOpDeps / natOpEquations [CoreDefs:523,550]   BLOCKED List Name / List (Expr × Expr)
            ├─ Env.find? / FEnv.find? [Env:467, FEnv:122]      BLOCKED Option ConstantInfo
            └─ … about 20 more (inductive checks, pins, nonStdAxiomMsg: String crash)
```

`Expr.instantiate1` (`ExprOps.lean:27`) is a plain 10-way structural match with `d+1` under binders; first failure: result type `Expr`, and its body has no other
construct, so it is exactly row 1.

## 4. Smallest feature set that unblocks the most

Greedy over *signature* features (*read*): number of functions whose every signature feature is in the chosen set. This is necessary, not sufficient
(bodies, and the one-function-per-program rule, can still reject; the 75 at step 1 are mostly `Name` constants, which need `String` literals). Baseline:
13 of 1 103 have no listed feature, 3 of them compile.

| step | add | covered |
|---|---|---:|
| 1 | `Name` | 75 |
| 2 | + `Expr` | 186 |
| 3 | + multi-field structure/record | 325 |
| 4 | + `Option` of heap objects | 389 |
| 5 | + `List` of non-bytes | 554 |
| 6 | + `Level` beyond the `frontx_ind` shape | 595 |
| 7 | + higher-order args | 622 |
| 8 | + state monad / `Except` / `[Monad m]` | **951** |
| 9 | + `HashMap` | 1 009 of 1 093 |

1. Data model first: `Expr` 232 + structure 226 + `Name` 87 = 545 of the 1 087 first failures (about half). The current `frontx_ind` shape (≤ 2 recursive fields +
   one scalar per constructor, other fields dropped) is the wall: `Expr.letE` has 3 recursive fields, `Name.str` a `String`. Steps 1-5 amount to one feature,
   **n-ary constructors/structures with typed fields (pointer, scalar word, String) and `Option`/`List` as cells of the same kind**: ~550 signatures.
2. Largest multiplier after that: the monad (+329 at step 8; 444 first failures). `CheckM = Except CheckError` and `CheckCM = StateT CState CheckM` have to be
   *specialised* (the `[Monad m]` resolved at use site); §16 has `Except` only for scalar payloads.
3. Independent and small: nullary constants (14), `String`/`Char` (15), `Int` (4), `partial` (1).
4. `HashMap`/`Array` of heap objects (9 + 6 first) matter last: they sit under the cached tier and need 1-2 first.
5. Semantic decision, not engineering: allocating any hashed `Name`/`Level`/`Expr` needs a stated meaning for `mixHash` (survey §0.4). `Level.simplify` is accepted
   through `frontx_ind`, whose `Level` cells carry no hash field; that is a restriction to state before any claim that the compiled function equals Lean's.

## 5. Caveats

- "Verbatim": function text unchanged; edit E1 only; no 4.29 vs 4.35 change was needed for any definition.
- First-failure counts are exact (**run**). "sig"/"trans" are regex over signature text and the name-based closure (upper bound). Every `→` is **read**.
- The translator prints `PANIC at Lean.Expr.appArg!` backtraces on many rejections (the command still reports its error); 13 functions crash with
  `unknown free variable _fvar.N` (`Display.*`, `nonStdAxiomMsg`, …).
- `out/F2.msgs` is the filtered output. `scripts/` are as run and read `/tmp/claude-0/cl/…` paths from this session.

## 6. Reproduce

```
git clone https://github.com/leanprover/con-leche && git -C con-leche checkout 6810492c1     # deps: ../deps/sail-riscv-lean @51c635c, `lake build Frontx`
python3 scripts/cg.py                                   # declaration index
python3 scripts/gen.py out/Full.lean ConLeche.Kernel.Core ConLeche.Cached.Decls      # concatenation (E1)
python3 scripts/mkprobe2.py                             # appends `frontx_compile f` for 1 103 names
lake env lean --tstack=4000000 -DmaxErrors=100000 F2.lean > F2.out                    # a few minutes
python3 scripts/parseF.py; python3 scripts/final.py     # tables
```
