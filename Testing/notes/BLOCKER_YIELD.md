# Blocker yield: lowest blockers and feature unlocks

Two depth-probe graphs: self-hosting (`Testing/selfhost-depth2`, exact call graph) and con-leche (`Testing/conleche-depth2`, call graph read from source text). The tables are generated from `Testing/dashboard/yield.json` by `Testing/dashboard/yield.py`. Inputs: the same six files `build.py` reads. Evidence tags: facts are from the probe outputs; inferences are marked **(inf.)**.

## 0. Counts

| graph | blocked | OK | lowest blockers |
|---|---:|---:|---:|
| self-hosting | 591 | 31 (+236 GEN, not counted) | 259 |
| con-leche | 1047 | 46 | 201 |

con-leche: 1 101 names in the features file; 8 `beside.*` names are unresolved in the probe (CONLECHE_DEPTH2 §2) and are dropped, so 1 093 are resolved: 46 OK and 1 047 blocked (the same count as the notes). `ConLeche.checkDecl` and `checkDeclKind` are not in the feature file.

## 1. Method

- **States.** OK = compiles (self-hosting: final class OK; con-leche: gate ok and arms ok). GEN = self-hosting generated or type-valued defs (`.elim`, instances, …), treated as clear. Blocked = everything else.
- **Lowest blocker.** A blocked function whose direct callees are all OK or GEN, or in its own strongly connected component. Ranked by "above" = number of transitive callers.
- **Feature labels.** Fixed list of 13 (section 2). Self-hosting: regex over the first-error message (`P2` if present, else `P1`, as `build.py`), on the types named in `unsupported parameter/result type …`. Con-leche: the `F` labels of `cl_greedy.json` mapped to this list. A 0-ary def (type has no `→`) also gets `0-ary constant` in both graphs. No match → `translator shape`.
- **Unlock.** For a set S of features, a blocked function counts as unlocked if every node in its closure is OK/GEN or blocked with all its features in S. Single feature: S = {F}. Greedy: up to 6 steps, each adding the feature with the largest total unlock. Combined = the two graphs summed with the same S (the graphs are disjoint, so this is a sum, not a joint closure).

## 2. Feature list and yield

| id | feature | self-host unlocks | self-host lowest | con-leche unlocks | con-leche lowest | combined unlocks |
|---|---|---:|---:|---:|---:|---:|
| F1 | translator shape (no type named) | 83 | 127 | 40 | 29 | 123 |
| F2 | 0-ary constant | 0 | 30 | 106 | 98 | 106 |
| F3 | inductive / structure type | 0 | 3 | 13 | 56 | 13 |
| F4 | monad / higher-kinded (Type → Type, m α) | 0 | 0 | 7 | 23 | 7 |
| F5 | polymorphic type variable | 31 | 106 | 0 | 0 | 31 |
| F6 | List / Array / Option of non-scalar element | 13 | 55 | 6 | 36 | 19 |
| F7 | sized BitVec / Fin | 38 | 43 | 0 | 0 | 38 |
| F8 | tuple (×) | 0 | 12 | 0 | 0 | 0 |
| F9 | function-valued parameter or result | 0 | 6 | 11 | 12 | 11 |
| F10 | HashMap / HashSet / memo state | 0 | 0 | 1 | 2 | 1 |
| F11 | String / Char / Int | 0 | 0 | 3 | 10 | 3 |
| F12 | non-computational (Type / Prop / Sort / Decidable) | 0 | 10 | 0 | 0 | 0 |
| F13 | several non-structural parameters | 9 | 8 | 0 | 0 | 9 |

"lowest" = lowest blockers whose own features include F. "unlocks" = blocked functions that F alone (S = {F}) makes fully unblocked.

## 3. Greedy sequences (up to 6 features)

**selfhost**

| step | add | total unlocked | gain |
|---:|---|---:|---:|
| 1 | translator shape (no type named) | 83 | 83 |
| 2 | polymorphic type variable | 188 | 105 |
| 3 | List / Array / Option of non-scalar element | 251 | 63 |
| 4 | sized BitVec / Fin | 327 | 76 |
| 5 | 0-ary constant | 406 | 79 |
| 6 | tuple (×) | 453 | 47 |

**conleche**

| step | add | total unlocked | gain |
|---:|---|---:|---:|
| 1 | 0-ary constant | 106 | 106 |
| 2 | translator shape (no type named) | 160 | 54 |
| 3 | inductive / structure type | 241 | 81 |
| 4 | List / Array / Option of non-scalar element | 396 | 155 |
| 5 | monad / higher-kinded (Type → Type, m α) | 439 | 43 |
| 6 | String / Char / Int | 495 | 56 |

**combined**

| step | add | total unlocked | gain |
|---:|---|---:|---:|
| 1 | translator shape (no type named) | 123 | 123 |
| 2 | 0-ary constant | 249 | 126 |
| 3 | polymorphic type variable | 392 | 143 |
| 4 | List / Array / Option of non-scalar element | 487 | 95 |
| 5 | inductive / structure type | 701 | 214 |
| 6 | sized BitVec / Fin | 815 | 114 |

Combined greedy is run jointly on both graphs with one set S. The per-graph greedy sets differ, so they are shown separately.

## 4a. Top 60 lowest blockers: Self-hosting

Feature ids: F1 = translator shape (no type named), F2 = 0-ary constant, F3 = inductive / structure type, F4 = monad / higher-kinded (Type → Type, m α), F5 = polymorphic type variable, F6 = List / Array / Option of non-scalar element, F7 = sized BitVec / Fin, F8 = tuple (×), F9 = function-valued parameter or result, F10 = HashMap / HashSet / memo state, F11 = String / Char / Int, F12 = non-computational (Type / Prop / Sort / Decidable), F13 = several non-structural parameters

| rank | above | name | module | features | first error (probe) | 0-ary: body size (chars), kind |
|---:|---:|---|---|---|---|---|
| 1 | 77 | `Proven.Mach.IR.Tst.a` | Compiler.Opt.IR | F5 | frontx: unsupported result type X ρ | — |
| 2 | 77 | `Proven.Mach.IR.Tst.b` | Compiler.Opt.IR | F5 | frontx: unsupported result type X ρ | — |
| 3 | 59 | `Proven.Mach.IR.Arg.regs` | Compiler.Opt.Alloc | F6, F5 | frontx: unsupported result type List α | — |
| 4 | 54 | `Proven.Ir.Tst.a` | Compiler.Ir.Syntax | F5 | frontx: unsupported result type X ρ | — |
| 5 | 54 | `Proven.Ir.Tst.b` | Compiler.Ir.Syntax | F5 | frontx: unsupported result type X ρ | — |
| 6 | 52 | `Proven.Mach.IR.Tst.c` | Compiler.Opt.IR | F1 | frontx_ind: X has no argument of a declared type | — |
| 7 | 51 | `Proven.Mach.IR.Ins.dst` | Compiler.Opt.Live | F6, F5, F1 | frontx: unsupported result type Option α PANIC at Lean.Expr.appArg! Le | — |
| 8 | 46 | `Proven.Ir.Tst.c` | Compiler.Ir.Syntax | F1 | frontx_ind: X has no argument of a declared type | — |
| 9 | 46 | `Proven.Mach.Wide.wenc` | Compiler.Wide | F1 | invalid instantiateLambda, too many parameters | — |
| 10 | 45 | `Proven.Ir.Block.params` | Compiler.Ir.Syntax | F6, F5 | frontx: unsupported result type List ρ | — |
| 11 | 45 | `Proven.T` | Spec.Code | F7 | frontx: unsupported result type Fin 32 | — |
| 12 | 44 | `Proven.Mach.Wide.lenBr` | Compiler.Wide | F1 | (kernel) application type mismatch Sim argument has type Type 1 but fu | — |
| 13 | 43 | `Proven.Mach.Wide.lenJ` | Compiler.Wide | F1 | (kernel) application type mismatch Sim argument has type Type 1 but fu | — |
| 14 | 42 | `Proven.Ir.Func.blocks` | Compiler.Ir.Syntax | F6, F5, F8 | frontx: unsupported result type List (X × X ρ) | — |
| 15 | 41 | `Proven.Mach.Wide.jOK` | Compiler.Wide | F1 | invalid instantiateForall, too many parameters | — |
| 16 | 40 | `Proven.Ir.Block.body` | Compiler.Ir.Syntax | F6, F5 | frontx: unsupported result type List (X ρ) | — |
| 17 | 40 | `Proven.Ir.Block.term` | Compiler.Ir.Syntax | F5 | frontx: unsupported result type X ρ | — |
| 18 | 40 | `Proven.Mach.WideF.toWide` | Compiler.Opt.BFn | F5, F1 | frontx: unsupported result type X PANIC at Lean.Expr.appArg! Lean.Expr | — |
| 19 | 40 | `Proven.encR` | Spec.Code | F7 | frontx: unsupported result type BitVec 32 | — |
| 20 | 38 | `Proven.Op.eval` | Spec.Code | F7 | frontx_ind: unsupported parameter type BitVec 64 | — |
| 21 | 37 | `Proven.Mach.Wide.brOK` | Compiler.Wide | F1 | invalid instantiateForall, too many parameters | — |
| 22 | 37 | `Proven.Mach.Wide.immOK` | Compiler.Wide | F1 | invalid instantiateForall, too many parameters | — |
| 23 | 37 | `Proven.encI` | Spec.Code | F7 | frontx: unsupported result type BitVec 32 | — |
| 24 | 36 | `Proven.Ir.Func.params` | Compiler.Ir.Syntax | F6, F5 | frontx: unsupported result type List ρ | — |
| 25 | 36 | `Proven.Mach.Wide.maxSlots` | Compiler.Wide | F1 | (kernel) application type mismatch Sim argument has type Type 1 but fu | — |
| 26 | 35 | `Proven.Mach.Cond.eval` | Compiler.Wide | F3, F5, F7 | frontx_ind: unsupported parameter type BitVec 64 frontx_ind: X on TCon | — |
| 27 | 35 | `Proven.Mach.rk` | Compiler.Exp | F5 | frontx: unsupported result type X | — |
| 28 | 34 | `Proven.Mach.WideF.encE` | Compiler.Opt.BFn | F6, F7 | frontx: unsupported result type List (BitVec 32) | — |
| 29 | 34 | `Proven.Mach.WideF.encL` | Compiler.Opt.BFn | F6, F7 | frontx: unsupported result type List (BitVec 32) | — |
| 30 | 33 | `Proven.Mach.Wide.offOK` | Compiler.Wide | F1 | invalid instantiateForall, too many parameters | — |
| 31 | 32 | `Proven.Mach.MOp.eval` | Compiler.MOp | F7 | frontx_ind: unsupported parameter type BitVec 64 | — |
| 32 | 30 | `Proven.Ir.Func.slots` | Compiler.Ir.Syntax | F12, F1 | frontx: unsupported parameter type Type PANIC at Lean.Expr.appArg! Lea | — |
| 33 | 30 | `Proven.Ir.Target.toWideF` | Compiler.Ir.Target | F5, F1 | frontx: unsupported result type X PANIC at Lean.Expr.appArg! Lean.Expr | — |
| 34 | 28 | `Proven.Ir.Func.entry` | Compiler.Ir.Syntax | F12, F1 | frontx: unsupported parameter type Type PANIC at Lean.Expr.appArg! Lea | — |
| 35 | 28 | `Proven.Ir.Prog.funcs` | Compiler.Ir.Syntax | F6, F5 | frontx: unsupported result type List (X ρ) | — |
| 36 | 26 | `Proven.A` | Spec.Code | F7 | frontx: unsupported result type Fin 32 | — |
| 37 | 26 | `Proven.Mach.IR.Ins.mv` | Compiler.Opt.Live | F6, F5, F1 | frontx: unsupported result type Option α PANIC at Lean.Expr.appArg! Le | — |
| 38 | 26 | `Proven.Mach.Sel.leaf` | Compiler.Opt.Sel | F6, F5 | frontx_ind: unsupported result type Option (X Nat) | — |
| 39 | 25 | `Proven.Ir.Target.encCall` | Compiler.Ir.Target | F6, F7 | frontx: unsupported result type List (BitVec 32) | — |
| 40 | 25 | `Proven.Ir.Target.encEC` | Compiler.Ir.Target | F6, F7 | frontx: unsupported result type List (BitVec 32) | — |
| 41 | 25 | `Proven.Ir.Target.encLC` | Compiler.Ir.Target | F6, F7 | frontx: unsupported result type List (BitVec 32) | — |
| 42 | 25 | `Proven.Ir.Target.encT` | Compiler.Ir.Target | F6, F7 | frontx: unsupported result type List (BitVec 32) | — |
| 43 | 25 | `Proven.Ir.Target.encX` | Compiler.Ir.Target | F6, F7 | frontx: unsupported result type List (BitVec 32) | — |
| 44 | 25 | `Proven.Mach.Sel.argUses` | Compiler.Opt.Sel | F13 | frontx_ind: a scalar parameter needs an entry `f xs = X n xs` | — |
| 45 | 25 | `Proven.immB` | Riscv.Steps.Branch | F7 | frontx: unsupported result type BitVec 32 | — |
| 46 | 25 | `Proven.immJ` | Riscv.Steps.Branch | F7 | frontx: unsupported result type BitVec 32 | — |
| 47 | 24 | `Proven.Mach.IR.SR.addrOf` | Compiler.Opt.SR | F6, F8 | frontx_ind: unsupported result type Option (Nat × Nat) | — |
| 48 | 24 | `Proven.Mach.IR.SR.isInc` | Compiler.Opt.SR | F1 | frontx_ind: nested patterns are not supported (X (by cases: frontx_ind | — |
| 49 | 24 | `Proven.Mach.Sel.isVar` | Compiler.Opt.Sel | F1 | frontx_ind: unsupported term ?i.1 (by cases: frontx_ind: unsupported t | — |
| 50 | 24 | `Proven.Mach.Sel.rangeOf` | Compiler.Opt.Sel | F13 | frontx_ind: more than one extra parameter of a declared type | — |
| 51 | 24 | `Proven.Mach.Sel.simpBin0` | Compiler.Opt.Sel | F13 | frontx_ind: more than one extra parameter of a declared type | — |
| 52 | 24 | `Proven.Mach.Sel.uses` | Compiler.Opt.Sel | F1 | frontx_ind: unsupported term ?i.1 (by cases: frontx_ind: unsupported t | — |
| 53 | 23 | `Proven.Ir.SC.seqs` | Compiler.Ir.Struct | F5, F1 | frontx: unsupported result type X PANIC at Lean.Expr.appArg! Lean.Expr | — |
| 54 | 23 | `Proven.Mach.IR.SR.fnd` | Compiler.Opt.SR | F6, F8 | frontx: unsupported parameter type List (Nat × Nat) | — |
| 55 | 23 | `Proven.Mach.IR.SR.incs` | Compiler.Opt.SR | F1 | frontx_ind: List.brecOn has no argument of a declared type | — |
| 56 | 23 | `Proven.Mach.Sel.cmpOf` | Compiler.Opt.Sel | F6, F5 | frontx_ind: unsupported result type Option X | — |
| 57 | 23 | `Proven.Mach.Sel.tstOf` | Compiler.Opt.Sel | F5, F8 | frontx_ind: unsupported result type X Nat × X Nat × Nat | — |
| 58 | 22 | `Proven.Ir.R0` | Compiler.Ir.Emit | F2, F5 | frontx: unsupported result type X | 14, literal data (names/strings/nats/constructors) |
| 59 | 22 | `Proven.Ir.R1` | Compiler.Ir.Emit | F2, F5 | frontx: unsupported result type X | 14, literal data (names/strings/nats/constructors) |
| 60 | 22 | `Proven.Ir.RLim` | Compiler.Ir.Emit | F2, F5 | frontx: unsupported result type X | 15, literal data (names/strings/nats/constructors) |

0-ary lowest blockers in total: 30; with a body found: 14. (Full list: `yield.json`, key `lowest`.)

## 4b. Top 60 lowest blockers: con-leche

Feature ids: F1 = translator shape (no type named), F2 = 0-ary constant, F3 = inductive / structure type, F4 = monad / higher-kinded (Type → Type, m α), F5 = polymorphic type variable, F6 = List / Array / Option of non-scalar element, F7 = sized BitVec / Fin, F8 = tuple (×), F9 = function-valued parameter or result, F10 = HashMap / HashSet / memo state, F11 = String / Char / Int, F12 = non-computational (Type / Prop / Sort / Decidable), F13 = several non-structural parameters

| rank | above | name | module | features | first error (probe) | 0-ary: body size (chars), kind |
|---:|---:|---|---|---|---|---|
| 1 | 502 | `ConLeche.ConstantInfo.name` | ConLeche.Kernel.Env | F3 | gate FAIL: frontx_ind: ConLeche.ConstantInfo.name has no argument of a declared type | — |
| 2 | 468 | `ConLeche.Expr.BTab` | ConLeche.Cached.ExprOpsC | F9 | gate FAIL: frontx_ind: ConLeche.Expr.BTab has no argument of a declared type | — |
| 3 | 465 | `ConLeche.natDivName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natDivName has no argument of a declared type | 17, calls functions |
| 4 | 465 | `ConLeche.natGcdName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natGcdName has no argument of a declared type | 17, calls functions |
| 5 | 465 | `ConLeche.natLandName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natLandName has no argument of a declared type | 18, calls functions |
| 6 | 465 | `ConLeche.natLorName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natLorName has no argument of a declared type | 17, calls functions |
| 7 | 465 | `ConLeche.natShiftLeftName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natShiftLeftName has no argument of a declared type | 23, calls functions |
| 8 | 465 | `ConLeche.natShiftRightName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natShiftRightName has no argument of a declared type | 24, calls functions |
| 9 | 465 | `ConLeche.natXorName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natXorName has no argument of a declared type | 17, calls functions |
| 10 | 463 | `ConLeche.natAddName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natAddName has no argument of a declared type | 17, calls functions |
| 11 | 463 | `ConLeche.natBleName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natBleName has no argument of a declared type | 17, calls functions |
| 12 | 463 | `ConLeche.natMulName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natMulName has no argument of a declared type | 17, calls functions |
| 13 | 463 | `ConLeche.natSubName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natSubName has no argument of a declared type | 17, calls functions |
| 14 | 462 | `ConLeche.Expr.HTab` | ConLeche.Cached.ExprOpsC | F9 | gate FAIL: frontx_ind: ConLeche.Expr.HTab has no argument of a declared type | — |
| 15 | 462 | `ConLeche.natBeqName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natBeqName has no argument of a declared type | 17, calls functions |
| 16 | 462 | `ConLeche.natModName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natModName has no argument of a declared type | 17, calls functions |
| 17 | 462 | `ConLeche.natPowName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natPowName has no argument of a declared type | 17, calls functions |
| 18 | 450 | `ConLeche.Expr.NTab` | ConLeche.Cached.ExprOpsC | F9 | gate FAIL: frontx_ind: ConLeche.Expr.NTab has no argument of a declared type | — |
| 19 | 409 | `ConLeche.withExclusive` | ConLeche.Kernel.Exclusive | F9 | gate FAIL: frontx_ind: unsupported parameter type Bool → ?β | — |
| 20 | 401 | `ConLeche.satRange` | ConLeche.Kernel.Expr | F2 | gate FAIL: frontx_ind: ConLeche.satRange has no argument of a declared type | 5, literal data (names/strings/nats/constructors) |
| 21 | 397 | `ConLeche.FBase.find?` | ConLeche.Kernel.FEnv | F6, F3 | gate FAIL: frontx_ind: unsupported parameter type ConLeche.FBase | — |
| 22 | 397 | `ConLeche.FEnv.lookup` | ConLeche.Kernel.FEnv | F6, F3 | gate FAIL: frontx_ind: unsupported parameter type ConLeche.FEnv | — |
| 23 | 384 | `ConLeche.Level.subst` | ConLeche.Kernel.Level | F1 | gate FAIL: frontx_ind: unsupported parameter type List ConLeche.Name | — |
| 24 | 356 | `ConLeche.Expr.bvarBRaw` | ConLeche.Kernel.Expr | F1 | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.bvarBRaw.eq_1 has no constructor pattern (by cases: fro | — |
| 25 | 352 | `ConLeche.Expr.bvarPoolSize` | ConLeche.Kernel.Expr | F2 | gate FAIL: frontx_ind: ConLeche.Expr.bvarPoolSize has no argument of a declared type | 33, recursion or self-reference |
| 26 | 346 | `ConLeche.Expr.resTerm` | ConLeche.Cached.ExprOpsC | F4 | gate FAIL: frontx_ind: unsupported parameter type Squash ({ r // r = ?c } × ?M) | — |
| 27 | 338 | `ConLeche.natName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.natName has no argument of a declared type | 22, literal data (names/strings/nats/constructors) |
| 28 | 331 | `ConLeche.Level.imaxRules` | ConLeche.Kernel.Level | F6, F11 | gate FAIL: frontx_ind: unsupported parameter type Int | — |
| 29 | 331 | `ConLeche.Level.leqCore` | ConLeche.Kernel.Level | F6, F11 | gate FAIL: frontx_ind: unsupported parameter type Int | — |
| 30 | 331 | `ConLeche.Level.rest` | ConLeche.Kernel.Level | F6, F11 | gate FAIL: frontx_ind: unsupported parameter type Int | — |
| 31 | 309 | `ConLeche.CheckM` | ConLeche.Kernel.Error | F4 | gate FAIL: frontx_ind: ConLeche.CheckM has no argument of a declared type | — |
| 32 | 301 | `ConLeche.charName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.charName has no argument of a declared type | 23, literal data (names/strings/nats/constructors) |
| 33 | 301 | `ConLeche.listName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.listName has no argument of a declared type | 23, literal data (names/strings/nats/constructors) |
| 34 | 299 | `ConLeche.Expr.stripPis` | ConLeche.Kernel.ExprOps | F2, F6 | gate FAIL: frontx_ind: unsupported result type Option (List ConLeche.Expr × ConLeche.Expr) | 0-ary, body not found |
| 35 | 299 | `ConLeche.charOfNatName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.charOfNatName has no argument of a declared type | 20, calls functions |
| 36 | 299 | `ConLeche.listConsName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.listConsName has no argument of a declared type | 19, calls functions |
| 37 | 299 | `ConLeche.listNilName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.listNilName has no argument of a declared type | 18, calls functions |
| 38 | 299 | `ConLeche.stringName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.stringName has no argument of a declared type | 25, literal data (names/strings/nats/constructors) |
| 39 | 299 | `ConLeche.stringOfListName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.stringOfListName has no argument of a declared type | 23, calls functions |
| 40 | 295 | `ConLeche.PropWhen.inter` | ConLeche.Kernel.PropWhen | F2, F3 | gate FAIL: frontx_ind: ConLeche.PropWhen.inter has no argument of a declared type | 0-ary, body not found |
| 41 | 294 | `ConLeche.Expr.mkAppN` | ConLeche.Kernel.ExprOps | F1 | gate ok; arms FAIL: frontx_ind: unsupported variable (a dropped field?) ?a (by cases: frontx_ind: unsupported  | — |
| 42 | 290 | `ConLeche.openPisAtFvars` | ConLeche.Kernel.CoreDefs | F2, F6 | gate FAIL: frontx_ind: more than one scalar parameter | 160, recursion or self-reference |
| 43 | 287 | `ConLeche.FBase.findTable?` | ConLeche.Kernel.FEnv | F6, F3 | gate FAIL: frontx_ind: unsupported parameter type ConLeche.FBase | — |
| 44 | 287 | `ConLeche.FEnv.rawTable?` | ConLeche.Kernel.FEnv | F6, F3 | gate FAIL: frontx_ind: unsupported parameter type ConLeche.FEnv | — |
| 45 | 286 | `ConLeche.BasisDSL.rule` | ConLeche.Kernel.Basis.Builder | F3 | gate FAIL: frontx_ind: unsupported result type ConLeche.RecRule | — |
| 46 | 286 | `ConLeche.Level.isEquiv` | ConLeche.Kernel.Level | F6 | gate FAIL: frontx_ind: unsupported result type Option Bool | — |
| 47 | 285 | `ConLeche.ConstantInfo.toConstantVal` | ConLeche.Kernel.Env | F2, F3 | gate FAIL: frontx_ind: ConLeche.ConstantInfo.toConstantVal has no argument of a declared type | 0-ary, body not found |
| 48 | 285 | `ConLeche.PropWhen.isNever` | ConLeche.Kernel.PropWhen | F2, F3 | gate FAIL: frontx_ind: ConLeche.PropWhen.isNever has no argument of a declared type | 0-ary, body not found |
| 49 | 285 | `ConLeche.boolTrueName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.boolTrueName has no argument of a declared type | 19, calls functions |
| 50 | 285 | `ConLeche.instPisWith` | ConLeche.Kernel.Inductives.Positivity | F2 | gate ok; arms FAIL: frontx_ind: a pattern on another argument (ConLeche.instPisWith.eq_2) (by cases: frontx_in | 0-ary, body not found |
| 51 | 284 | `ConLeche.boolFalseName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.boolFalseName has no argument of a declared type | 20, calls functions |
| 52 | 283 | `ConLeche.Expr.abstract1` | ConLeche.Kernel.ExprOps | F1 | gate FAIL: frontx_ind: more than one scalar parameter | — |
| 53 | 283 | `ConLeche.ProjTable.entry` | ConLeche.Kernel.Env | F3 | gate FAIL: frontx_ind: ConLeche.ProjTable.entry has no argument of a declared type | — |
| 54 | 283 | `ConLeche.formerResSort` | ConLeche.Kernel.CoreDefs | F1 | gate FAIL: frontx_ind: unsupported result type Option ConLeche.Level | — |
| 55 | 281 | `ConLeche.PropWhen.bindZ` | ConLeche.Kernel.PropWhen | F9, F3 | gate FAIL: frontx_ind: ConLeche.PropWhen.bindZ has no argument of a declared type | — |
| 56 | 280 | `ConLeche.natPredName` | ConLeche.Kernel.CoreDefs | F2 | gate FAIL: frontx_ind: ConLeche.natPredName has no argument of a declared type | 18, calls functions |
| 57 | 280 | `ConLeche.sorryAxName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.sorryAxName has no argument of a declared type | 32, calls functions |
| 58 | 277 | `ConLeche.andName` | ConLeche.Kernel.Basis.Names | F2 | gate FAIL: frontx_ind: ConLeche.andName has no argument of a declared type | 22, literal data (names/strings/nats/constructors) |
| 59 | 277 | `ConLeche.lamProj?` | ConLeche.Kernel.PropRead | F2, F6 | gate FAIL: frontx_ind: unsupported result type Option (Nat × Nat) | 0-ary, body not found |
| 60 | 276 | `ConLeche.Expr.peelPis` | ConLeche.Kernel.PropRead | F2 | gate ok; arms FAIL: frontx_ind: equation ConLeche.Expr.peelPis.eq_1 has no constructor pattern (by cases: fron | 0-ary, body not found |

0-ary lowest blockers in total: 98; with a body found: 69. (Full list: `yield.json`, key `lowest`.)


## 5. Caveats

- **Con-leche edges are approximate.** `index.py` links a name to every same-named def (≤3 candidates, same module first), from identifier text. Edges can be false, and true edges can be missing. Lowest-blocker status and unlocks inherit this.
- **First-error labels hide later blockers.** A function is counted by the features of its first message (self-hosting `P2` else `P1`; con-leche the gate, which stops at the first failing signature). A feature in S can be the only blocker reported and still leave the function blocked. Unlocks are therefore an upper bound on what a feature actually enables.
- **Nothing here is compiled.** "Unlocked" means the probe's blocker set is covered. No feature was implemented or run through `frontx`. Self-hosting OK means `frontx_compile` or `frontx_ind` passed; 21 of the 31 are not verified by a message (SELFHOST_DEPTH2 §1).
- **Self-hosting features are regex over messages.** The `X ρ` / `X` placeholder in messages is read as a polymorphic type variable **(inf.)**. Field accessors such as `Proven.Mach.IR.Tst.a` are classed by their message, so a structure field read may be under-counted.
- **Con-leche features are regex over signatures** (`cl_greedy.json`). The 159 functions with no label fall to `translator shape`. Gate-level features (two scalar parameters, `more than one scalar parameter`) are not in that list, so the con-leche side has no `several non-structural parameters` yield.
- **`translator shape` is a catch-all**, not a feature anyone can build. It is listed because the task's list includes it. Its unlock counts show how much of each graph is blocked only by messages the regexes do not name, not a feature to implement.
- **GEN is treated as clear.** GEN defs (236) are not probed. Their callees are still counted through closures, so a blocked callee of a GEN def still blocks the caller's unlock. Only the "lowest" test (direct callees) ignores GEN's own state.
- **0-ary detection.** Self-hosting: type text has no `→` (from `sh_cg.tsv`). Con-leche: greedy's regex. Both can miss 0-ary defs whose type is a function alias, and can mark a function with a `→` alias as non-0-ary.
- **0-ary bodies.** Con-leche: parsed from `F2.lean.txt` (same declaration rule as `index.py`). Self-hosting: `def <short>` in the repo file of the module at `origin/main`; 16 of 30 not found (name or file mismatch). Kind is a heuristic: "literal data" if the body has no lowercase call other than the constructor names `mk`, `mkStr`, `mkNum`, `mkSimple`, `str`, `num`, `anonymous`, and tactic proofs; "recursion or self-reference" if the short name recurs in the body; otherwise "calls functions". Size is characters after stripping comments.
- **Rankings** are by transitive callers within each graph. Graphs are different sizes and roots, so compare ranks within a graph only.

## 6. Reproduce

```
python3 Testing/dashboard/yield.py <input dir> Testing/dashboard/yield.json <F2.lean.txt> <repo root>
```
The input dir is the one `build.py` reads (see its header), with `all.json` from `index.py` on `F2.lean.txt`.

## 6. Self-hosting "translator shape" (F1), broken down (main session, from `blockers_per_def.tsv`, class TRANS)

`PANIC at Lean.Expr.appArg!` is a follow-on printed after an earlier `unsupported …` message, not the cause; the cause is the
first message. Counts of first messages (217 TRANS rows; top classes):

| n | message | reading |
|---:|---|---|
| 32 | `frontx_ind: X has no argument of a declared type` | probe chose a type `T` absent from the signature, or 0-ary / scalar-only function: probe mapping + 0-ary constants |
| 29 | `Unknown constant` | probe named auxiliary/private constants (`Ir.IndLow.bin`, `*.elim`): probe artefact |
| 22 + 5 | `equation ite.eq_1` / `HAppend.hAppend.eq_1 has no constructor pattern` | body whose top is `if … then … else` or `++`: the front end unfolds the head symbol as if it were the function. Real gap |
| 16 + 3 | `List.brecOn` / `Nat.brecOn has no argument …` | structural recursion seen through `brecOn` instead of the equation lemmas. Real gap; same fix as the con-leche knot note (drive the front end by equation lemmas) |
| 15 + 6 | `invalid instantiateForall/instantiateLambda, too many parameters` | arity bug: definitions whose value is a `fun` after fewer binders than the type (`def f : A → B → C := fun …`). Real bug |
| 10 + 6 | `Application type mismatch` (tuple `X × X T`; structure `self`) | elaboration of tuple/structure-projection arguments. Real gap |
| 6 | kernel `Sim argument has type Type 1` | universe level in the generated simulation statement. Real bug |
| 5 + 5 + 4 | more than one extra parameter / scalar needs an entry / pattern on another argument | front-end shape limits |

So F1 is mixed: about 60 are probe artefacts; the real compiler gaps are equation-lemma driving (ite/++/brecOn, ~46),
the arity bug (~21), tuple/projection elaboration (~16) and the universe bug (6).
