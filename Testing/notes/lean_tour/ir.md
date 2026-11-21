# Lean 4 low-level IR (λRC) — tour for nano (tag v4.34.1)

Source read: github.com/leanprover/lean4 @ v4.34.1, paths relative to `src/`. No `lean` binary was run;
the worked examples are hand-derived from the code, not machine output. Line numbers are for this tag.

**Big surprise in v4.34.1:** the "IR passes" no longer live in `Lean/Compiler/IR/`. Boxing, borrow inference,
RC insertion, reset/reuse and its expansion are LCNF passes in the new *impure* phase
(`Lean/Compiler/LCNF/Passes.lean:144-160`). `IR/` now only holds the λRC datatypes, the checker, `ToIR`
(LCNF → IR, a thin 1:1 lowering) and the emitters. The old `IR/Boxing.lean`, `IR/RC.lean`, `IR/Borrow.lean`,
`IR/ResetReuse.lean`, `IR/ExpandResetReuse.lean` are gone. Older papers/blogs/code point at the removed files.

## 1. Plain-language explanation

Lean values are heap objects with a **reference count** (RC). The compiler's last job is to turn a pure program
into code that (a) manipulates counts explicitly (`inc`/`dec`), (b) avoids allocation by **reusing** a dead
object's memory when the program is about to build a same-shaped object ("functional but in place"), and
(c) makes types honest about machine representation (unboxed `UInt64` vs boxed object).

Pipeline (impure phase, in order, `Passes.lean:144-158`):
`pushProj → insertResetReuse → elimDeadVars → simpCase → inferBorrow → explicitBoxing → explicitRc →
expandResetReuse → coalesceRC → pushProj → detectSimpleGround → inferVisibility → toposort`, then `ToIR`.

Ideas, from the paper "Counting Immutable Beans" (arXiv 1908.05647):
* **Borrowing**: a parameter marked borrowed (`@&`) is never consumed by the callee, so the caller need not
  `inc` before the call if it still uses the value later. Inferred by a monotone dataflow analysis.
* **Explicit RC**: walk the code with liveness; `dec` a value at the first point it is dead, `inc` it when it is
  passed as *owned* and still used afterwards. Values projected from borrowed values count as borrowed.
* **Reset/reuse**: after `case x of Cons h t => ...`, if `x` is dead and the branch allocates a same-sized
  constructor, emit `w := reset x` (if `x` is unshared: release its fields, keep the cell; else `dec x`, w=box(0))
  and `reuse w in Ctor ...` (if `w` is a cell, overwrite fields in place; else allocate fresh).
* **Expansion**: reset/reuse pairs are later expanded into an explicit `isShared` test with a hot path
  (in-place `set`s, skipping stores of unchanged fields and skipping the incs of projections) and a cold path.

### Worked example 1: `def f (x : Nat) := x + 1`
After toMono/toImpure (before RC), roughly:
```
def f (x : obj) : obj :=
  let one : obj := 1;           -- Nat literal, type `tagged` (<2^32) else `tobject` (ToIR.lean:56-60)
  let r   : obj := Nat.add x one;
  ret r
```
`Nat.add` is `@[extern "lean_nat_add"]` with both params borrowed → inferBorrow leaves `x` borrowed (all
params start borrowed, `InferBorrow.lean:111-117`; nothing forces owned). ExplicitRC then emits **no inc/dec at
all** (small Nat literals are tagged scalars; `inc`/`dec` carry `check := true` so a scalar pointer is skipped at
runtime, `ExplicitRC.lean:398-412`). Final IR: `def f (x_1 : @& obj) : obj := let x_2 := 1; let x_3 := Nat.add x_1 x_2; ret x_3`.
At runtime `lean_nat_add` tests the tag bits: both scalar ⇒ add + overflow check; else bignum (GMP) path.

### Worked example 2: list map shape (reuse)
```
def g : List Nat → List Nat | [] => [] | h :: t => (h+1) :: g t
```
`cases x | cons h t =>` : `x` is owned, dead after projecting `h`,`t`, branch allocates `cons` ⇒
`insertResetReuse` yields `let w := reset[2] x; ... let r := reuse w in cons h' t'`. After
explicitRc: `let h := proj[0] x; inc h; let t := proj[1] x; inc t; let w := reset[2] x;…`. After expandResetReuse:
`isShared x` ? (cold: `inc`s kept, `dec x`, fresh `ctor`) : (hot: no incs, `set x[0]:=h'; set x[1]:=t'`, reuse `x`).
Hot path = a destructive in-place list update with zero allocation. `g t` is not a tail call (cons after), so no loop.

## 2. File map (all `src/Lean/Compiler/`)
| What | file:line |
|---|---|
| λRC datatypes: `IRType` 77, `Expr` (ctor/reset/reuse/proj/uproj/sproj/fap/pap/ap/box/unbox/lit/isShared) 177, `FnBody` (vdecl/jdecl/set/setTag/uset/sset/inc/dec/del/case/ret/jmp/unreachable) 220, `Alt` 216, `Decl` 352 | `IR/Basic.lean` (564 lines) |
| Well-formedness checker (types, arities, scoping) `checkFnBody` 197, `checkDecls` 250 | `IR/Checker.lean` |
| LCNF(impure) → IR, `lowerLet` 130, `lowerLitValue` 56, `lowerDecl` 188 | `IR/ToIR.lean` (213) |
| Pass order | `LCNF/Passes.lean:144-160` |
| Reset/reuse insertion = paper's R/D/S: `S` 83, `D` 188, `Code.insertResetReuse` 255, `mayReuse` 70 | `LCNF/ResetReuse.lean` (333) |
| Ownedness pre-analysis (user `@&` hints blocking reuse) | `LCNF/PropagateBorrow.lean` (169) |
| Borrow inference: `OwnReason` ~203, `infer` ~237 fixpoint loop, init all-borrowed 111 | `LCNF/InferBorrow.lean` (454) |
| Boxing: `mkCast` 145, `Code.explicitBoxing` 261, `mkBoxedVersion` 46 | `LCNF/ExplicitBoxing.lean` (378) |
| RC insertion: derived-value analysis 45-155, `LiveVars` 179, `addInc` 398, `addDec` 405, `addIncBeforeAux` 481, `addDecAfterFullApp` 521, `LetDecl.explicitRc` 563, `Code.explicitRc` 607 | `LCNF/ExplicitRC.lean` (704, biggest) |
| Reset/reuse expansion (hot/cold paths) `processResetCont` 203, `Code.expandResetReuse` 288 | `LCNF/ExpandResetReuse.lean` (385) |
| Block-local inc/dec merging | `LCNF/CoalesceRC.lean` (104) |
| `cases` simplification (single arm, default-arm folding) | `LCNF/SimpCase.lean` (134) |
| Dead-variable elim | `LCNF/ElimDead.lean` (129) |
| Abstract interpretation pruning unreachable ctor branches (`Value` = bot/top/ctor/choice) | `LCNF/ElimDeadBranches.lean` (683) |
| IR interpreter (C++, 1240 lines; `Reset` 489, `Reuse` 501, `Inc`/`Dec`/`Del` 741-755) | `src/library/ir_interpreter.cpp` |
| Runtime RC/boxing primitives: `lean_box` 335, `lean_dec_ref` 691, `lean_is_exclusive` 729 | `src/include/lean/lean.h` |
| C emitter / LLVM emitter | `LCNF/EmitC.lean`, `IR/EmitLLVM.lean` (1678) |

## 3. Facts that matter for nano

**IR semantics (what a nano IR must agree with)**
1. Values: `tobject` = tagged scalar pointer *or* heap pointer. `lean_box(n) = (n<<1)|1` (lean.h:335). A word
   with low bit 1 is a scalar; `inc`/`dec` with `check=true` skip scalars. Small Nat/enum ctors/`UInt8/16` boxed are scalars.
2. `Nat` literal type is `tagged` iff `n < 2^32` (ToIR.lean:59), else `tobject` (may be bignum). Runtime small-Nat
   bound is 2^63−1 (`LEAN_MAX_SMALL_NAT`); overflow promotes to a GMP object. nano must pick: bounded Nat (then
   `nano ⊆ Lean` needs a *hypothesis*, per ROADMAP's "bounds as arguments") or implement bignum.
3. RC counter: `rc>0` single-thread, `rc<0` multi-thread (atomic), `rc==0` persistent (never freed, `dec` is a no-op).
   `lean_is_exclusive` ⇔ single-thread AND rc==1 (lean.h:729). A persistent/MT object is therefore **never** reused in place.
   nano (pure, single core, no IO) can drop MT/persistent: rc ≥ 1 always, exclusive ⇔ rc == 1.
4. `reset n x`: exclusive ⇒ `dec` the first n object fields, return x (cell survives, fields now dangling and must be
   overwritten); else `dec x`, return `box(0)`. `reuse w in C ys`: w scalar ⇒ fresh alloc; else write tag iff
   `updtHeader` and all fields. Interpreter: `ir_interpreter.cpp:489-515`. Caveat: scalar (usize/ssize) fields are
   not touched by reset; `mayReuse` requires equal `size`, `usize`, `ssize` (ResetReuse.lean:70).
5. Reuse across different ctors of the *same* type needs tag rewrite (`updateHeader = cidx differs`); `relaxedReuse`
   (second try) even allows different types of equal layout (ResetReuse.lean:40-80) — a heuristic, not a correctness matter.
6. Borrow rules (InferBorrow.lean header): owned is forced for (i) params flowing into `reset` (RC must be exact),
   (ii) tail-call preservation: if a tail call passes an owned arg, the callee param becomes owned so no `dec` follows
   the call (keeps tail calls = loops; constant stack — important for a stackless nano target); and for perf for
   ctor args, owned params of callees, paps. `@[export]` functions: all params owned (ABI). User `@&` only overridden when forced.
7. Derived borrows: `proj` from a borrowed value is itself borrowed (no inc) — correct only because a borrowed
   parent cannot be mutated/freed during the callee. Same trick for `Array.get` → `getInternalBorrowed` variants
   (ExplicitRC.lean:~575-590).
8. Boxing: a *boxed* wrapper (`foo._boxed`) is generated for any decl with scalar params/result (`requiresBoxedVersion`
   30); used by closures and the interpreter. Unboxed `UInt64`/`USize`/`Float` box to heap objects unless small.
   `UInt8/16/32`: tagged scalars, no alloc (on 64-bit).
9. Order dependence: `expandResetReuse` must run before `coalesceRC` (it relies on inc positions), `insertResetReuse`
   must run before `simpCase` (case simplification would destroy ctor-info) — CoalesceRC.lean:14-27, SimpCase.lean:16-30.
10. The `isShared` test makes behaviour depend on dynamic RC, but results must not: a correct IR has equal *values*
   either path. This is the central soundness obligation (hot path = cold path semantically), and it is **not**
   formally proven in Lean's repo (checker only checks types/scoping). A test model exists: `tests/elab/rc_model.lean`
   is referenced from lean.h:690 but was not found in this checkout (only the comment); not verified.

**Edge cases a nano re-implementation must get right**: join-point params also have ownership; `case` on a var whose
alternative doesn't use some live vars needs per-branch `dec` prologue (ExplicitRC `addPrologForAlt` 421); the same
var passed twice to an owned param needs `inc` n−1 (`getNumConsumptions` 471); a `let` result unused must still be `dec`'d
(side effects, 563-570); `reset` of a field-less/scalar ctor is skipped (`info.isScalar`, ResetReuse.lean:~266).

## 4. Reuse assessment for nano
nano's target is a pure sub-compiler (bytes → bytes, no IO, no threads), proofs in Lean, `partial`/`unsafe`/`sorry` disallowed.
**Hard fact:** Lean's passes are written in `CompilerM`/`CoreM` (monad stacks with `IO` refs, `HashMap`, `StateRefT`, many `partial def`s,
`panic!/unreachable!`). Copying them as-is would break nano's self-hosting subset and be unprovable without rewriting. So (c) is not viable for any pass.

| Idea | (a) blueprint | (b) oracle | (c) copy as-is | Effort (rough, honest) |
|---|---|---|---|---|
| λRC datatypes (`Basic.lean`) | yes: ~10 ctors, tiny. Drop `float`/`struct`/`union`/`tagged`; keep object/scalar | yes (Format output comparable) | no (`Name`, `Array`, `Std.TreeMap` indexed state, structural-recursion over nested arrays of `Alt`) | 1–2 days to define; total |
| Checker | yes: easy, total (`FnBody` recursion). Proving "checked ⇒ no stuck state" is the useful theorem | partially | no (needs `CoreM`) | 2–4 days incl. progress lemma |
| ExplicitBoxing | yes, but only needed if nano has >1 repr (UInt64 vs Nat). If nano is all machine words: skip | yes | no | 3–5 days; proof = type-erasure simulation |
| Borrow inference | blueprint **optional**: it's an optimization (fixpoint over a finite lattice, terminates since `owned` only grows: easy total proof with fuel = #params). Correctness is vacuous (RC pass is correct for *any* borrow assignment *provided* tail-call/reset constraints hold) | yes: compare inferred `@&` with Lean's `set_option trace.Compiler.inferBorrow` | no | 4–7 days if proven; may skip initially: all-owned is always sound, just slower |
| ExplicitRC (inc/dec) | yes: this is the core. Paper gives a clean declarative rule set; liveness is a simple backward pass | **strong oracle**: for any function nano also compiles, Lean emits IR via `set_option trace.compiler.ir.result true`; compare *dec/inc counts* (not necessarily identical) | no (derived-value/DerivedValMap, HashMaps, `partial`) | 1.5–3 weeks to implement+prove. Proof: refinement to a heap-with-counts semantics where `rc(o)` = number of live references; invariant "RC = reference count" + no leak/no use-after-free. This is the paper's Thm (in the paper proven on paper, not mechanized; Isabelle-style mechanization exists only as research, I did not verify) |
| Reset/reuse insert+expand | yes, but **big proof cost**: soundness needs "x unshared ⇒ no other ref ⇒ overwriting invisible". Needs a separation-style heap model with exclusive ownership. This is the part nano's block/layout model (ROADMAP: pairwise-disjoint blocks) could make *cheaper* than in Lean: if nano allocates from a bump region and never frees, reuse is the **only** way memory is recycled | yes (IR text diff on `simple_reuse`-like tests) | no | 2–4 weeks incl. proof; optional optimization, do after RC is proven |
| ExpandResetReuse hot-path tricks (skip identical stores/incs) | later, as a proved peephole | yes | no | 1 week on top of the above |
| CoalesceRC, SimpCase, ElimDead | yes, small & local; each a block-local rewrite | yes | no | days each; CoalesceRC proof = commutation of inc/dec within basic block (subtle only because `dec` may free) |
| ElimDeadBranches (abstract interp) | low priority; relies on `Value` lattice + SCC fixpoint | n/a | no | skip |
| IR interpreter | **yes as a semantics**: define `step` on λRC with explicit heap `Loc → (rc, ctor)` in Lean (~200 lines). It's the reference for correctness theorems. Lean's C++ one is not reusable (C++, FFI) | the C++ interpreter can be an executable oracle for fuzzing | no | 1 week |

**Recommendation (honest):** The reusable value is the *design*, not the code. For a first nano memory story:
1. Define λRC + the heap semantics (interpreter) in total Lean; keep the checker.
2. Implement ExplicitRC without borrowing (all params owned), prove RC-correctness. This alone gives a sound allocator story.
3. Add borrow inference as a proved optimization, then reset/reuse. Each is independently skippable; semantics preserved by construction.
4. Use Lean's real pipeline as a **test oracle** (observable behaviour + counts via `trace.compiler.ir.*`), never as a trusted component (invariant 1: nano ⊆ Lean).
Open risks: (i) multi-word Nat/bignum: Lean's semantics are unbounded; nano needs either explicit bounds or an arithmetic library;
(ii) a non-moving bump allocator without free makes `dec`→`del` meaningless; either add a freelist per size class (as lean's `alloc.cpp` does) or run RC only for in-place reuse and never free;
(iii) closures (`pap`/`ap`) require boxed ABI and generic apply — `ROADMAP` does not list them yet, so postpone unless the subset needs higher-order functions;
(iv) I did not run Lean, so all example IR above is derived by reading, treat as illustrative.
