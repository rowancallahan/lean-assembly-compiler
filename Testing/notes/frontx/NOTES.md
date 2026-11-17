# frontx: from list pipelines to ordinary recursive Lean definitions

Branch `frontx`, rebased onto the reorganised `main` (round 4, section 11). Files: `Riscv/Frontx/*.lean` (lake lib
`Frontx`, not a default target), `Testing/asm/emit_frontx.lean`, `Testing/asm/frontx_test.py`,
`Testing/asm/frontx-words/`, `Testing/notes/frontx/{NOTES,SURVEY,PLAN}.md`. Sections 1–10 were written before the
rebase and use the old paths (`Proven/Frontx/` = `Riscv/Frontx/`, `asm/` = `Testing/asm/`); where section 11
supersedes a statement there (machine theorems: now `Implements1`), section 11 says so.

**Round 2 is section 9, round 3 section 10, round 4 (rebase, `Implements1`, lists, specialisation) section 11, round 5
(list results, `Option` results, general `match` shapes, inlined calls, the book table) section 12.**

## 1. Status

Kernel-checked (no `sorry`, no `axiom`, no `native_decide`, no `bv_decide`, no `extern`/`implemented_by` in
`Proven/Frontx/`):

| what | where | axioms (`#print axioms`) |
|---|---|---|
| `Tree` language, compiler `prog : Lay → Tree → Nat → BStmt`, `prog_ok`, `prog_ok_ro` (source level, once and for all) | `Tree.lean` | `propext`, `Classical.choice`, `Quot.sound` |
| `Sim` and the per-node rules `sim_ret/call/let/load/cload/dite` | `Tree.lean` | same |
| representation lemmas (`r8`, `r32`, `r64`, `rN`, `blk`) | `Rep.lean` | same |
| `frontx_compile f`: for each `f` below, `f.step1`, `f.runs`, `f.exec`, all generated | `Examples.lean` | same |
| `crcCode_ok`: the generated CRC-32 loop on the Sail RISC-V model through the existing `compileBF_ok` | `Machine.lean` | the 77 of `msortCode_ok` (the three above + 7 model constants + 67 `riscv_*` externs); the two sets were compared and are equal |

Tested, not proved: `asm/frontx_test.py check 40` runs the 686 words of `crcCode` on QEMU and on the Sail C emulator
(40 inputs, lengths 0..562, own stack per case with misaligned `sp`): `a2 ^ 0xFFFFFFFF = zlib.crc32(input)` on both,
input and guard bytes unchanged, `gp`/`sp` restored, stack unchanged outside the 104-byte frame, every Sail data
write inside a frame. 638.5 instructions per input byte (3 944 444 for 6 178 bytes). `#eval crc32 "123456789".toUTF8`
gives `0xCBF43926` (interpreter, not a proof).

Sketch only (not built): everything in sections 6 and 7 that is not in the table above, including the `for`-loop
route (6.6).

`frontx_compile` succeeds, with no hand proof, on:

| function | shape | vars (user + control) | obligations | translate + step proof | induction | `exec` |
|---|---|---|---|---|---|---|
| `sumDown` (`LoopExamples.lean`, was hand-proved) | 2 × `BitVec 64`, WF recursion | 2 + 4 | 4 | 0.05 s | 0.01 s | 0.09 s |
| `gcdSub` (`LoopExamples.lean`, was hand-proved) | 3 nested `if`, 2 recursive calls | 2 + 3 | 9 | 0.10 s | 0.02 s | 0.01 s |
| `byteSum` | `ByteArray`, `Nat` index, `UInt64` acc, `xs[i]` under `if h :` | 5 + 4 | 10 | 0.12 s | 0.02 s | 0.02 s |
| `find` | early exit on a loaded byte | 5 + 3 | 12 | 0.11 s | 0.01 s | 0.01 s |
| `count` | value-level `if` | 6 + 4 | 11 | 0.15 s | 0.02 s | 0.02 s |
| `xorAll` | `xs[i]!`, `UInt8` arithmetic (masked) | 5 + 4 | 10 | 0.10 s | 0.01 s | 0.1 s |
| `eqFrom` | two arrays, `∧` in the test | 7 + 3 | 15 | 0.15 s | 0.02 s | 0.01 s |
| `crcGo` (CRC-32, bitwise, 8 inlined bit steps, `UInt32`) | helper inlining, 9 temporaries | 14 + 4 | 19 | 1.05 s | 0.02 s | 0.03 s |
| `adlerA` (lean-svg `Png.adlerChunk`, first component) | `match fuel with \| 0 \| n+1`, guarded read | 7 + 5 | 15 | 0.28 s | 0.02 s | 0.02 s |
| `b64Sum` (uses lean-svg `Bytes.at'` and `Font.b64Digit` verbatim) | helpers, `&&`, `==`, `≤` on `UInt8` | 7 + 5 | 15 | 0.71 s | 0.02 s | 0.02 s |

Times are wall-clock milliseconds reported by the command itself (4 cores, unloaded), per function; the kernel check
of each generated `step1` term is 1–7 ms. `Examples.lean` as a whole (12 functions): 5.5 s in `lake build`.

Rejected, with the message shown (each is a correct rejection, see section 6):

| input | message |
|---|---|
| `xs[i].toUInt64 + sumRec xs (i+1)` | `recursive call not in tail position` |
| lean-svg `adlerChunk` verbatim (returns `UInt64 × UInt64`) | `unsupported result type UInt64 × UInt64` |
| `acc * 31 + …` | `unsupported term` (no multiply in `Op`) |
| `if i < xs.size && xs[i]! != k` | `could not prove (blk xs)[i]? = some xs[i]!.toBitVec` (the load is emitted before the test) |
| `Nat` accumulator `n + xs[i].toNat` | `could not prove n + xs[i].toNat < 2^64` |
| fuel loops without `with … i + fuel < 2^64` | `could not prove i + 1 < 2^64` |
| `List UInt8` parameter | `unsupported parameter type` |

## 2. Setup (task 1)

`setup/box.sh` ran to completion (exit 0). `swapon /swapfile` did not activate swap in this container (`free`
shows 0 swap); 15 GB RAM was enough. `lake build Proven.PipeExamples Proven.LoopExamples Proven.Arr2Src`: 167 jobs,
about 51 minutes wall-clock from a cold start (the Sail model is most of it; largest single file 1223 s).
`lake build Proven.Arr2F` (needed only for `Machine.lean`): 12 more minutes (`Arr2Words` 696 s). `Machine.lean` itself: 1.1 s.
The front end itself needs none of the machine files: `Tree.lean`, `Rep.lean`, `Translate.lean` only use the
source-level definitions of `Arr2Code.lean`/`Arr2Src.lean`. They were developed against a copy of those definitions
without the Sail import (compile times: `Tree` 1.8 s, `Rep` 0.7 s, `Translate` 5 s). In the tree they import
`Proven.Arr2Src`, which transitively imports the Sail model only because `Arr2Code.lean` imports `Proven.Loop` for
instruction words.

## 3. Survey of lean-svg (task 2)

Full report: `frontx/SURVEY.md` (39-row table of byte-level pieces with file:line, four pieces quoted verbatim,
feature table with the grep heuristic for each number, stage sizes, most-used core functions).
Not built or type-checked; counts are regex heuristics over the import closure of `LeanSvg/Render.lean`
(101 files, 33 067 lines, 1 666 defs; 35 files are generated font data). Toolchain there: Lean v4.34.0 (here: v4.29.0).

Facts that decide the design:

- Recursion: 0 `partial`, 0 `termination_by`, 0 `mutual`, 0 `let rec`. 26 self-recursive defs, all structural on a
  `Nat` fuel argument (`match fuel with | 0 | fuel'+1`). Loops: 340 defs use `Id.run`, 354 use `for` (295 over
  ranges), 334 `let mut`, 137 `break`/`continue`, 4 `while` (2 defs).
- Numbers: `Nat` in 910 defs, `Int` in about 500 (`abbrev Fx := Int`), `UInt8` in 59, `UInt32` in 13, `UInt64` in 4.
  No `Float` anywhere; there is a software float `abbrev F32 := Nat` (13 files; output pixels depend on it).
  `*` in 454 defs, `/` in 157, `Int.ediv` 412 occurrences, `%` in 82.
- Data: `Array` in 521 defs (`push` in 189, `setIfInBounds`/`modify` in 103, `getD` 1 250 occurrences), `ByteArray`
  in 388, `String` in 379, `Option` in 496, tuples in 289, 123 structures (median 5 fields, largest 77), 52
  inductives of which 2 recursive, `Std.HashMap` in 10 defs (keys `String`, `Clip.Key`), one `StateM`.
- Higher-order: 202 defs make higher-order calls, 281 contain lambdas; 3 defs have a type parameter; 0 classes.
- No `IO`, `unsafe`, `extern`, `implemented_by`, `sorry`. `Task.spawn` once (only when `threads ≥ 2`).

The smallest byte-level pieces and what the current languages lack for each (details in `SURVEY.md`, section A):

| piece | lines | style | missing today |
|---|---|---|---|
| `Bytes.at'` | 1 | `if h : i < bs.size then bs[i] else 0` | nothing after this branch (guarded load) |
| `Font.b64Digit`, `Image.b64Val`, `isDigit` … | 7 | `if` chain on a byte | nothing (inlined) |
| `PngDecode.be32`, `GifDecode.le16`, `Font.u16/u32` | 1–3 | non-recursive, `Nat` shifts/ors of 4 `at'` | non-recursive entry point, `Nat` shift/or lemmas |
| `Png.adlerChunk` | 6 | fuel recursion, 2 `UInt64` accumulators | pair result |
| `Png.adler32Rows` | 16 | nested `for` in `Id.run` | `% 65521`, `/ 5552`, general `*`, calls |
| `Png.crcBytes` + `crcTable` | 3 + 5 | `ByteArray.foldl` closure, 256 × `UInt32` table built by `Array.ofFn` | word arrays (4-byte loads), closure, constant table |
| `Png.crcRun4` | 19 | fuel recursion, 4 tables | word arrays, a non-tail fallback call |
| `Image.base64Decode`, `FontFace.base64`, `Font.base64DecodeInto` | 15–31 | `for` loop, `push` on an output `ByteArray`, `Option` result | output buffer with length, `Option`, `String` input for one of them |
| `Svg.hexVal` (3 copies) | 5 | `Option Nat` result | `Option` |
| `Text.decodeUtf8` | 25 | `for` as fuel, output `Array Nat` | word-array output |
| integer → decimal | none in the repo: all through core `toString` on `Nat` | — | `/ 10`, `% 10`, `String` |

So for lean-svg the dominant loop form is option (ii) of the brief (`Id.run do … for … let mut`), not (i).
This prototype implements (i); 6.6 states what (ii) needs on top of it.

## 4. Design (task 3)

Three layers.

**(a) `Tree` (once and for all, `Tree.lean`, 500 lines).** The body of a first-order tail-recursive function as a
decision tree over the existing `BExp`:

```
Tree ::= ret e | call [(v, e), …] | ite c t e | let_ v e k | load v b i k
       | cload v b i c d k        -- v := if c ≠ 0 then block b [i] else d
       | store b i e k            -- in the language and in prog_ok; not produced by the translator yet
```

`Tree.step : Tree → BState → Option Out` is one iteration (`Out = ret r σ | call σ`; `none` = out-of-bounds),
`Tree.Runs t σ r σ'` iterates to a `ret`. `prog L t out : BStmt` is
`fl := 1; while fl { body }; out := res`, where a `ret e` leaf is `res := e; fl := 0`, a `call` leaf assigns the new
arguments in parallel through temporaries, and a conditional is two loops that run at most once
(`a := c; b := (a == 0); while a { T; a := 0 }; while b { E; b := 0 }`), because `BStmt` has no `if`.
Variables: `M` user variables, then `res`, `fl`, `K` call temporaries, 2 condition variables per nesting depth.

```lean
theorem prog_ok (L : Lay) {t : Tree} (hw : t.wf L) {σ σ' : BState} {r : BitVec 64} (h : t.Runs σ r σ')
    (out : Nat) (τ : BState) (hA : Agree L.M σ τ) :
    ∃ τ', BExec (prog L t out) τ τ' ∧ τ'.env out = r ∧ τ'.heap = σ'.heap ∧
      ∀ v, v < L.M → v ≠ out → τ'.env v = σ'.env v
```

The existing `compileBF_ok` then takes `BExec` to the machine, unchanged.

**(b) `Rep.lean` (once per (type, operation), about 180 lines).** How a Lean scalar sits in a 64-bit variable:
`BitVec 64` as is, `r64 x = x.toBitVec`, `r32`/`r8` zero-extended, `rN n = BitVec.ofNat 64 n`; a `ByteArray` is a
heap block `blk xs`. One lemma per supported operation pushes the representation through it, e.g.
`r32 (a + b) = (r32 a + r32 b) &&& 0xffffffff`, `r32 (a >>> b) = r32 a >>> ((r32 b &&& 31).toNat % 64)`,
`rN (a + b) = rN a + rN b`, `rN (a - b) = rN a - rN b` if `b ≤ a`, `(rN a < rN b) = (a < b)` if both `< 2^64`,
`(a = b) = (r8 a = r8 b)`. Supported: `+ - &&& ||| ^^^` on all five types (masked for `UInt8`/`UInt32`),
`>>>` (and `<<<` in the translator, lemma only for `r32 >>>`), `= ≠ < ≤ > ≥`, `∧ ∨ ¬`, `== != && || !`, `decide`,
value-level `if`, the conversions `toUInt8/32/64`, `toNat`, `Nat.toUIntN`, `xs.size`, `xs[i]`, `xs[i]!`, literals.

**(c) `frontx_compile f` (`Translate.lean`, about 740 lines, untrusted).** Reads `f` through its unfolding equation
(`getUnfoldEqnFor?`, i.e. `f.eq_def`; never the compiler IR), walks the body:
`if`/`dite`/`match n with | 0 | m+1` in tail position → `ite`; `let` and compound arguments of helper functions →
temporaries; other constants → unfolded (inlined); array reads → `load`/`cload`; a full application of `f` →
`call`; anything else → `ret`. It emits

```lean
f.tree : Tree        f.lay : Lay
f.Rep  : args → BState → Prop     -- heap = [blk xs, …], σ.env v = rep x, bounds x < 2^64 for Nat, the `with` invariant
f.out  : args → LOut (args tuple) -- the body of f with leaves tagged  ret (rep e) / call args'
f.step1 : ∀ args σ, f.Rep args σ → Sim _ f.tree σ (f.out args)                       -- one iteration, no induction
f.runs  : ∀ args σ, f.Rep args σ → ∃ σ', f.tree.Runs σ (rep (f args)) σ'
f.exec  : ∀ args σ, f.Rep args σ →
            ∃ σ', BExec (prog f.lay f.tree out) σ σ' ∧ σ'.env out = rep (f args) ∧ σ'.heap = σ.heap
```

How the equation is proved:

- `f.step1` is a proof *term built by the translator*, one rule of `Tree.lean` per node it emits. Each emitted
  expression leaves one small obligation (`E.denote env = rep e`, a load's bounds, a test `c.denote env ≠ 0 ↔ P`, the
  conjuncts of `f.Rep` for the new arguments). Before an obligation is handed to
  `simp [Rep lemmas, inlined helpers, hypotheses] <;> omega`, the Lean terms already held in temporaries are
  generalised to variables, so no obligation sees more than one layer of a helper.
- `f.runs` is `fun_induction f`: the function's own termination argument (structural or well-founded) is reused; no
  measure and no loop invariant is ever written. In each case the path hypotheses select the leaf of `f.step1`
  (`frontx_path`), and a `call` leaf is closed by the induction hypothesis. "The recursive function is the invariant"
  holds literally: the only extra invariant is `f.Rep` (bounds of `Nat` values).
- `f.exec` is `prog_ok_ro` applied to `f.runs`; `Tree.wf` by `simp`.

If any step fails, the command fails and adds no theorem (the tree stays defined for inspection).

### Why (i) and not (ii)

(i) has a ready-made induction principle (`f.induct`) and an unfolding equation; both come from Lean's own
elaborator and are kernel-checked there. For (ii) the term is `forIn [a:b] ⟨state⟩ (fun i r => … pure (ForInStep.yield/done ⟨…⟩))`
(printed from Lean 4.29 for two test loops; `let mut` variables become an `MProd`, `break`/early exit become
`ForInStep.done`, the code after an `if` becomes a local `__do_jp` lambda). `LOut` of `Tree.lean` is `ForInStep` up to
naming, so a `for` body translates with the same node rules; what (ii) needs in addition is listed in 6.6.

## 5. What broke, in the order it happened (task 3: "what broke")

1. **`simp` over the whole iteration is exponential.** First version: prove each `fun_induction` case by
   `simp [tree, Tree.step, …]` (evaluate the step, then compare with the Lean side). Fine for 7 of the examples
   (0.1–0.3 s each). For CRC-32 with `n` inlined bit steps: `n = 1` 0.2 s, `n = 2` 0.5 s, `n = 3` 2.1 s, `n = 4`
   "maximum number of steps exceeded". Cause: each bit step uses its input three times; substituting temporaries
   and unfolding helpers builds a term of size 3^n. This is what forced the certifying design of section 4(c)
   (CRC-32 with 8 steps: 1.05 s, 19 obligations).
2. **Normal forms.** A whole-term `simp` equation only closes if both sides reach the same normal form. Cases met:
   - `0` vs `0#64` in path hypotheses (hypotheses must be normalised with the same set);
   - comparisons: pushing `r32` inwards first makes `r32 a = r32 b ↦ a = b` unusable for compound `a`; fixed by
     moving fixed-width comparisons to the `BitVec` level instead (`r32_eq'` etc.). For `Nat` the direction stays
     `BitVec → Nat` (bounds are needed, and `omega` needs the `Nat` facts), so a `Nat` test whose sides are compound
     (`i + 1 < n`) is not covered;
   - literals: `r32 1` vs `1#64`; fixed by evaluating constants in the translator and `r32_lit` (`no_index`) lemmas;
   - a select `if C = 0 then b else a` whose condition `simp` rewrites to `¬(A ∧ B)` and then to `A → ¬B` before
     `ite_not` applies; fixed by an opaque `sel` and the one-step lemma `sel_c`.
   Each fix is a lemma or an orientation in `Rep.lean`, not a per-function proof.
3. **`fun_induction` substitutes equations.** For `if n = 0` the base case has no hypothesis `n = 0`; `n` is replaced
   by `0`. The path follower then decides the test by `rfl`, or by `omega` (`fuel' + 1 = 0`).
4. **Elaboration errors become `sorry` silently** inside `Tactic.run` unless `withoutRecover` is used; one
   intermediate version produced a theorem depending on `sorryAx`. Now the command checks every generated proof
   term for `sorry`/metavariables before `addDecl`.
5. **Unbounded `Nat`.** `Nat` parameters get the hypothesis `x < 2^64` in `f.Rep` automatically; it must be
   re-established at every call. For `i < xs.size` loops this is automatic (`omega` from the test and
   `xs.size < 2^64`). For lean-svg's fuel loops it is false as stated (`i` grows with `fuel`, and `at'` returns 0 past
   the end, so the Lean function is defined for `i ≥ 2^64` while the machine index wraps). The user supplies
   `with fun _ i fuel _ => i + fuel < 2^64`; preservation is by `omega`.
6. **Reads.** A read is loaded where it is first needed in emission order, unconditionally. `xs[i]` inside the
   branch guarded by `i < xs.size` works; `if i < xs.size && xs[i]! != k` does not (short-circuit `&&` is not
   control flow in `BExp`). The guarded form `if h : i < xs.size then xs[i] else d` got its own tree node
   (`cload`, 110 lines of once-and-for-all proof) because lean-svg reads through it everywhere (1 250 `getD`, `at'`).
7. **`Translate.lean` details that cost time**: `scoped`/`hints` are keywords; `getElem!` has 8 arguments;
   `enableRealizationsForConst` is needed after `addDecl` before `simp` can unfold a new definition; the optional
   `with` clause had to be two `elab` rules.

8. **`BStmt.wf` (the existing compiler's limits)** is checked per program by `decide +kernel` (a `Decidable`
   instance for `BStmt.wf` is in `Machine.lean`). `crcGo` passes with 12 slots (20 variables). `b64Sum` does not:
   the 5-deep `if` chain of `b64Digit` is one expression of depth 11 (limit 6). The translator does not split
   expressions; it has the mechanism (temporaries) but no depth criterion. So `b64Sum.exec` holds at source level
   and has no machine theorem. (Fixed in round 2, section 9.1.)
9. A name clash unrelated to this work: `Proven.ArrExamples` and `Proven.LoopExamples` both define
   `Proven.sumProg_wf`, so `SortMergeMachine` and `LoopExamples` cannot be imported together.

Code quality of the generated programs (measured, not optimised): `sumDown` is 71 words (prologue included) against
16 for the hand-written `sumProg` of `LoopExamples.lean`; the CRC loop is 686 words and 638.5 instructions per byte.
Known causes: a conditional is two loop headers plus two flag assignments; every leaf sets `res`/`fl` or copies all
changed arguments through temporaries; `skip` is an assignment; variables above 7 live in stack slots (CRC uses 12);
constants are rebuilt at each use (`0xEDB88320` is 47 words, 8 times); tests produce a 0/1 value that is tested again.

## 6. The hard parts (task 4)

Sizes are estimates from what was built here: a new `Tree` node with its `comp_ok` case, `step_ro` case and `sim_`
rule was 110 lines (`cload`); a representation lemma is 2–5 lines; a new syntactic form in the translator is
10–40 lines.

### 6.1 Unbounded `Nat` (and `Int`)

- Done: `Nat` held in one 64-bit variable, bound `x < 2^64` as hypothesis in `f.Rep`, re-proved at each call by
  `omega`, optional user invariant (`with`).
- Translator needs: bounds for intermediate values (today only parameters carry bounds; `rN_add` needs none,
  `rN_sub`, comparisons and conversions do). For `Array`/`ByteArray` indices the bound comes from the size; for
  accumulators (`n + xs[i].toNat`) there is no bound without a user statement. Options: (a) hypothesis in the theorem
  (what is done; the final theorem is then conditional on the input, e.g. `i + fuel < 2^64`); (b) the user states a
  bound per function (`with`); (c) the Lean source is changed to `UInt64`/`UInt32` where wrap-around is intended.
  A proof that an unbounded computation fits in 64 bits cannot be found automatically in general.
  For lean-svg (910 defs with `Nat`, about 500 with `Int`), (a)/(b) means a size contract per function, derived from
  its own limits (`maxInput` 64 MiB, `maxDim` 16384, coordinates documented as clamped to ±2^30).
- Middle layer needs: signed comparison and arithmetic shift exist in `Op` (`slt`, `ashr`); multiply, divide and
  modulo do not exist at all (454 / 157 / 82 defs use them). `*` by a constant and `/ %` by powers of two can be
  shifts and masks in the translator (about 30 lines + 6 lemmas); general `*` needs the M extension words and step
  lemmas in the backend (one `gen_*.py` family, as for `add`), `Int.ediv` needs the sign cases on top.
- True big numbers (limb arrays) are a separate item of `ROADMAP.md`; nothing here helps.
- Size: constant mul/div/mod about 100 lines; `Int` as two's complement with bounds about 150 lines of `Rep` lemmas
  and 50 of translator; M-extension words are backend work outside this estimate.

### 6.2 Non-tail recursion

- Translator needs: nothing new to *read* it (the unfolding equation and `f.induct` exist for every structural or
  well-founded definition), but the `Tree`/loop target cannot express it: a non-tail call needs a return address and
  a frame per activation.
- Middle layer needs: calls (`jal`/`ret` with `ra` saved), a stack discipline (frames carved from the single work
  block, the bound `space n` of the spec derived from the recursion depth), and a Hoare rule for a call
  ("if the callee's theorem holds, the caller continues with the result in `a0` and its frame intact"). The proof of
  a recursive function is then again `f.induct`, with the depth bound as an extra obligation.
  `compileBF` already has a frame (prologue, slots relative to `gp`), so one activation is done; what is missing is
  nested activations and the separation of frames.
- Without calls, two things still work: accumulator-passing versions written by the user, and *inlining* of
  non-recursive helpers (done here: `crcBit`, `at'`, `b64Digit`).
- Size: not built. The `Stmt → AStmt → BStmt` steps were each one file of 150–300 lines of compiler plus
  proof and one generated words file; a call/return step is of that order plus the stack-depth accounting in
  the spec.

### 6.3 Data structures

- Structures and tuples of scalars: no allocator needed. A structure parameter is one variable per field
  (flattening); a tuple result is several result variables. Translator: `Prod.fst/snd`, projections and
  constructor applications, about 80 lines; `f.Rep`/`LOut` already carry tuples. Middle layer: results in more than
  one register, or written to the output block per `Encode.lean` (`enc (a, b) = enc a ++ enc b` exists).
  This alone unlocks `adlerChunk` verbatim and most of lean-svg's small structures (median 5 fields).
- `Option`/`Except String` results: a tag variable plus payload (`Encode.lean` has the `Option` layout). About 60 lines.
- Word arrays (`Array UInt32`, `Array Nat` with a bound): `BStmt` needs `load64/store64` (or 4-byte) on blocks:
  "S2" of `ARRAYS.md`, not started; needs two constructors, an alignment side condition, the store-inside-region
  lemma. The translator side is the same as bytes (about 30 lines + `blk32` lemmas).
- Constant tables (`crcTable`): either a read-only data block whose contents equal the Lean constant (a closed
  `decide`-style fact, 1 KiB here) or computed at start by compiled code.
- Arrays of structures, nested arrays, `String`, recursive inductives (only 2 in lean-svg; trees for the tree
  evaluator): need a layout per type in `Encode.lean`, a bump allocator over the work block, and a representation
  predicate (value ↔ cells, with separation). This is the "allocator (linked list)" item of `ROADMAP.md`. Nothing
  was prototyped. The translator would then turn `match` on a constructor into a tag load and field loads; the
  per-function proof stays `f.induct` + per-node obligations, with the representation predicate in `f.Rep`.
- `Std.HashMap` (10 defs in lean-svg): either compile core's implementation (needs all of the above plus
  polymorphism/`Hashable` instances specialised) or replace it by a verified map of our own with the same lookup
  semantics; the second is a `ROADMAP.md` item.

### 6.4 `Array` functional updates

- In a tail-recursive loop an array parameter that every call passes on as `arr` or `arr.set i v` is used
  linearly by construction; the block can be updated in place. `Tree.store` and its case of `prog_ok` exist
  (kernel-checked); the translator does not emit it yet. Needed: `blk (arr.set i v) = (blk arr).set i _`
  (1 lemma), the `call` case accepting `xs.set i v`, `f.Rep` relating the block to the *current* array, and
  `prog_ok` instead of `prog_ok_ro` in `f.exec`. About 80 lines.
- `push` (670 occurrences in lean-svg): the block is `data ++ junk` with a separate length variable and a capacity
  hypothesis (`out.size + k ≤ capacity`, from the caller: lean-svg mostly uses `emptyWithCapacity`). Representation
  is then a relation, not `blk`; `rd`/`wr` lemmas for a prefix. About 150 lines, and a capacity bound per function,
  which is the same kind of contract as 6.1.
- General (non-linear) use, e.g. the old array read after an update: needs a copy, or a linearity check in the
  translator that rejects it. Inside one loop the check is syntactic (the old name does not occur after the
  update). Across calls it is an ownership discipline of the calling convention.

### 6.5 Closures and higher-order functions

- 202 defs in lean-svg call `map`/`foldl`/`filter`/`any`/…, mostly with a literal lambda. First-order
  specialisation covers these: unfold the combinator to its loop (`Array.foldl` is a loop over an index) and
  inline the lambda. The translator already inlines by unfolding; it needs the loop form of each combinator as a
  rewrite to a tail-recursive function (one lemma per combinator, from core), then proceeds as today. The existing
  `Pipe` front end does this for a fixed set on lists.
- `__do_jp` join points of `do` blocks are local lambdas applied in tail position; beta-reduction removes them
  (code duplication) or they become shared tree nodes (needs a join-point node, see 6.6).
- Functions passed as parameters (`Bytes.skipWhile (p : UInt8 → Bool)`): specialise per call site.
- True closures stored in data (`Thunk` twice, `Unit →` font thunks): out of reach without a closure
  representation; in lean-svg they can be replaced by eager values.

### 6.6 What option (ii) (`for` loops in `Id.run`) needs on top of this prototype

1. A node sequence: the function body is straight-line code, a loop, more code, a second loop, possibly nested.
   `prog` is one loop. Needed: `Tree` leaves that continue into another tree (sequencing) and loops as statements
   (nesting). This is the main structural gap; estimated 200–300 lines in `Tree.lean` (the `comp_ok` induction
   already handles nested condition loops).
2. `forIn` over `Std.Range` in `Id`: one lemma turning it into the iteration of the body with `ForInStep`
   (core has the unfolding lemmas for `Std.Range.forIn`), and the body translated with the existing node rules,
   `ForInStep.yield/done` in the role of `call/ret`, the `MProd` state as several variables.
3. `Id.run`, `pure`, `bind` in `Id` unfolded (definitional).
4. Termination is free (the range is finite); the bound `i < stop < 2^64` comes from the range.
Not built in round 1; the 340 `Id.run` defs of lean-svg depend on it. Round 2 built points 2–4 (section 9.2);
point 1 (sequencing and nesting) is still open.

## 7. Recommendation (task 5)

Once-and-for-all = proved once, generic in the function. Per function = generated and kernel-checked at each
`frontx_compile`, no human proof. Contract = a statement the user must supply (bounds, capacities).

| stage | adds | once-and-for-all proofs | per function | unlocks |
|---|---|---|---|---|
| 0 (this branch) | tail recursion over `BitVec 64`/`UInt8/32/64`/bounded `Nat` + read-only `ByteArray`s, helper inlining, guarded reads, fuel `match` | `prog_ok`, `sim_*`, `Rep` lemmas | `step1` obligations, `runs` by `fun_induction`, `exec`; contract: `Nat` bounds | byte sum/find/count, bitwise CRC-32, Adler inner loop (one component) |
| 1 | tuples/structures of scalars (params and results), `Option` result, in-place `set`, output buffer with `push` + capacity, non-recursive entry points (prologue code before the loop, epilogue after), expression splitting to depth < 7, constant `*` `/` `%` | `store` in the read-write `exec`, prefix-block lemmas, `Rep` lemmas | same; contract: capacity | lean-svg `adlerChunk`, `be32`, `hexVal`, `b64Digit` standalone, base64 decode (`FontFace.base64`), percent-decode |
| 2 | sequencing and nesting of loops, `for`/`Id.run` (6.6), word arrays (S2: 4/8-byte block access), constant tables, combinator unfolding (`foldl`, `map`, `any`) | sequence/nest rules in `Tree`, `forIn` lemma, `load32/64` words | same | lean-svg CRC-32 as written (`crcBytes`, `crcRun4`, tables), `adler32Rows`, `Png.encode` (needs general `*`, `%`: M extension), UTF-8 decode |
| 3 | calls and a stack (non-tail recursion, non-inlined helpers), depth bound in `space n` | call rule, frame separation | `f.induct` + depth obligation | tree evaluator over a prefix byte encoding (`ROADMAP.md`), recursive descent |
| 4 | allocator, layouts for inductives / arrays of structures / `String`, representation predicates, `match` on constructors | allocator laws, layout lemmas per type (derivable per `structure`) | same; contract: memory bound | linked list, hash map, tagged dispatch; lean-svg's `Array Svg.Node`, `Style` |
| 5 | `Int`/big `Nat` policy per client, polymorphism by specialisation, `HashMap` replacement, the long tail of core functions (`SURVEY.md` D) | per core function, a counterpart lemma | same | the compiler core (self-hosting: its `List (BitVec 32)` output and `Exp`/`Stmt` inductives need stage 4; its `partial`/`Nat` use decides the rest), lean-svg `render` |

Evidence behind the ordering:

- Stage 0 cost: about 1 400 lines of Lean for the three files, of which 500 are the generic layer. Per function the
  marginal human cost was zero for 12 functions (one line `with …` for the two fuel loops); the marginal machine cost
  is under 1.2 s. The machine theorem for one of them (`crcCode_ok`) is 25 lines of glue of the kind
  `msortCode_ok` has, not generated yet (generating it is mechanical: `envOf`, `HeapRel` from `bytesAt`).
- Speed is a standing requirement (`ROADMAP.md`); at 638 instructions per byte the generated CRC is far from it.
  The causes listed in section 5 are all in `prog`/`comp` (once-and-for-all code): a conditional statement in
  `BStmt`, direct loop conditions, and register allocation would be proved once and change no per-function proof.
- Stage 1 items are each a local extension of what exists (estimates in section 6: 60–150 lines each); none needs a
  new middle-layer mechanism. They are what separates the current examples from compiling lean-svg's small
  functions verbatim.
- Stage 2 is where lean-svg's own CRC-32 and base64 sit: its CRC is table-driven (`Array UInt32`, `ByteArray.foldl`)
  and its loops are `for` loops. The bitwise CRC of this branch computes the same function but is not lean-svg's
  definition; no equality between the two was proved.
- Stages 3 and 4 need new middle-layer mechanisms (calls, allocator) that this experiment did not touch; the
  front-end side of both is the same scheme (unfolding equation → node rules → `f.induct`), because `f.induct` exists
  for every recursion Lean accepts.
- The recurring per-function human input in every stage is the size contract (6.1, 6.4): `Nat`/`Int` bounds and
  buffer capacities. lean-svg has the limits in its code (`maxInput`, `maxDim`, `maxPixels`); turning them into
  per-function preconditions is the part that does not come for free.

## 8. Reproduce

```
bash setup/box.sh                               # once
lake build Proven.Frontx.Examples               # source-level theorems (needs Proven.Arr2Src built)
lake build Proven.Frontx.Machine                # + crcCode_ok on the Sail model (needs Proven.Arr2F, slow)
lake env lean asm/emit_frontx.lean && python3 asm/frontx_test.py check 40   # QEMU + Sail C emulator, ~50 s
```

`frontx_compile f` prints one line per function: variables, obligations, times.

## 9. Round 2

New files: `Proven/Frontx/For.lean` (102 lines), `ForExamples.lean`, `ForMachine.lean`; `Translate.lean` is now
1 310 lines, `Tree.lean` 563, `Rep.lean` 208, `Machine.lean` 134. All kernel-checked, same axiom sets as before
(source level: `propext`, `Classical.choice`, `Quot.sound`; machine level: the 77 of `msortCode_ok`).
`lake build Proven.Frontx.ForMachine` builds everything (Frontx files: about 30 s after `Proven.Arr2F`).

A correction to how round 1 may read: the full 8-bit-step CRC-32 has had an automatic equation proof and the
machine theorem `crcCode_ok` since round 1. What failed past 3 bit steps was only the *first proof method*
(one `simp` over a whole iteration): term size 3^n from substituting temporaries and unfolding helpers, hitting
`simp`'s step limit. It is not a depth limit and not proof search; section 5.1.

### 9.1 Expression depth (`BStmt.wf` needs depth < 7, < 6 for indices)

`fit` in `Translate.lean`: every expression the translator emits is cut to depth ≤ 5; a subexpression that does not
fit goes to a fresh temporary (`let_` node; the proof step is `sim_let` with the value `E.denote env`, by `rfl`).
No Lean term is attached to such a temporary, so nothing changes in the obligations. The command now also defines
`f.slots` (variables − 8, the `N` of `compileBF`). Result: `b64Sum` (lean-svg `at'` + `b64Digit` in a fuel loop)
gets 2 more variables and the machine theorem `b64Code_ok`.
`Machine.lean` now has the glue once: `ro1_ok` (one read-only byte array at `a0`: initial source state from the
registers, `HeapRel` from `bytesAt`). A machine theorem is then `ro1_ok wf … (f.exec …)`, 3 lines of proof, with
`wf` by `decide +kernel`. Not generated by the command yet (the statement's register hypotheses are still typed
by hand).

### 9.2 `for` loops in `Id.run do` with mutable locals

Once and for all (`For.lean`): `forIn_range_eq` (a `forIn [a:b] init F` in `Id` is the iteration `forFrom`,
from core's `Std.Legacy.Range.forIn_eq_forIn_range'`), `for_runs`, and

```lean
theorem for_exec (L : Lay) {t : Tree} (hw : t.wf L) (hro : t.ro = true) (R : Nat × S → BState → Prop)
    (F : Nat → S → Id (ForInStep S)) (post : S → BitVec 64) (a b : Nat) (init : S)
    (inits : List (Nat × BExp)) (out : Nat)
    (hstep : ∀ i s σ, R (i, s) σ →
      Sim R t σ (dite (i < b) (fun _ => cvt post i (F i s).run) (fun _ => .ret (post s))))
    {env : BEnv} {heap : Heap} (h0 : R (a, init) ⟨seqSet env inits, heap⟩) :
    ∃ σ', BExec (initS inits (prog L t out)) ⟨env, heap⟩ σ' ∧
      σ'.env out = post (forIn (m := Id) [a:b] init F).run ∧ σ'.heap = heap
```

The tree's state is the loop index plus the mutable locals; one tree iteration is "if `i < b` then the body, where
`ForInStep.yield s'` is a call with `(i + 1, s')` and `ForInStep.done s'` returns the code after the loop applied to
`s'`, else return". No induction is generated per function: the induction over the range is inside `for_exec`.

Per function (`compileLoop` in `Translate.lean`), all automatic:
- the body is found as `Id.run (lets; forIn [a:b] init F >>= post)`, unfolding helper definitions at the head
  (so `skipWs bs i := skipWhile bs i isWs` is the loop of `skipWhile` with the predicate filled in: a
  function-typed parameter is handled by specialisation);
- `let mut` variables are the components of the `MProd` state; `F i ⟨x…⟩` is translated with the same node rules as
  a recursive body, after stripping the `Id` structure (`bind`, `pure`, `__do_jp` join points are beta-reduced;
  all definitional, the kernel re-checks);
- `break` is `ForInStep.done`; early `return v` is an `Option` in the loop state that is `none` at every `yield`
  and `some v` at a `done`: such a local gets no machine variable, the relation says it is `none`, and the
  fall-through leaf is transported along that equation;
- the initial values are assignments before the loop (`f.inits`), their obligations are those of a call leaf;
- `f.step1` (the `hstep` of `for_exec`), `f.exec : ∀ params σ, f.Rep0 params σ → ∃ σ', BExec (initS f.inits
  (prog f.lay f.tree out)) σ σ' ∧ σ'.env out = rep (f params) ∧ σ'.heap = σ.heap`. That `rep (f params)` is the
  `post (forIn …)` of `for_exec` is checked by the kernel by unfolding `f`.
- `frontx_compile f with inv`: for a loop, `inv : params → index → locals → Prop` is the loop invariant; it is
  needed when a local is an unbounded `Nat` (lean-svg's `j` in `skipWhile`/`findByte`: `j ≤ i`).

Non-recursive functions: the same translation, `fun_cases` instead of `fun_induction`.

Results (`ForExamples.lean`, 4.3 s for the file; lean-svg code verbatim unless noted):

| function | source | kind | variables / slots | obligations | time | machine theorem | QEMU + Sail |
|---|---|---|---|---|---|---|---|
| `sumTo` | own | `for`, `let mut` | 12 / 4 | 17 | 0.3 s | – | – |
| `findByte` | `Bytes.lean:38` | `for`, early `return`, `at'` | 16 / 8 | 32 | 0.45 s | `findCode_ok` (140 words) | 30 cases ok |
| `skipWs` (= `skipWhile … isWs`) | `Bytes.lean:26,32` | `for`, `break`, predicate parameter | 16 / 8 | 29 | 0.45 s | – | – |
| `skipWsComma` | `Bytes.lean:35` | same, lambda predicate | 16 / 8 | 29 | 0.45 s | – | – |
| `be32` | `PngDecode.lean:36` | no loop, 4 guarded reads, `Nat` `<<<`/`\|\|\|` | 14 / 6 | 16 | 0.8 s | `be32Code_ok` (198 words) | 30 cases ok |
| `le16` | `GifDecode.lean:42` | no loop | 10 / 2 | 8 | 0.3 s | – | – |
| `b64Digit` | `Font.lean:554` | no loop, `if` chain | 13 / 5 | 11 | 0.35 s | – | – |
| `toLower`, `isNameChar` | `Bytes.lean:20–23` | no loop, `Bool` result | 5 / 0, 3 / 0 | 3, 1 | 0.1–0.2 s | – | – |
| `b64Sum` (round 1, now with splitting) | `at'` + `b64Digit` in a fuel loop | recursion | 18 / 10 | 15 | 1.1 s | `b64Code_ok` (615 words) | 30 cases ok |
| `crcGo` (round 1) | own, bitwise CRC-32 | recursion | 20 / 12 | 19 | 1.1 s | `crcCode_ok` (686 words) | 30 cases ok |

`python3 asm/frontx_test.py check 30` (all four programs, 50 s): result register equals the Python reference
(`zlib.crc32`, a transcription of `b64Digit`, `bytes` search, big-endian read with 0 past the end) on QEMU and on the
Sail C emulator, input and guards unchanged, `gp`/`sp` restored, stack unchanged outside the frame, Sail data writes
inside frames only. Instructions per call: `be32` 187, `findByte` 2 683 on average (inputs up to 492 bytes),
CRC 84 373 (638 per byte).

Human input in this round: the three `with` lines (`j ≤ i` twice, `i + 3 < 2^64`, `i + 1 < 2^64`), and for each
machine theorem its statement plus 3 lines.

### 9.3 What broke in round 2

1. `forIn` has 8 arguments in Lean 4.29 (no monad-instance argument), and the range type is
   `Std.Legacy.Range`.
2. A test `(A ∨ B ∨ C ∨ D)` written with `||` on `Bool`: proving `c.denote env ≠ 0 ↔ P` by `simp` left
   `¬A → ¬B → ¬C → D ↔ ((A ∨ B) ∨ C) ∨ D` (the negated side gets a different normal form). Tests are now discharged
   as `c.denote env = if P then 1 else 0` and converted by one lemma (`ne0_of_c`).
3. Generalising a `Nat` temporary (`j + 1`) to a variable loses its bound (`x < 2^64` unprovable). `Nat`
   temporaries now keep their defining equation as a hypothesis.
4. `(fun j y => …) x ()` left by join points: one `headBeta` is not enough; `idNorm` now beta-reduces at each step.
5. `frozen` is a keyword once the Sail model is imported (it was a local variable name; the standalone build
   accepted it).
6. A loop state `MProd (Option Bool) PUnit` has one local but is a pair: state construction must follow the type,
   not the number of locals.

### 9.4 Still not covered (met while trying lean-svg functions)

- A test before the loop or two loops in sequence / nested (`startsWith`, `eqAscii`, `eqAsciiCI`: `if sizes differ
  then false else Id.run do for …`; `findSeq` calls `startsWith` in its loop body). This is point 1 of 6.6:
  the program is one loop with initialisation. It is the next structural step.
- `Option`/tuple results (`hexVal`, `adlerChunk`), output arrays (`decodeUtf8`, base64 decoders, `be32` writer),
  `String` arguments (`s.toUTF8`), multiplication/division, word tables (lean-svg's CRC): unchanged from section 6.
- `Nat` `>>>`, `%`, `/` (only `+ - &&& ||| <<<` and comparisons have `rN` lemmas).
- Loops whose range bound is not a parameter or an array size (the bound must be `< 2^64` by `omega`).
- The machine theorem and its register hypotheses are not generated by the command.
- Code quality is unchanged (section 5): no work was done on `prog`/`comp`.

### 9.5 Updated plan

Stage 1 of section 7 is partly done (non-recursive entry points, expression splitting). Stage 2's `for` loops are
done for a single loop. In order of what blocks the most lean-svg code now:
1. sequencing and nesting in `Tree` (pre-tests, several loops, a loop in a loop body); with it `startsWith`,
   `eqAscii`, `findSeq`, `adler32Rows`-shaped code;
2. results other than one scalar: tuples, `Option` (tag + payload);
3. output buffers (`push` with capacity) and in-place `set`;
4. generate the machine theorem from the command (`ro1_ok` generalised to several arrays and to writes);
5. `prog`/`comp` code quality: a real conditional in `BStmt`, loop conditions without the flag variable.
Not rebased: this branch is still on `9310b1a`; the reorganised `main` renames the modules (`Proven.X` →
`Riscv.Direct.X`), so a rebase is a rename of the imports of five files plus a full rebuild.


## 10. Round 3 (book functions over `Nat`; in progress)

`Proven/Frontx/BookExamples.lean`: 14 functions of "Functional Programming in Lean" (survey verdict "B", branch
`booksurvey`) with the book's own definitions, all with automatic `exec` theorems (axioms `propext`,
`Classical.choice`, `Quot.sound`): `add1`, `maximum`, `isZero`, `pred`, `Nat.double`, `triple`, `quadruple` (no
recursion); `even`, `plus`, `times`, `minus`, `double` (structural recursion on `Nat`, the call NOT in tail
position); `div` (well-founded, `1 + div (n - k) k ok`, with its proof argument `ok : k ≠ 0`), `halve`
(patterns `0`, `1`, `n + 2`).

New in the translator:
- **Primitive recursion on `Nat` as a loop** (`natRec_forIn` in `For.lean`, once and for all): `f 0 = b`,
  `f (k'+1) = E[f k']` with the other arguments unchanged is the loop `acc := b; for j in [0:k] do acc := E[acc]`.
  This is the accumulator transformation with no algebra on the result; the per-function part is
  `∀ j, f (j+1) = h j (f j)` by `rfl`.
- **Accumulator mode** for `f x = g + f x'` under arbitrary tests (any recursion Lean accepts, `Nat` result):
  the tree carries `acc`, `f.runs` is stated for `acc + f x` and proved by `fun_induction`; the reassociation at
  each recursive call is `omega`. Chosen automatically when the plain translation finds a non-tail call. Not
  mechanical (and rejected) when the context of the call is not `· + g`: e.g. `f x' * 2`, two recursive calls.
- `match` on a `Nat` with several patterns (`0`, `1`, `n + 2`): tests `n = c` in order, then `n - c`.
- truncated `Nat` subtraction (`rN_sub'`): plain `sub` when `b ≤ a` follows from the context by `omega`, else a
  select; proof-valued parameters (`ok : k ≠ 0`) are passed through and carry no variable.
- `frontx_compile f with inv using eq₁, eq₂`: `using` gives equations `g args = closed form` used instead of
  unfolding `g` (needed because there are no calls: `times` calls `plus`, `minus` calls `pred` inside the
  recursion). Human input for the 14 functions: `plus_eq`, `pred_eq`, and the invariant `acc ≤ n` of `minus`.

Bounds: form (1)/(2) of the owner's list as hypotheses of the generated theorem (`n < 2^64` per `Nat` parameter in
`f.Rep`), in the function's own signature for `div` (`ok`). Results are stated as `BitVec.ofNat 64 (f args)`:
for `add1`, `plus`, `times`, `double`… no no-overflow hypothesis is needed for that statement (it is the value mod
2^64); `minus` needs `acc ≤ n` because `pred` tests its argument against 0. Fuel form (3): fuel recursion already
works (`adlerA`, `b64Sum`); a step bound in terms of fuel is not proved.

Not done from the "B" list: everything over `List` (`length`, `take`, `drop`, `reverse`, `sum`, `filter`,
`mergeSort`, `insertionSort`: a list parameter needs the array-view representation, the existing `compile%`
pipeline covers `take/drop/reverse/map/fold` on `List UInt8`), `timesTwelve`, `Pos.plus`/`Even.plus` (structures).

### 10.1 A test before the loop, `String` arguments (lean-svg `startsWith`, `eqAscii`, `eqAsciiCI` verbatim)

All three compile with automatic `exec` theorems (`ForExamples.lean`; 27–35 obligations, about 2 s each).
- `if c then v else loop` needs no sequencing of programs: `pretest_eq` (`For.lean`, once) rewrites it to the loop
  over `[a : if c then a else b]` followed by `if c then v else post`; the existing loop path does the rest
  (the test is evaluated again at each iteration and at the exit: a code-quality cost, not a proof cost).
- A `String` parameter is the heap block `blk s.toUTF8` (two variables, base and length), read through
  `s.toUTF8` exactly as lean-svg does.
- `frontx_compile f requires pre with inv using eqs`: `requires` is a precondition on the parameters (for
  `startsWith`: `i + s.toUTF8.size < 2^64`, the sum the test computes); `with` stays the loop invariant.
- Compound `Nat` comparisons (`i + sb.size > bs.size`) now work: a compound side goes to a temporary whose
  defining equation is kept for `omega`; a temporary defined by an `if` contributes `x = a ∨ x = b`.
What broke: `simp` rewrites `s.toUTF8.size` to `s.utf8ByteSize` (two library simp lemmas, now excluded); a `first`
alternative containing `t <;> omega` inside a `simp` discharger logs errors instead of failing (error recovery is
on there); `ite` reached the `Bool` translator before the value-level `if` rule.
Still open from the sequencing item: two loops in sequence and a loop inside a loop body (`findSeq` calls
`startsWith` per iteration): these need a call or a nested-loop node; not started.

### 10.2 Results with several components (pairs, `Option`)

lean-svg `Svg.hexVal : UInt8 → Option Nat` and `Png.adlerChunk : … → UInt64 × UInt64` compile verbatim
(`ForExamples.lean`), with automatic `exec` theorems of the form
`∃ σ', BExec (prog …) σ σ' ∧ σ'.env out = rep (π₀ (f xs)) ∧ σ'.heap = σ.heap ∧ AllEnv σ'.env [(v₁, rep (π₁ (f xs))), …]`.
- A result type `α × β × …` or `Option α` over scalars is a list of components `π_j` (`Prod.fst/snd` chains;
  `Option.isSome` as a 0/1 word and `fun o => o.getD 0`); component 0 is the result variable, the others get their
  own variables, assigned just before the `ret` leaf.
- Once and for all (`Tree.lean`): outcome `LOut.retm r rs`, `sim_retm`, `step_callQ`/`step_retQ`, `prog_okQ`,
  `AllEnv`. Per function: the same obligations as before plus one per extra component and leaf.
- Limits: recursion / non-recursive path only (not `for` loops, not accumulator mode); a leaf must be a
  constructor application (`(a, b)`, `some v`, `none`) after unfolding; tuple/`Option`/structure *parameters* and
  `match` on them are not done; results are not yet laid out as bytes per `Encode.lean` (they are in variables).
- New lemma family for `c.toNat - n` on fixed-width `c` (`r8_toNat_sub`, `r32_toNat_sub`).

### 10.3 Structures, tuples and `Option` as parameters; `match` on them

`Proven/Frontx/DataExamples.lean` (all generated): `addPoints (p1 p2 : Point) : Point` (structure of two `Nat`),
`swap : UInt64 × UInt64 → UInt64 × UInt64` (`match p with | (a, b)`), `getOr : Option Nat → Nat → Nat`
(`match o with | none | some v`), `fst3 : Nat × UInt8 × Bool → UInt8`, `zeroX` (`{ p with x := 0 }`),
`countdown` (recursion whose state is a `Point`; needs `with fun p => p.y + 2 * p.x < 2^64`: `Nat` fields carry the
usual 64-bit bound).
- A parameter of a structure type whose fields are scalars (nested allowed, `Prod` included) is one variable per
  field, keyed by the projection terms; `f.Rep` has `σ.env v = rep (p.f)` per field; a `match p with | ⟨a, b⟩` is
  `B p.1 p.2` (accepted by the kernel through structure eta), no test is emitted.
- `Option α`: variables for `o.isSome` and `o.getD 0`; `match o` is a test of the first with `v := o.getD 0`.
  The representation requires payload 0 for `none`.
- Results of any such structure type use the same component list (10.2).
- No allocation, no layout yet: components are variables (registers/slots). Writing/reading them as bytes per
  `Encode.lean` (`Bytes` instances) is the missing link to the `Implements`-style statement.
Not done: enum-like inductives (tag word; needs per-type lemmas), sums with payloads other than `Option`,
recursive inductives (allocation), these types inside `for` loops or accumulator mode.

## 11. Round 4: rebase, `Implements1` theorems generated, lists as views, specialisation

Rebased onto `main` 87b3831 (`Spec/ Compiler/ Riscv/ Arm/ Testing/`). Modules renamed `Proven.Frontx.X` →
`Riscv.Frontx.X`; imports `Riscv.Direct.Arr2Src`/`Arr2F`. `Riscv.Examples.LoopExamples` is no longer imported
(it clashes with `ArrExamples`, which the `Implements1` glue needs): `sumDown`/`gcdSub` are copied into
`Examples.lean`. The old machine theorems (`crcCode_ok` … via `ro1_ok`, `compileBF_ok`) are replaced.

Kernel-checked here (`lake build Riscv.Frontx.Machine Riscv.Frontx.BookExamples Riscv.Frontx.DataExamples
Riscv.Frontx.ListExamples` against the Sail model):

| what | where | axioms |
|---|---|---|
| `exec_up`, `wfB_up` (a `Proven.BStmt` program and its run, mapped into the middle layer with more blocks), `implements1_of_frontx`, `Res` (result encodings: `UInt8/32/64`, `BitVec 64`, `Nat` mod 2^64, `Bool`) | `Impl1.lean` | `propext`, `Classical.choice`, `Quot.sound` + the Sail model's (through `implements1_of_exec` of `Riscv/Back/Implements1.lean`) |
| `g.implements1` for 8 entry points, generated by `frontx_entry g` + `frontx_implements g` | `Machine.lean` | 77, the same set as main's `sum_implements1` (compared as sets) |

The generated statement (single bound, `Spec/Implements1.lean`):

    g.implements1 : Implements1With (fun xs => xs.data.toList) Res.enc g.code g (fun _ => 8 * (g.slots + 1) + 7)

`g.code = compBFO N [0, 3] [2] (.seq (toMS g.prog) (store8 k))` — the optimised drop-in for the standard entry point
`rvF.codeF (rvF.compBF …)` (`Riscv/Back/Implements1Opt.lean`, proof `implements1_of_execO`; switched at the merge into
main: e.g. CRC-32 810 → 201 words); `store8 k` (main's) writes the `k+1` result bytes. Input: the raw bytes (`maxLen` = 2^20 default);
output: `Res.enc` (little-endian). Generated programs now keep variables 2 and 3 free (work/output base) and start
scalars at variable 4. Per entry point nothing is written by hand; well-formedness and "variable 2 is never
assigned" are `decide +kernel`.

Entry points (the function on the whole input): `crcRaw xs = crcGo xs 0 0xFFFFFFFF`, `b64All xs = b64Sum xs 0
xs.size 0`, `findNL xs = findByte xs 0 10`, `be32At0 xs = be32 xs 0`, and the book's `Tail.sum`, `NonTail.sum`,
`Tail.length`, `length` (MatchDef) on `xs.data.toList`. `frontx_entry g [from eq]`: `g xs` (or the right side of
`eq`) must be `f xs a₁ … aₙ` with `aᵢ` closed or `xs.size`.

Tested, not proved: `python3 Testing/asm/frontx_test.py check 40 <fn>` for all 8, QEMU and the Sail C emulator,
`Implements1` calling convention (a0 input, a1 length, a2 work base, a3 output, sp = work end), lengths 0..2996:
output = Python reference, input and guards unchanged, `gp`/`sp` restored, every Sail data write in the result bytes
or the work block. Code sizes: 810 (crcRaw), 676, 286, 335, 220, 224, 216, 218 words; work space 47–127 bytes.

Translator additions (all checked in the Sail-free sandbox and in the lake build):
- `frontx_compile f from eq measure μ`: a proved recursion equation `f xs = body` instead of the unfolding
  equation; `f.runs` by strong induction on `μ xs : Nat` (decrease by `omega`), outcome-directed case splits
  (`frontx_cases`). Tail calls and accumulator mode.
- `frontx_view f`: a `List UInt8` / `List Nat` parameter is the input block from index `i` on
  (`view B i = B.data.toList.drop i`, `viewN` for `List Nat`); type parameters are instantiated with `UInt8`;
  adds `f.view` and `f.view.eq : f.view B i … = if h : i < B.size then <cons case>[x := B[i], t := view B (i+1)]
  else <nil case>`, recursive calls on the tail folded. Only `match xs with | [] | x :: t` (2 patterns).
- `frontx_spec g` for `def g ys := f a₁ … aₙ`: specialisation of polymorphic / higher-order `f` at fixed arguments
  (types, instances, functions); `g.eq` is `f`'s unfolding equation with the recursive calls folded to `g`
  (rejects a recursive call that changes a fixed argument).
- multiplication by a `Nat` literal: shifts and adds through a generated `mulLitL_c : c * x = x <<< k₁ + …`
  (`omega`). Fixed-width multiply and variable × variable: not done (no multiply in `Op`, `Spec/` is frozen).
- `frontx_u8_facts` (bounds `x.toNat < 256` for loaded bytes, used by `omega` in obligations).
- fail-fast: every generated `exec` is checked to depend on `propext`, `Classical.choice`, `Quot.sound` only
  (`checkAxioms`); `addThm` fails unless the result is a theorem. Reason: a kernel failure inside one command had
  left a lemma behind as an axiom (found by `#print axioms`, fixed, now caught automatically).

Book "B" functions in this round (`ListExamples.lean`, `BookExamples.lean`, book text verbatim from
`leanprover/fp-lean`, all with automatic `exec`): `Explicit/BetterPlicity/AutoImpl/MatchDef.length`,
`NonTail.sum`, `NonTail.length`, `Tail.sumHelper`, `Tail.lengthHelper` (+ `Tail.sum`, `Tail.length` as entry
points), `Floop.List.head?`, `List.findFirst?` specialised to `(· > 3)`, `NewNamespace.triple`/`quadruple`
(now verbatim `3 * x`, `2 * x + 2 * x`), `timesTwelve`. Bound forms used: `Tail.sumHelper` needs
`with soFar + 255 * (B.size - i) < 2^64` (form 1, an invariant), `Tail.lengthHelper` `soFar + (B.size - i) < 2^64`,
`timesTwelve` `requires 12 * x < 2^64`; the others none. Not done from the "B" list: `List.final?` (3 patterns),
functions returning a list (`take`, `drop`, `reverse`, `filter`, sorts: need an output buffer), `Pos.plus`,
`Even.plus` (user inductives, not enum-like).

Not done / still open: output buffers (list results), nested/sequenced loops and calls (the `calls` box), enum-like
inductives, entry points with more than one input / non-scalar results, multiply. Main's
`Riscv/Examples/Crc.lean` does not build at 87b3831 (unsolved goals at lines 50, 72, 91, 117); nothing here
imports it.

Reproduce (repo root):

```
lake build Riscv.Frontx.Machine Riscv.Frontx.BookExamples Riscv.Frontx.DataExamples   # ~1 h clean (Sail), then ~1 min
lake env lean Testing/asm/emit_frontx.lean
for f in crcraw b64all findnl be32at0 tailsum nontailsum taillength booklength; do
  python3 Testing/asm/frontx_test.py check 40 $f; done
```


## 12. Round 5: list results, general `match` shapes, `Option` results, calls

### 12.1 List results (output block, length in `a1`)

A function whose result type is `List UInt8` is compiled in **list mode** (chosen by the result type):
destination passing with two hidden parameters, the output index `j` (a variable) and the output block `O`
(heap block 1, no variable; `a3` in the `Implements1` convention). Once and for all (`Tree.lean`):
`wrO O j L = O.take j ++ L.map toBitVec ++ O.drop (j + |L|)`, `wrO_nil`, `wrO_cons`, the outcome `LOut.reth r H`
(result and heap), `sim_reth`, `sim_store1` (a `store` node into block 1). Per function, generated:
- `f.Rep … j O σ`: heap `[blk B, O]`, `env jv = rN j`, `|O| < 2^64`, and the capacity `j + |f xs| ≤ |O|`;
- tree leaves: `[]` → `ret j`; `y :: t` → `store 1 j y`, continue with `j + 1`, `O.set j y`; a recursive call →
  tail call with the current `j`, `O` (so `x :: f xs'`, `f xs'` (filter), `a :: b :: f xs'` all work);
- the store bound `j < |O|` and the capacity of a call are proved from the capacity hypothesis rewritten by the
  function's equation and the path conditions (`capOblig`);
- `f.runs : Rep … → ∃ σ', Runs σ (rN (j + |f xs|)) σ' ∧ σ'.heap = [blk B, wrO O j (f xs)]` (strong induction on
  the measure; each leaf closes by `wrO_cons`/`wrO_nil` and `omega`), `f.exec` from `j = 0`.
- `Impl1.lean`: `implements1_list` (once): such a program, then `a1 := v4`, compiled by `compBFO`, gives
  `Implements1With (fun xs => xs.data.toList) (fun l => l) code f space (retLen := true)`;
  `frontx_implements_list g` generates `g.code`, `g.implements1`.

**General `match` shapes in `frontx_view`** (needed for `take`/`drop`, `match n, xs with …`, and `final?`,
`[y]` / `y1 :: y2 :: ys`): the body of `f … (view B i) …` is normalised (`vnorm`): a stuck `match` is split on a
discriminant that is a view (`if h : k < B.size`, `B[k] :: view B (k+1)` or `[]`), a `Nat` (`if n = 0`, `0` or
`n - 1 + 1`) or a view inside a discriminant, and reduced (`reduceMatcher?`); `B[k] :: view B (k+1)` is folded
back to `view B k` and recursive calls to `f.view`. The equation is proved by following the tests of the
right-hand side (`veqGo`: `by_cases`, `view_eq`, `subst`, `rfl`). Several list parameters are views of the same
block with their own indices (`append xs ys`).

**Results that end with the rest of the input** (`drop 0 xs = xs`, `[] ++ ys = ys`):
`frontx_tailcopy f.view measure μ` defines `f.view.cp … m k := bif m then view B k else f.view …`, its equation
(copy loop when `m`, else the body with `view B k'` ↦ `cp … true k'`, recursive calls ↦ `cp … false k`) and the
measure; the copy is a mode of the same loop, so nothing else changes.

### 12.2 `Option UInt8` results as bytes

`Res (Option UInt8)` (`Impl1.lean`): two bytes, tag and payload (`0` for `none`), the word `rOpt8 o = tag +
(payload <<< 8)`; `frontx_entry` joins the two result variables (`opt_join`, `Rep.lean`). `head?`, `final?`,
`findFirst?` now have machine theorems.

### 12.3 Results (all generated; source level 3 axioms, machine level the 77)

| entry point | book function | words | work bytes | QEMU + Sail vs Lean |
|---|---|---|---|---|
| `take5` | `take 5` (Intro, `match n, xs`, 3 patterns) | 80 | 87 | 50 cases ok |
| `drop5` | `drop 5` (Intro, pattern definition) | 135 | 119 | 50 cases ok |
| `matchDrop3` | `Match.drop 3` | 135 | 119 | 50 cases ok |
| `filterAll` | `NonTail.filter (· > 3)` | 72 | 71 | 50 cases ok |
| `incEach` | `List.map (· + 1)` | 59 | 55 | 50 cases ok |
| `twice` | `xs ++ xs` (`List.append`, two views) | 108 | 111 | 50 cases ok |
| `headOf` | `Floop.List.head?` | 57 | 39 | 50 cases ok |
| `finalOf` | `Floop.List.final?` (patterns `[]`, `[y]`, `y1 :: y2 :: ys`) | 77 | 71 | 50 cases ok |
| `findFirstGt3` | `List.findFirst? · (· > 3)` | 76 | 63 | 50 cases ok |

Tests: `frontx_test.py` now takes the cases from `frontx-words/<f>.cases`, written by `emit_frontx.lean` with the
result computed by Lean (`#eval` of the function: "executed Lean"); output block exactly the result's length, so the
capacity hypothesis is tight; `a1` = length checked for list results; the Python references of the older entry
points are kept as a second check.

### 12.4 Calls to translated functions (inlined sub-programs, `Tree.sub`)

A call `g args` in the body of `f`, where `g` was compiled by `frontx_compile` (it has `g.exec` with the result in
its variable 4, heap kept, at most one byte-array parameter = `f`'s first block), becomes a **sub-program**: `g`'s
whole program runs inside `f`'s iteration, its variables renamed into a fresh range `b .. b + n` of `f`'s
(`rho b`: `g`'s variables `0 .. 3` are `f`'s, `4 + j` is `b + j`), its temporaries cleared afterwards (`callP`).
A call to a recursive (looping) `g` is a nested loop. Everything stays a `BStmt`, so the machine theorem is the
same `compBFO` route as before. Once and for all (`Sub.lean`, 3 axioms): `BExec.detF` (determinism), `exec_agree`,
`exec_ren` (a renamed run), `callP_exec`; `Tree.sub` with `sim_sub`, `comp_ok_sub`, the `ro`/`wf` cases
(`Tree.lean`). Per call, generated: the arguments are assigned to `g`'s parameter variables (`let_` items;
their temporaries are placed inside `g`'s range, which is cleared after the call, so the range is shared), the
obligations of `g.Rep` for the renamed state, `g.exec` applied, `callP_exec`. A recursive `g` is always called; a
non-recursive one is inlined as before and called only when inlining fails (e.g. `pred`'s `match` in a value
position); a non-recursive callee may be unfolded in later obligations (facts about its result).

Results:
- book `minus` calls `pred`: **no `pred_eq` any more** (the invariant `acc ≤ n` stays: `pred`'s argument must be
  `< 2^64`; `pred x ≤ n` is proved by unfolding `pred`).
- `times` still uses `plus_eq`: as a call, `plus n acc` needs `acc < 2^64`, i.e. `times n j < 2^64`, which is a
  fact about `times` (no generated theorem gives it); the closed form is the honest way.
- entry points for all 15 `Nat` book functions (`Machine.lean`, `BookNat`): `fAt xs i := f (u16 xs i) …` calls the
  compiled book function, `fE xs := fAt xs 0`; 5–16 slots; `fE.implements1` for each.
- nested loops: `CallExamples.lean`, `countDup` (a loop over `k` calling the loop `occursFrom bs (k+1) bs[k]`),
  entry `dupCount`, 14 slots, 144 words, QEMU + Sail on inputs up to 2769 bytes (≈ 3.8 M iterations).

Limits (why lean-svg `findSeq` → `startsWith` is not done): (1) the variables of caller and callee share the
24 machine variables of `compBFO` (`N ≤ 16` slots): `startsWith` alone has 20 variables, `findSeq`'s loop ~14;
(2) `startsWith` takes a `String` (a second block) — callee blocks must be the caller's first block; (3) a Nat
result of a callee is opaque: comparing it (`findByte … < bs.size`) needs its bound `< 2^64`, which no generated
theorem states. (1) and non-tail self-recursion need real calls with frames (`MachineC`, `Compiler/CStmt.lean`):
that route has no `Implements1` bridge on the optimised back end yet (`callsCode_implements` is the `ImplementsW`
form, unoptimised), so it is not used here.

### 12.5 The book's "B" list (survey `book_survey.csv`, branch `booksurvey`) and some "C" functions

"Machine theorem" = a generated `g.implements1 : Implements1With …` (single bound, optimised back end
`compBFO`/`implements1_of_execO`, the standard 77 axioms) for an entry point `g` on the input bytes; all source-level
theorems (`f.exec`) depend on `propext`, `Classical.choice`, `Quot.sound` only. "Test" = `frontx_test.py check 50`:
QEMU and the Sail C emulator against the result computed by Lean (`#eval` of the book definition,
`emit_frontx.lean`), all cases ok (`Testing/scripts/frontx_tests.sh` runs all 37 entry points).
Book text verbatim unless noted. `Nat` arguments of entry points are 16-bit little-endian numbers in the input
(`u16`, `BookExamples.lean`); `Nat` results are 8 bytes mod `2^64`, `Bool` 1 byte, `Option UInt8` 2 bytes, lists
their bytes with the length in `a1`.

| book function (chapter) | machine theorem | entry point | words | human input / reason if no |
|---|---|---|---|---|
| `add1` (1) | yes | `add1E` | 90 | – |
| `maximum` (1) | yes | `maximumE` | 131 | – |
| `isZero` (1) | yes | `isZeroE` | 102 | – (called: `match` in value position) |
| `pred` (1) | yes | `predE` | 123 | – (called) |
| `even` (1), `Match.even` (1) | yes, yes | `evenE`, `matchEvenE` | 110, 110 | – (loop, called) |
| `plus` (1) | yes | `plusE` | 164 | – |
| `times` (1) | yes | `timesE` | 164 | closed form `plus_eq` (`plus n acc` needs `acc < 2^64`: a fact about `times`) |
| `minus` (1) | yes | `minusE` | 271 | invariant `acc ≤ n` (no closed form any more: calls `pred`) |
| `div` (9, `Div.lean`; the Intro version is a non-terminating error example) | yes | `divE` | 163 | divisor `u16 + 1` (the book's `ok : k ≠ 0`) |
| `halve`, `Match.Explicit.halve` (1) (`Match.Oops.halve` is an error example) | yes, yes | `halveE`, `explicitHalveE` | 145, 145 | – |
| `double`, `Nat.double` (1) | yes, yes | `doubleE`, `natDoubleE` | 131, 90 | – |
| `triple`, `quadruple`, `timesTwelve` (1) | yes | `tripleE`, `quadrupleE`, `timesTwelveE` | 92, 91, 97 | – |
| `length`: `Explicit` (= `Ooops`/`Oooops` text), `BetterPlicity`, `AutoImpl`, `MatchDef` (1) | `MatchDef`: yes; others source level (same shape) | `bookLength` | 73 | – |
| `NonTail.length`, `Tail.length` (9) | yes, yes | `nonTailLength`, `tailLength` | 73, 73 | `Tail`: invariant `soFar + (size - i) < 2^64`; `NonTail` also with real calls (`nonTailLengthRec`, section 15) |
| `NonTail.sum`, `Tail.sum` (9) | yes, yes | `nonTailSum`, `tailSum` | 78, 77 | `Tail`: invariant `soFar + 255 (size - i) < 2^64`; `NonTail` also with real calls (`nonTailSumRec`, section 15) |
| `List.head?` (1) | yes | `headOf` | 57 | – |
| `List.final?` (1, 3 patterns) | yes | `finalOf` | 77 | – |
| `List.findFirst?` (1) | yes | `findFirstGt3` | 76 | specialised to `(· > 3)` (`frontx_spec`) |
| `take` (1, `match n, xs`) | yes | `take5` | 80 | – |
| `drop` (1), `Match.drop` (1) | yes, yes | `drop5`, `matchDrop3` | 135, 135 | – (`frontx_tailcopy`) |
| `NonTail.filter` (9) | yes | `filterAll` | 72 | specialised to `(· > 3)` |
| `reverse` (1, `let rec helper` with `soFar`), `Tail.reverse` (9) | no | – | – | a list accumulator (`soFar`): a list parameter that is not a view of the input |
| `Tail.filter` (9, `filterHelper`) | no | – | – | list accumulator, then `accum.reverse` |
| `NonTail.reverse` (9, `reverse xs ++ [x]`) | no | – | – | non-tail recursion whose result is used under `++`: needs real calls with a stack (or the length of the recursive result) |
| `mergeSort` (9) | no | – | – | `splitList` returns a pair of lists, `merge` takes two lists that are not views: needs allocation / list values in memory |
| `insertionSort` (9, `Array`, both versions) | no | – | – | in-place `Array.swap` and a `Fin` index: no array results / mutation in frontx |

Also: `List.map (· + 1)` (`incEach`, 59 words), `xs ++ xs` (`twice`, 108 words, core `List.append`), and from class
"C": `Both.sameLength` (two list inputs; `sameLen`, 131 words), and a nested loop `countDup` (`dupCount`, 144 words).
Not attempted from "C": everything needing multiply of two variables (`volume`, `factorial`), enums / user
inductives (`Weekday`, `BinTree`, `Pos`), strings as values, pair results as bytes (`Prod.switch`, `zip`, `unzip`),
monadic code (chapters 4–7).

Count (distinct B functions, variants merged): 26 of 32 compile with a machine theorem (`add1`, `maximum`, `isZero`,
`pred`, `even`, `plus`, `times`, `minus`, `div`, `halve`, `double`, `Nat.double`, `triple`, `quadruple`,
`timesTwelve`, `length`, `NonTail.length`, `Tail.length`, `NonTail.sum`, `Tail.sum`, `head?`, `final?`,
`findFirst?`, `take`, `drop`, `NonTail.filter`); 6 do not (`reverse`, `Tail.reverse`, `Tail.filter`,
`NonTail.reverse`, `mergeSort`, `insertionSort`).

Reproduce: `lake build Riscv.Frontx.Machine`; `lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean`
(the interpreter needs the stack for the book's non-tail recursions); `bash Testing/scripts/frontx_tests.sh`.

## 13. Speed (branch `frontx-speed`): fast loops, plain loads, sequential calls

Measured: `Testing/notes/BENCH_FRONTX.md`, last section (find 27 → 6, drop 26 → 6, sum 12 → 4, map 16 → 7,
filter 22 → 7.95, append 47 → 14 instructions per byte; gcc -O2 5, 5, 4, 6, 6.97, 7).

Why it was slow: one tree step per iteration of `while fl { comp t }`, every conditional two at-most-once loops
over 0/1 flags, call arguments through temporaries, the `at'` guard tested again in the loop, a byte mask before
each store; the optimiser's strength reduction needs `while i <u n` with a trivial head and an increment `i := i + 1`,
which none of these loops had.

What changed (all once and for all; the generated per-function proofs are untouched apart from three tactics):
- `Fast.lean` (new; `prog`, `prog_ok`, `prog_ok_ro`, `prog_okQ` moved here, statements unchanged): an iteration is
  now `fast loops; if fl { comp t }`. One fast loop per path of `ite`s from the root (`peel`) to a subtree `S`:
  * `S` all `call`s: `while Gv { S }`; pairs common to all leaves are assigned after the step (`common`,
    `hoist_step`, so `filter`'s `i := i + 1` is one increment); constant pairs `v := c` are dropped when `Gi` checks
    `v = c` (`kOf`, `strip_step`; drop's mode flag);
  * `S = X; if c then A else B` with `X` loads/lets and one branch all `call`s: `k := 1; while Gv ∧ k { X; k := c';
    if k { call branch } }; if Gv ∧ ¬c' { other branch }` (find, findFirst?);
  * conditions whose variables the loop does not write, `fl` and the constant checks are tested once outside (`Gi`).
  `FastOK` (the iteration invariant `Inv`: `m` more `call` steps to the result, or returned; steps never increase) for
  both shapes (`fastLoop_ok`, `fastExit_ok`, `fastOf_ok`), `iter_ok`, `loop_ok` by strong induction on `m`.
  An iteration whose old-compiler code would exceed `BStmt.wf`'s 1000 words keeps the plain step (CRC-32).
- `Tree.lean`: `call` leaves assigned in order when no later expression reads an earlier target (`seqOK`, `seqA_ok`);
  a stored value's `&&& 255` dropped (`unmask`, `and255`).
- `Translate.lean`: a guarded read whose guard follows from the path conditions and the invariant is a plain `load`
  (obligations proved like those of `load`, else the `cload` as before; `findByte`: `j < size` from `i < size`,
  `j ≤ i`). Proofs of `Tree.ro`, `prog_ok_ro`/`prog_okQ`'s `ro` and the callee `vltF` by `decide +kernel` (the new
  `prog` is too big for elaborator `rfl`/`decide`).
- `Compiler/Opt/Flow.lean` (`OPT.md`, last section) turns the at-most-once loops into `when`s, fuses the tests, moves
  the exit test of the search loop into the `loop2` head; then the existing strength reduction fires.

Not done: loop fusion (`twice`), merging the two counters of `for … in [i:n]` with `j` (find: 6 vs 5), strength
reduction of `loop2` loops and of loops with two indices, registers for `twice`'s reduced loops (see BENCH_FRONTX).
Tested: `frontx_tests.sh` (37 entry points, QEMU + Sail against Lean) all ok.

## 14. Round 6: tuples and structures, `%` / `/` by constants, `foldl` over bytes

Files: `Riscv/Frontx/PairExamples.lean` (targets, entry points, machine theorems), `Bytes.lean` (results as bytes,
once), additions in `For.lean`, `Rep.lean`, `Impl1.lean`, `Translate.lean`.

**Compiled verbatim** (source text copied, provenance in the file; no API edits were needed for Lean 4.29):

| function | source | machine theorem / entry | words | test (QEMU + Sail vs Lean) |
|---|---|---|---|---|
| `Adler32.Native.adler32` (+ `Spec.unpack`, `updateBytes`, `updateByte`, `pack`) | lean-zip @7e10583 `Zip/Native/Adler32.lean:17` | `adlerE xs = adler32 1 xs`, `Res UInt32` | 121 | 50 ok, and = `zlib.adler32` on all cases |
| `Adler32.Native.updateBytes` (pair result) | `Zip/Native/Adler32.lean:13` | `adlerStateE xs = updateBytes (1, 0) xs`, 16 bytes | 150 | 50 ok |
| `Spec.updateByte`, `pack`, `unpack` | `Zip/Spec/Adler32.lean:29,39,47` | source level (`exec`) | – | – |
| `BetterPlicity.replaceX` (`{ point with x := newX }`, `PPoint Nat`) | fp-lean @0abeea5 `Intro.lean:1203` | `replaceXE`, 16 bytes | 155 | 45 ok |
| `fromOption` (`Option` parameter, match) | `Intro.lean:1879` | `fromOptionE` | 139 | 50 ok |
| `MythicalCreature.small` (structure parameter) | `FunctorApplicativeMonad.lean:238` | `smallE` | 49 | 50 ok |
| `DataExamples` `swap`, `addPoints`, `zeroX`, and a nested `(UInt8 × UInt32) × Nat` | this repo | `swapE`, `addPointsE`, `zeroXE`, `nestE` | 132, 149, 119, 130 | 50 ok each |

Human input for Adler: `requires` = lean-zip's own `Spec.Valid (Spec.unpack init)` written out (`init.toNat % 65536 <
65521 ∧ init.toNat / 65536 < 65521`), `with a < 65521 ∧ b < 65521` (`Spec.Valid` of the state). Entry glue (the `…At`
functions reading bytes of the input) is not book code.

What was added:
- **`Array.foldl` over the bytes**: `foldFor?` finds `B.data.foldl g s` in the body (unfolding the user helpers that
  contain it, e.g. `updateBytes` inside `adler32`); `bfoldl_forIn` (`For.lean`, once) makes it the `for` loop over
  `[0:B.size]` with `g` inlined per byte; the code around it is the loop's post code (`pack`), its initial state is
  translated before the loop (`unpack init`). `ByteArray.foldl` (no library lemma relating it to `Array.foldl`) is not done.
- **Tuple loop state**: `flattenS`/`stateComps`/`mkState` flatten `Prod` (nested); `yield (g s b)` with a helper `g`
  returning the tuple is unfolded and its `let`s become temporaries.
- **Loops with several result components**: `cvtM`, `for_runsM`, `for_execM` (`For.lean`, once): the exit leaf sets the
  extra result variables (`retm`); `break`/`return` in such loops is rejected.
- **Structure / tuple parameters of loops and entries** (one variable per component, `resultComps`, now also with a tuple
  as first component); the first `ByteArray` parameter is block 0 wherever it stands (`adler32 (init) (data)`).
- **Results as bytes** (`Bytes.lean`): `storeC` writes the components after the program, `k` little-endian bytes each
  (`UInt8`/`Bool` 1, `UInt32` 4, `UInt64`/`Nat` 8), one after another (the field order of `Bytes (α × β)` in
  `Spec/Encode.lean`; `Nat` fixed 8 bytes mod `2^64`, not `encNat`); `storeC_exec`, `entry_bytes`. `frontx_entry g`
  adds `g.comps`, `g.enc`; `frontx_implements_bytes g` gives
  `Implements1With (fun xs => xs.data.toList) g.enc g.code g space` through `implements1_bytes` (`Impl1.lean`).
- **`%`, `/` by a literal or a named constant** (`MOD_ADLER` is unfolded): `2^k` → mask / shift (lemmas on `rN`,
  generated per constant); otherwise one conditional subtraction (`x < c ? x : x - c`, `x / c` as `x < c ? 0 : 1`), which
  needs `x < 2 c`: checked at translation time by `omega`, else a loud error naming the missing bound. No division
  routine for unbounded arguments.
- `UInt8/32/64.ofNat`, `UInt32 <<<` (`r32_shl`, the G1 gap of the lean-zip survey), `Nat >>>` (`rN_shr`); projections of
  constructor terms (`{ large := b }.1`); `match` on a constructor (an inlined helper applied to `none`) is reduced;
  `frontx_u8_facts` also gives `UInt16/32/64.toNat` bounds.
- `oblig` tries `with_reducible rfl` first and the full `rfl` last: a failing `rfl` on `UInt32` terms took 6 s (`pack`).

Not done / why: lean-zip-common `BitReader` (`readBit`, `readBits`, `alignToByte`, `readUInt16LE`): the structure has a
`ByteArray` field (a block inside a structure parameter, and a structure result containing the array) and the results are
`Except String (UInt32 × BitReader)` (a `String` error payload); `alignToByte` alone needs the `ByteArray`-field
structure. `Crc32.Native` needs a constant table. Book: `Prod.switch` has no body in the book (an exercise), `unzip`/`zip`
are lists of pairs (needs output of several lists), the `Point` examples are `Float`. `addPoints` on `u16` inputs needs 17
slots (> 16 of `compBFO`): the entry reads bytes instead.

## 15. Non-tail recursion with real calls (`frontx_rec`, branch `calls-impl1`)

Route: the PLAIN `MachineC` path (`Compiler/CStmt.lean` `compC`, `compP`), not the optimised `compBFO`: the
optimiser's register allocation has no notion of calls, so extending it is far more work; on the plain path the
call proof (`execC_ok`, `compP_ok`) already existed and only the `Implements1` bridge was missing.

| what | where | axioms |
|---|---|---|
| `implements1_of_cexec`: `CExec P need (res := main())` writing the result bytes ⇒ `Implements1With` of `callsCode1 P` (blocks `a0` input, `a3` output, stack = work block below `sp`), `space n = need n + 24` | `Riscv/Back/CallsImpl1.lean` | the standard 77 |
| `rec_ok`: the schema `f a = if go a then comb a (f c₀ a) … (f c_{m-1} a) else comb a 0 … 0` as a `CStmt` function `recFn` (pieces `GO`, `ARG j k`, `COMB`; locals: parameters, call results, argument staging); by strong induction on `μ`, a call runs in `frame · (μ a + 1)` bytes of stack | `Compiler/Rec.lean` | 3 |
| `piece_lift`, `implements1_rec` (entry `main := v4 := f(args); store bytes`, `space n = need n + 32`) | `Riscv/Frontx/Rec.lean` | 77 |
| `frontx_rec f [from eq] measure μ`, `frontx_rec_entry g [from eq]` | `Riscv/Frontx/RecCmd.lean` | – |
| `nonTailSumRec`, `nonTailLengthRec`, `fibLen` `.implements1` | `Riscv/Frontx/RecExamples.lean` | 77 |

`frontx_rec`: the equation must be an `if`/`dite` tree; each leaf has no recursive call or all of them (`f cⱼ`,
arguments closed over the parameters, a byte array passed unchanged). Generated: the pieces `f.rec.go` (Bool: the
leaf calls), `f.rec.a{j}_{k}` (argument components) and `f.rec.comb` (calls replaced by `r`s), each compiled by
the existing translator with its variables from `S = 8 + 2p + m` on (new optional `start`/`noBound` arguments of
`compileCmd`; the `r`s of `comb` carry no `< 2^64` bound, results are mod `2^64`), `f.rec.combEq` (`split <;>
simp_all`), and the four hypotheses of `rec_ok` (copies into the piece's parameters, `piece_lift`, the pieces'
`exec`). Tail calls are not touched: functions without non-tail calls keep the loop route. The stack bound comes
from the measure: `frame · (μ(entry args) + 1)`; the entry checks `μ(entry args) ≤ |xs|` (`omega`), so
`space n = 8 (N + 1) (n + 1) + 32` (N locals ≤ 16). Well-formedness (`g.wf`) is `wf_calls` (simp evaluation).

Results (book text verbatim, through `frontx_view`; no accumulator; tests `frontx_test.py check 50` on QEMU + Sail
against executed Lean, work block exactly `space n`, every Sail write in the result bytes or the work block):

| entry point | function | words | locals / frame | space | test |
|---|---|---|---|---|---|
| `nonTailSumRec` | `NonTail.sum` (9) | 333 | 10 / 88 B | `88 (n+1) + 32` | 50 cases, lengths ≤ 2769 |
| `nonTailLengthRec` | `NonTail.length` (9) | 326 | 9 / 80 B | `80 (n+1) + 32` | 50 cases, lengths ≤ 2769 |
| `fibLen` | `fib n = if n < 2 then n else fib (n-1) + fib (n-2)` (not in the book; two calls) of the input length | 411 | 11 / 96 B | `96 (n+1) + 32` | 50 cases, n ≤ 16 |

Speed (RV64, `minstret` under `qemu -icount`, one call; C = `riscv64-linux-gnu-gcc -march=rv64i -O2`):
`NonTail.sum` n = 1000: 140 271 instructions (140 per element) vs 4 008 (gcc turns the recursion into a loop:
35x); `fib 20`: 3 371 341 vs 225 885 (15x; ~154 instructions per call). Code: 333 / 411 words vs 11 / ~290
(gcc unrolls `fib`). The cost is the plain back end (every variable in a stack slot) plus four whole frontx
programs per activation (each with its own `fl` loop).

Not done:
- `times` without `plus_eq`: `times n (k+1) = plus n (times n k)` passes the recursive result as `plus`'s matched
  argument, which must be exact (`< 2^64`); that is a fact about `times` (e.g. `times n k = n * k`), which nothing
  generated provides (the call itself is not the obstacle). Also its `match k with | k'+1` binds the call argument
  to a pattern variable (`frontx_rec` needs arguments in the parameters, e.g. via a `from` equation).
- `NonTail.reverse` (`reverse xs ++ [x]`): needs list results in the schema (the call writes into the output block
  and returns its end index; `rec_ok` keeps the heap fixed, the heap would have to be threaded through the calls
  and `comb`, plus `wrO` composition and capacity obligations). Not built.
- Match patterns with pattern variables in call arguments (`| n+2 => fib n + fib (n+1)`), leaves with a subset of
  the calls, `Bool` results (`0` as the "no call" value), list/byte-array arguments other than the view's block.

Speed numbers: `python3 Testing/asm/rec-bench/bench.py 1000 20`.

Reproduce: `lake build Riscv.Frontx.RecExamples`; `lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean`;
`python3 Testing/asm/frontx_test.py check 50 nontailsumrec` (also `nontaillengthrec`, `fiblen`; note the Sail
memory trace is ~150–320 MB per run).

## 16. Round 7: `Except` / `Option` with payloads, `do` / `bind` / `throw`, `ByteArray` fields (branch `feat-except`)

Files: `Riscv/Frontx/Exc.lean` (once: `r16`, the component functions, the `bind` lemmas), `ExceptExamples.lean`
(lean-zip-common `BitReader`, lean-zip `readBitsFast`), `ExceptBook.lean` (fp-lean chapter 5); additions in
`Translate.lean`, `Tree.lean`, `Fast.lean`.

**Encoding.** A result `Except ε α` is `excTag r` (1 byte: `1` = `ok`, `0` = `error`: Sum's `inr`/`inl` of
`Spec/Ty.lean` for `Except ε α ≅ ε ⊕ α`) followed by the components of `α` in the fixed-width layout of §14 (`UInt8`/`Bool` 1,
`UInt16` 2, `UInt32` 4, `Nat`/`UInt64` 8 bytes, fields in order), all `0` on `error`; **the error value is dropped**
(an `Except String α` result says only "error"). `Option α` the same (`Option.isSome`, zeros on `none`; the tag is
`Spec/Encode.lean`'s `Option` tag; `Option UInt8` keeps its §12.2 word). A `ByteArray` field of a structure is not
written: it is the input block (read-only). So `readBit : Except String (UInt32 × BitReader)` is 21 bytes
`[tag, bit (4), pos (8), bitOff (8)]`. Encoding the message bytes was not done: results are fixed-width (`encC`).

**Compiled verbatim, machine theorem + test** (QEMU + Sail vs executed Lean, 50 cases each, all ok):

| function | source | entry | slots / words |
|---|---|---|---|
| `BitReader.readBit` | lean-zip-common @6b7d018 `ZipCommon/BitReader.lean:17` | `readBitE` (`pos`, `bitOff` from byte 0) | 11 / 156 |
| `BitReader.readBits` (+ `go`, `do`/`←`) | `:29` | `readBitsE` (`⟨xs,1,3⟩ 20`), `readBits2E` (`⟨xs,0,0⟩ 25`) | 15 / 245 |
| `BitReader.alignToByte` | `:39` | `alignE` | 4 / 96 |
| `BitReader.readUInt16LE` | `:44` | `readUInt16LEE`, `readUInt16LE5E` (`bitOff` 0 / 5) | 10 / 128, 130 |
| `Zip.Native.readBitsFast` (+ `go`) | lean-zip @7e10583 `Zip/Native/Inflate.lean:28` | `readBitsFastE` (`⟨xs,1,3⟩ 20`; same bytes as `readBitsE` on all cases) | 15 / 245 |
| `Monads.Option.firstThird`, `M.firstThird`, `M.ExplicitParens.firstThird`, `M.firstThirdInfix` | fp-lean @0abeea5 `Monads.lean:25-127` | `opt…FirstThirdE` | 11 / 76 |
| `Monads.Err.first`, `firstThird`, `AndThen.firstThird'`, `WithInfix.firstThird` (`get`, `andThen`, `~~>`, `ok` inlined) | `Monads.lean:166-292` | `err…E` | 3 / 46, 11 / 76 |
| `readAligned` (this repo: `if … then throw …` in `do`) | – | `readAlignedE` | 14 / 182 |

Source level only (`exec`, 3 axioms): `firstThirdFifth` (19 slots), `firstThirdFifthSeventh` (27) in `Option`,
`Option.M`, `Err`, `Err.WithInfix`: over the 16 slots of `compBFO` (one nested test per list element).
Human input: `readBit requires br.bitOff < 8` (lean-zip-common's own `hbo`), `readBits.go with br.bitOff < 8 ∧
shift + k < 2^64` (no overflow of `shift + 1`), `readBitsFast.go` the same, `readUInt16LE requires br.pos + 3 < 2^64`
(no overflow of `pos + 1 + 2`). The `readBits` → `go` wrapper is the entry's `rfl` equation (`frontx_entry … from`).

What was added:
- `resultComps`: `Except ε α` / `Option α` with compound payloads (`excTag`/`excGet π 0`, `isSome`/`optGet π 0`);
  `ByteArray` fields skipped; `projNorm` reduces them on constructors.
- **Normalised equation** (`normEq`, for `Except` / `Option` results and structures with a `ByteArray` field): `simp`
  (so it is proved) unfolds the non-recursive helpers that are bound, projected or return `Except`/`Option`, pushes
  `bind` into `if`s (`exc_bind_ite`, `ok a >>= f = f a`, `error e >>= f = error e`, `throw`, `pure`), projections
  into `if`s (`apply_ite`), and a `match` on a `Nat` parameter becomes `if n = 0 … else … (n - 1)`; compiled via
  `from fn.eqx measure` (the structural argument, or `0`).
- Structure parameters with a `ByteArray` field: the field is block 0 (`Rep`: `heap = [blk br.data]`, `env 1 = size`),
  checked unchanged in recursive calls; fields the body never reads get no variable (`f.dropped`, read by
  `frontx_entry`); entries take `⟨xs, c₁, c₂⟩` arguments.
- `UInt16` (`r16` lemmas), `UInt8 >>>`; compound `Nat` sides of `==`, `=`, `≠` and indices with `if`/`%`/`/` go to
  temporaries.
- **No call temporaries when a call leaf can be assigned in order**: the pairs are reordered (`seqOKm`) and
  `Tree.wf` asks `seqOK as ∨ |as| ≤ K` (`Tree.lean`, `Fast.lean` adapted), `K` counts only the other leaves. This
  brought `go` from 20 to 15 slots; all older entry points lost words (re-emitted, all tests ok).
- `frontx_view` unfolds a helper at the head whose body is a `match` (`andThen`, `get`).

Not done / why: error messages as bytes (fixed-width results); calls to a translated function with several result
components (`callInfo` takes one result word; the callee range would not fit in 24 variables anyway), so a non-tail
`readBits` use inside another function is not possible; `Err.get` / `Eff.get` (`xs[i]?` at a variable index on a view);
`Monads.Option.first` (`xs[0]?` is not a `match`; same as `head?`); `readBytes` (`ByteArray` result, `extract`).

Reproduce: `lake build Frontx`; `lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean`;
`bash Testing/scripts/frontx_tests.sh`; axioms: `Testing/scripts/axioms_s.lean`.

## 17. User inductives with payload as cells in memory (branch `feat-inductive`)

Files: `Compiler/Ind.lean` (values, programs, the compiler), `Compiler/IndOk.lean` (expressions, `F`),
`Compiler/IndDec.lean` (decoder, encoder), `Compiler/IndMain.lean` (`ind_ok`, the whole program), all source level,
3 axioms; `Riscv/Back/CallsImpl1W.lean` (`implements1_of_cexecW`: the `MachineC` bridge of §15 with a word block at the
bottom of the work block), `Riscv/Frontx/Ind.lean` (`implements1_ind`), `Riscv/Frontx/IndCmd.lean` (the commands),
`Riscv/Frontx/IndExamples.lean` (targets). Plain back end `compP` with real calls (as §15), not the optimiser.

**Representation.** A value is a tree of 4-word cells `[tag, x, l, r]` (`C.c t x l r`: constructor index, one
scalar word, two child pointers) in word block 0 = the bottom of the work block, bump-allocated (global `v5`) from word
4; cell 0 is `[255, 0, 0, 0]` = `z` (absent child, pointer 0). Children are allocated before parents, so a pointer
bounds the depth (`Rp.depth`) and cells are never written again (`Agree`, `Rp.mono`). A user type maps into `C`
(`T.emb`, generated): per constructor at most two fields of the type (`l`, `r`) and one `Nat`/`UInt64`/`Bool` (`x`);
other fields are dropped (e.g. `Level.param`'s `Name`). **Byte format** (`C.enc T.sh`, stated, prefix): tag byte, then
the constructor's fields in declaration order, `x` 8 bytes little-endian mod `2^64`; two inputs one after the other.
The program decodes the input into cells (`dec`, recursive descent with a cursor), runs `F`, and encodes a tree result
back (`enc`, length in `a1`) or stores a word result (`Nat` 8 bytes mod `2^64`, `Bool` 1 byte).

**Space** (`Proven.Frontx.Ind.space M n`): `wn = 8 + 4 (M + 1) n` words of cells (decoding allocates at most one cell
per input byte; `F` at most `M` per node, `M` = constructors per arm, arms calling each child at most once, `al_le`),
then the stack `56 + 136 (1 + n + wn)` (frames of 136 bytes, depth ≤ nodes ≤ n for `dec`/`F`, ≤ cells for `enc`):
`1368 + 712 n` bytes for word results, `1368 + 1288 n` for one constructor per node. Loose but from the input length.

**Programs.** `E rk k` (kind-indexed: word / tree): fields, the parameters `a` (word) and `b` (tree), literals, `bin`,
`mk` (allocate), `call ch a b` (recursion on a child). `Pg.sem`/`Pg.al` are the meaning and the allocation count.
`F`'s body is a loop over the arm of the current tag: an arm that is a call is a TAIL CALL (the loop continues on the
child: `Tail.sum`, `Tail.reverse`, `levelHasParam`'s `succ`), other calls are real calls (`count`, `mirror`).
`ind_ok` (once): for well-formed inputs, `main` writes the bytes of `pg.sem v₁ a0 b`.

**Commands.** `frontx_ind_type T := ty` generates the shape, `T.emb`, `T.emb_wf`, fold lemmas, `T.enc`, `T.enc2`.
`frontx_ind f on T` reads the arms off `f`'s equations (one per constructor; or `f xs = g lit xs` / `g [] xs` for an
entry), generates `f.ind.pg`, `f.ind.sem` (by induction, `simp`), `f.ind.wf` (`wf_calls`), `f.code`, `f.implements1`.

**Compiled verbatim, machine theorem (77 axioms) + test** (`frontx_test.py check 50`, QEMU + Sail vs executed Lean):

| function | source | words | test entry |
|---|---|---|---|
| `BinTree.count` | fp-lean @0abeea5 `Induction.lean:318` (type `Classes.lean:1255`) | 1124 | `bt_count` |
| `BinTree.mirror` | `Monads/Conveniences.lean:53` | 1123 | `bt_mirror` |
| `BinTree.graftLeft` (two inputs) | `Induction.lean:516` | 1022 | `bt_graftleft` |
| `Pos.toNat` | `Classes.lean:232` (type `:122`) | 712 | `pos_tonat` |
| `Pos.plus` (two inputs) | `Classes.lean:181` | 727 | `pos_plus` |
| `NonTail.sum` (`List Nat`) | `ProgramsProofs/TCO.lean:6` | 1054 | `nontail_sum_ln` |
| `Tail.sum` → `Tail.sumHelper` (loop) | `TCO.lean:40-45` | 1024 | `tail_sum_ln` |
| `Tail.reverse` → `Tail.reverseHelper` (loop, allocates) | `TCO.lean:102-107` | 1027 | `tail_reverse_ln` |
| `List.append` (two inputs) | Lean 4.29 core `Init/Prelude.lean` | 996 | `list_append_ln` |
| `levelHasParam` | con-leche @6810492 `Kernel/Expr.lean:187` (types `Kernel/Name.lean:28`, `Kernel/Expr.lean:38`) | 912 | `level_hasparam` |
| `Level.isNeverZero` | `Kernel/Level.lean:55` | 834 | `level_isneverzero` |

Human input: none (no invariants, no closed forms); entry glue: none (the theorems are about the functions themselves,
`fun t => f t`, `fun p => f p.1 p.2`).

Not done / why: `Pos.mul` (calls `Pos.plus`: one function per program), `eqBinTree` (match on two trees),
`hashBinTree` / computed `hashData` (`mixHash` is opaque), `Level.combining`/`simplify` (overlapping patterns, `=` on
levels, calls to another function), `BinTree` insert/`number` (comparisons, `ite`, state monads: no `ite` in `E` yet),
`NonTail.reverse` (`++` of a call result: another function), payloads other than one scalar (`Name`, `String`, pairs).
Codes are big (700–1100 words: the plain back end, four functions with stack frames) and slow (every variable in a slot).

Reproduce: `lake build Riscv.Frontx.IndExamples`; `lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean`;
`bash Testing/scripts/frontx_tests.sh`; axioms: `Testing/scripts/axioms_t.lean`.

## 18. More than 16 slots (branch `more-slots`)

The 16-slot limit of `compBFO` is gone: `NS = 254` and `optB` only asks that locals `j ≥ 24` be spilled (back end:
`Testing/notes/OPT.md`, "More than 16 locals"). `implements1_listW` / `_bytesW` / `_resW` (`Impl1.lean`) take
`N ≤ NS`; the `frontx_implements*` macros use them; the `N ≤ 16` theorems stay, as wrappers. Entry points with
`Implements1` theorems now (verbatim book / repo code; QEMU + Sail vs executed Lean, `frontx_test.py check 50`, all ok):

| function | entry | slots / words |
|---|---|---|
| `Monads.Option.firstThirdFifth`, `Monads.Err.firstThirdFifth` | `optFirstThirdFifthE`, `errFirstThirdFifthE` | 19 / 109 |
| `Monads.Option.firstThirdFifthSeventh`, `Option.M.…`, `Err.…`, `Err.WithInfix.…` | `opt…`, `optM…`, `err…`, `errInfix…FirstThirdFifthSeventhE` | 27 / 235 |
| `addPoints` (`DataExamples`) on four 16-bit inputs | `addPoints16E` | 17 / 197 (95 cases) |
| `tinyCompile` (`TinySelf.lean`, from branch `tinyself`) | `tinyCompile` | 17 / 305 |

`tinyCompile`: its plain fallback is not well-formed (`wf` false: loops of 1166 and 1064 plain words, over the 1024 of
`beqz`); that is also why the earlier 19-slot binary hung on QEMU and Sail (the fallback words were used and the loop
branch offset was out of range). New `frontx_implements_listC g` (`Checked.lean`): at elaboration `pickC` finds the
register choice (table + spilled locals), `g.code := compBFC …` keeps only the optimised words, and
`implements1_listC` needs `optB` to accept that choice (`decide +kernel`, ~30 s) instead of `wf`. Self-hosting data
point: `Testing/asm/tiny/selfhost_test.py` runs the `tinyCompile` binary on QEMU on the 5 tiny programs (code ==
Lean's `tinyCompile`) and runs each code it produced on `qemu-riscv64` on 17 inputs: 85 / 85 == Lean `tinyRun`.

Not done: lean-svg `findSeq` → `startsWith` (blocked by the front end, not the slots any more: the call to
`startsWith`, a loop with a `String` block, is not a supported call, "frontx: unsupported Bool"). Code quality over 16
slots: the prologue still zeroes every slot, and locals `≥ 24` are always spilled (no renumbering by use).
Reproduce: `lake build Frontx`; `lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean`;
`lake env lean --tstack=400000 Testing/asm/emit_tiny.lean`; `bash Testing/scripts/frontx_tests.sh`;
`python3 Testing/asm/tiny/selfhost_test.py`; axioms `Testing/scripts/axioms_u.lean`.

## 19. Scalars and conditionals (branch `feat-scalars`)

Files: `Compiler/Ind.lean`, `IndOk.lean`, `IndMain.lean` (`E.ite`, once), `Riscv/Frontx/Ind.lean` (comparison lemmas),
`Riscv/Frontx/IndCmd.lean` (front end), `Riscv/Frontx/IndCmpExamples.lean` (targets, user inductives),
`Riscv/Frontx/Translate.lean`, `Rep.lean` (list front end: `UInt64` shifts, `*`/`/`/`%` by powers of two, `min`/`max`),
`Riscv/Frontx/ScalarExamples.lean` (targets, fixed-width words), `Testing/asm/ind-bench/` (speed), axioms
`Testing/scripts/axioms_v.lean`.

**`if` in the inductive path.** `E` (`Compiler/Ind.lean`) has a new constructor `ite (c : E rk .w) (e₁ e₂ : E rk k)`:
`ev` evaluates only the chosen branch, `alE` counts only its cells, `E.calls`/`E.mks` take the `max` of the branches
(so `Pg.lin`, "each child called at most once per arm", still bounds the cells: `alE_le`), `comp` evaluates `c` into a
temporary, then a `CStmt.ite`. Proved once: the `ite` case of `comp_ok` (`IndOk.lean`) and of `alE_le` (`IndMain.lean`);
`ind_ok`'s statement is unchanged. Comparisons are the existing `Op`s (`ult`, `eq`, `xor 1` for `¬`, `and`, `or`).
A call in a branch is a real call (the stack bound `136 · depth` already covers it); only a whole arm that is a call
is a loop (see "not done").

**Front end** (`IndCmd.lean`): `if`/`ite`, `cond`, `decide`, `<`, `≤`, `>`, `≥`, `=`, `≠`, `==`, `!=`, `¬`, `∧`, `∨`,
`&&`, `||`, `!`, and a `match` on a `Bool` (`List.elem`'s `match a == b with | true => … | false => …`: reduced per
constructor). Comparisons on `Nat`, `UInt64`, `Bool`; `UInt64` `+ - &&& ||| ^^^` (wrap like the word). A function
with overlapping patterns (`| _ => false`, the equations carry hypotheses) is read from its unfolding equation with
the argument replaced by each constructor and the `match` reduced (`armsOfCases`): enumerations with wildcards.
A constructor may now fill a dropped field (not in the byte format, e.g. a `Unit` value), and a `Unit` parameter
is allowed (`Tree.insert t k ()`).

**Theorem shape for comparisons (range hypothesis, owner's way (1)).** A `Nat` field is stored mod `2^64`, which
commutes with `+` but not with `<`/`=`. `frontx_ind_type T := ty` now also generates `T.small : ty → Prop` (every `Nat`
field `< 2^64`, by structural recursion). When an arm compares `Nat`s, the generated theorems carry it:
`f.ind.sem : ∀ t a b, T.small t → a < 2^64 → [T.small b →] pg.sem (T.emb t) (ofNat a) … = …` and the machine
theorem takes its input in the subtype:

    insert5.implements1 : Implements1With (fun g => TU.enc g.val) TU.enc insert5.code
      (fun g : {g : Tree Unit // TU.small g} => insert5 g.val) (Ind.space insert5.ind.pg.M) (2 ^ 20) true

(two inputs: `{g // T.small g.1 ∧ T.small g.2}`). Functions comparing only `UInt64`/`Bool`/tags keep the plain
statement. The sem proof: unfold, `nat_ult`/`nat_eq` (`Riscv/Frontx/Ind.lean`, side conditions by `omega` from
`T.small`), `bw_eq0`, `split`, `simp_all`.

**Compiled verbatim, inductive path** (`frontx_ind`; machine theorem with the standard 77 axioms, `sem` 3; tests
`frontx_test.py check 50`, QEMU + Sail against executed Lean; trees built by the library's own `insert`, keys small
(5 often present) and near `2^64`; enumerations: every value, every pair, repeated to 50 cases):

| function | source | entry | words | test |
|---|---|---|---|---|
| `Tree.contains` | Lean 4 v4.29.0 `doc/examples/bintree.lean:26` (type `:18`; `β := Unit`) | `contains5 t = t.contains 5` | 1003 | `tree_contains5` |
| `Tree.insert` | `doc/examples/bintree.lean:54` | `insert5 t = t.insert 5 ()` | 1462 | `tree_insert5` |
| `List.elem` | core `Init/Data/List/Basic.lean:785` | `elem5 xs = List.elem 5 xs` | 928 | `list_elem5` |
| `List.erase` | core `Init/Data/List/Basic.lean:1511` | `erase5 xs = xs.erase 5` | 1081 | `list_erase5` |
| `Weekday.isWeekend` (A and B) | fp-lean @0abeea5 `Monads/Conveniences.lean:85,94` (type `:71`) | the function | 710, 710 | `weekday_isweekend_a/b` |
| `Ordering.swap`, `then` (two inputs), `isLE`, `isEq` | core `Init/Data/Ord/Basic.lean:45,100,123,107` | the function | 769, 702, 540, 538 | `ordering_*` |

Human input: none; entry glue: the literal key (`frontx_ind`'s scalar argument must be an entry literal).

**List front end (`frontx_compile`)**: `if`, `<`, `≤`, `=`, `≠`, `==`, `&&`, `||`, `!` on `Nat`/`UIntN` were already
there (sections 9–16). New: `UInt64` `<<<`/`>>>` (`r64_shl`/`r64_shr`: before, `x <<< 16` on a `UInt64` timed out in
`rfl`), `UInt64` `x * 2^k`, `2^k * x`, `x / 2^k`, `x % 2^k` as shifts / a mask (`r64_mulPow`, `r64_divPow`,
`r64_modPow`, per constant a one-line instance), `min`/`max` on `Nat` (`Nat.min_def`). Compiled verbatim (con-leche
@6810492 `ConLeche/Kernel/Expr.lean`, the packed `Expr` data word), each with `g.implements1` (77 axioms) and
`frontx_test.py` on 61 cases (the saturation edges `32766/32767/32768`, `0`, `2^32`, `2^63`, `2^64 - 1`, then the
random inputs):

| function | source line | entry (input) | words |
|---|---|---|---|
| `hashOfData` (`w / 4294967296`) | 251 | `hashOfDataE` (word at 0) | 106 |
| `bvarOfData` (`w / 65536 % 32768`) | 254 | `bvarOfDataE` | 109 |
| `fvarOfData` (`w / 2 % 32768`) | 257 | `fvarOfDataE` | 109 |
| `lpOfData` (`w % 2 == 1`) | 260 | `lpOfDataE` | 87 |
| `hash32` (`w % 4294967296`) | 263 | `hash32E` | 109 |
| `satPred` (`if x == 32767 … else x - 1`) | 271 | `satPredE` | 113 |
| `satSucc` (`UInt64.ofNat (min (n + 1) satRange)`) | 266 | `satSuccE` (16-bit `n`) | 81 |
| `packData` (`h * 4294967296 + b * 65536 + f * 2 + if lp …`) | 247 | `packDataE` (bytes 0–3) | 106 |

Entry glue: `rdLE` (a loop reading `k` little-endian bytes, called as a sub-program) and the byte readers of
`BookExamples`. `packDataE` reads its three words as single bytes (three `rdLE` calls need 22 slots; the word
readers above exercise the full range).

**Speed** (`python3 Testing/asm/ind-bench/bench.py`: one call, `minstret` under `qemu -icount`, bytes in → bytes out
on both sides; C = `ind-bench/ind.c`, `riscv64-linux-gnu-gcc -march=rv64i -O2`, decoding into nodes, running the same
algorithm (persistent insert / erase), encoding):

| entry | input | ours | gcc -O2 | ratio |
|---|---|---|---|---|
| `tree_contains5` | balanced BST, 255 keys (2551 bytes) | 108 864 | 27 631 | 3.9 |
| `tree_insert5` | same | 203 747 | 44 776 | 4.6 |
| `list_elem5` | 201 elements, 5 last (1810 bytes) | 89 707 | 14 716 | 6.1 |
| `list_erase5` | same | 158 793 | 27 936 | 5.7 |
| `satPredE` / `bvarOfDataE` / `packDataE` | one word | 171 / 170 / 104 | 111 / 108 / 65 | 1.5 / 1.6 / 1.6 |

Most of the inductive-path cost is decoding/encoding through the plain back end (every variable in a stack slot,
four functions with frames); the scalar entries go through the optimiser (`compBFO`).

**Not done / why:**
- var × var `*`, `/`, `%` (RISC-V M): `Op` (`Spec/Code.lean`) has no multiply/divide, so it needs a new `Op`, its
  code in every back end and the register allocator, and per-instruction lemmas on the Sail model. Checked the model
  (`LeanRV64D/InstsEnd.lean`): `execute_MUL` is `mult_to_bits_half` (low part = `a * b` mod `2^64`); `execute_DIV`
  unsigned by zero gives `-1` (all ones) where Lean's `x / 0 = 0`, so `/` needs a guard (`if b = 0 then 0 else divu`);
  `execute_REM` unsigned by zero gives `rs1`, which is Lean's `x % 0 = x`. Not started.
- `Int` scalars, `BitVec w` for `w ≠ 64`, `UInt8/16/32` fields in the inductive path (only `Nat`/`UInt64`/`Bool`).
- enumerations as fields or as a `match` inside an arm other than `Bool` (`match compare a b with | .lt …`, fp-lean's
  `merge`): `reifyMatch` handles `Bool` only; an enum-valued field would need its own scalar kind.
- a call in an `ite` branch is a real call, not a loop (`contains`, `elem` recurse in both branches of the test):
  making `arm` recurse through `ite`s needs `loop_ok`'s arm case generalised over the branch; not done (would mostly
  remove a frame per level).
- fp-lean @0abeea5 has no binary-search-tree `insert` (searched `examples/` and `book/`): the Lean 4 doc example is
  used instead. `Tree.find?` (`Option β` result) and a key from the input (the scalar argument is an entry literal)
  are not supported.
- the generic `frontx_compile` path fails on `(u16 xs i).toUInt64` (a compound `Nat` under `Nat.toUInt64`): the
  entry points read words with `rdLE` instead.

Reproduce: `lake build Frontx`; `lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean`;
`bash Testing/scripts/frontx_tests.sh`; `python3 Testing/asm/ind-bench/bench.py`.

Statement fingerprints: `ind_ok` and the eleven section-17 `implements1` theorems keep their `stmt` hashes; only their
closures changed (`E` gained `ite`). Not re-frozen here (left to the owner: `statement_check.sh --freeze`); the new
theorems are not in the fingerprint list yet. `check.sh`: ALL CHECKS PASSED (with that warning).

## 20. Word arrays, tables, mutable arrays (branch `feat-arrays`)

A separate, reflective front end for programs over arrays, with its own compiler to the middle layer
(`Proven.Mach.BStmt`, which already had word blocks: `load64`/`store64`) and the optimised back end `compBFO`.
Files (all new, `Riscv/Frontx/Wa*.lean`, lake lib `Frontx`): `WaLang` (language, meaning, `Runs`, `runs_of`),
`WaComp` (locations, representation `Rel`/`SR`/`AR`, operation lemmas `mop_ok`/`mcmp_ok`/`mcast_ok`), `WaExp`
(expressions, `E.comp_ok`), `WaUpd` (in-place updates, `A.pre_ok`/`A.st_ok`), `WaStmt` (loop bodies `T.comp_ok`, loops:
`comp_loop`, `fast_loop`, `loopCode_ok`), `WaPg` (fresh arrays, programs, `Pg.comp_ok`), `WaImpl` (bridges
`implements1_wa` scalar result / `implements1_waA` array result), `WaCmd` (`wa_compile`), `WaLeanZip` (targets).
Tests: `Testing/asm/emit_wa.lean` → `frontx-words/wa_*`, run by `frontx_tests.sh` (header `wa A N B L`, see
`frontx_test.py`); axioms: `Testing/scripts/wa_check.sh` (`axioms_wa.lean`); speed: `Testing/asm/wa-bench/`.

**Language** (`WaLang.lean`). Typed syntax over an environment of slots `Sl` = scalar (`UInt8/16/32/64`, `Nat`,
`Bool`) or array (`ByteArray`, `Array t`); variables are typed de Bruijn indices `Mem Γ s`; values `Vals Γ` are nested
pairs. `E` (scalars: `+ - * / % &&& ||| ^^^ <<< >>>`, `== != < ≤`, `&& || !`, casts `toNat`/`ofNat`/`toUIntN`, `if`,
`a[i]!` / `a[i]'h`, `a.size`), `A` (in-place updates `set!`, `push`, `if`), `F` (fresh arrays: `Array.replicate`,
a constant table, `xs.data`, alias), `T` (loop bodies: `if`, `let`, `call` = next state, `ret`), `Pg` (stages: `let`,
loop, result). The meaning `den` is written with the very operations library code uses (per type, explicit instances),
so a reflected Lean term equals the meaning of its syntax after `simp` unfolds `den` (no restatement). Loops are
relational (`Runs`); `runs_of` turns "`g s = body.den s g` plus a measure and an invariant" into `Runs`.

**Compiler and proof** (once, source level, `propext`/`Classical.choice`/`Quot.sound`). Locations: a scalar is a
variable; an array is a size variable plus its elements: the input block (bytes, read only) or words `off ..` of the
work block (`wheap[0]`, one 64-bit word per element, `cap` words). Expressions → three-address statements (a pure
shallow expression is one assignment, `toB`/`pureOr`); `a[i]!` is a guarded load (`0` out of range, as `getElem!`),
`a[i]'h` a plain load whose bound is an obligation. Constant tables are stored word by word before use (`tblStores`),
`Array.replicate` is a fill loop. A loop `if c then (calls) else (results)` compiles to `t := c; while t { …; t := c }`
(`fast_loop`), any other body to `fl := 1; while fl { body }`. At a `call` leaf the scalar components go through
temporaries; at most one array component changes: its update evaluates all indices and values in the old state
(`A.pre`), then stores (`A.st`; `set!` re-checks `i < size` at run time). The frame of a loop is "work words outside the
written slot unchanged" (`WO`, `Loc.sep`), checked statically by `Pg.wf` (`decide +kernel`).
Run-time conditions are an `ok` predicate per expression (`Nat` operands of non-homomorphic operations `< 2^64`, plain
loads in range); a program's meaning together with them is `Pg.Good` (per loop: an invariant `P` and the `Runs`).

**`wa_compile f [invariant P measure μ]*`** (`WaCmd.lean`, untrusted). For `f : ByteArray → β` (β scalar or array):
unfolds non-recursive helpers (arguments become `let`s, `letBeta`, for sharing), hoists constant tables and `xs.data` to
the front (restart on demand), turns `Array.foldl g init arr` into a loop over `(acc, i)` (`foldGo`, `foldl_foldGo`;
invariant `i ≤ arr.size` and measure automatic) and a call of a recursive user definition into a loop over its
arguments (body: its unfolding equation; `invariant`/`measure` given as functions of the arguments), and generates
`f.wa`, `f.good : ∀ xs, xs.size < 2^32 → f.wa.Good (xs, ()) (f xs)` (stage by stage; per loop the equation by
`rw [go]` + `simp` over `den`, the steps and side conditions by `simp` + `omega`), `f.code` and `f.implements1`.

**Compiled verbatim** (lean-zip @7e10583, `WaLeanZip.lean`; `Implements1` with the 77 Sail axioms; QEMU + Sail vs
executed Lean, 50 cases each, all ok; CRC results also = `zlib.crc32`):

| entry | library code | words | work words (A) / slots (N) | human input |
|---|---|---|---|---|
| `crc32E xs = Crc32.Native.crc32 0 xs` | `Zip/Native/Crc32.lean:14,17,22`, `Zip/Spec/Crc32.lean:25,30,78,84` (`table := Spec.mkTable`, `Array.ofFn`; `crcByteTable` with `if h : index < table.size`) | 1631 | 256 / 12 | none |
| `crcUpdateE xs = updateBytes 0xFFFFFFFF xs` | same | 1615 | 256 / 11 | none |
| `countLengthsE xs = countLengthsFast xs.data 15` (`Array Nat` result, 16 × 8 bytes, `retLen`) | `Zip/Native/Inflate.lean:536` (`Array.replicate`, `count.set! ln (count[ln]! + 1)` under `if 0 < ln ∧ ln ≤ maxBits`) | 131 | 16 / 20 | `invariant i ≤ lengths.size ∧ lengths.size < 2^32 ∧ maxBits = 15 ∧ count.size = 16`, `measure lengths.size - i` |
| `countLengths7E` (`maxBits = 7`) | same | 131 | 8 / 20 | same with 7 / 8 |

Theorem shapes: `Implements1With (fun xs => xs.data.toList) Res.enc crc32E.code crc32E (fun _ => 8 * 256 + 8 * (12 + 1) + 7)`
(constant work space: table words + frame); `Implements1With … (encArr (.arr .nat)) countLengthsE.code countLengthsE
(fun _ => 8 * 16 + 8 * (20 + 1) + 7) (retLen := true)` (`encArr`: every element `width` bytes little-endian, `Nat` mod
`2^64`; the result length is returned in `a1`; the output bound is `Implements1`'s own `|enc (f a)| ≤ output.len`).
The table is not trusted: its words are `t.rep tb[j]` computed from `Spec.mkTable` inside `decide +kernel` (wf) and at
emission; the source side reads `table[index]` through `den`.

**Speed** (`python3 Testing/asm/wa-bench/bench.py wa_crc32 crc32c 0 1000 10000`, `minstret` under `qemu -icount`,
gcc = `riscv64-linux-gnu-gcc -march=rv64i -O2` table CRC with a static table): 19.2 instructions per byte vs 11.0
(1.74×), plus 1609 once per call (storing the 256 table words; gcc's table is in `.rodata`): n = 10000: 191 609 vs
110 010; n = 1000: 20 609 vs 11 010. Remaining per-byte overhead: the verbatim `if h : index < table.size` test and
the run-time bound check of `xs.data[i]!` are kept (no interval reasoning yet), copies of the call temporaries into the
state variables, `UInt32.ofNat b.toNat` masks. Code is big (1631 words) because of the 256 unrolled stores.

**Overlap with section 19** (`feat-scalars`): this front end has its own complete scalar operation set
(`UInt8/16/32/64`, `Nat`, `Bool`: `Op2`/`Cmp`/`cast` with `mop_ok`/`mcmp_ok`/`mcast_ok`, reusing the `r8/r16/r32/r64/rN`
lemmas of `Rep.lean`/`Exc.lean`); nothing in `Translate.lean`/`Ind*.lean` was changed.

**Not done / why.**
- Growing output (`ByteArray.push`, `Array.push`, `++`) and read-while-write (`copyLoopGo`): the syntax (`A.push`,
  `F.empty`, `F.extract`) and the update phases exist, but `A.ok` rejects `push` and `F.wf` rejects `empty`/`extract`:
  missing are (1) a capacity tied to the input for a growing array (the work block would be `A + B·n` words; the push
  obligation `size < cap` needs the capacity in the source-level `Good`), (2) the copy loop of `extract`, (3) `%` / `/`
  by a variable (`k % distance`, a subtraction loop), (4) `Prop` parameters of the loop function (`copyLoopGo`'s
  `hd_pos hsd`: an invariant-guarded `g`), (5) a `ByteArray` result from the work block (bytes stored one per word:
  `outLoop` handles it with width 1). (1)–(5) are each local to `WaPg`/`WaUpd`/`WaExp`/`WaCmd`.
- `nextCodesFast` (`(code + count[bits-1]!) * 2`: `*` by a variable is not in the machine operations), `kraftSumFast`
  (`*`, `<<<` by a variable), `fillEntries` (pair result), the Huffman tables of `Inflate` (built by these).
- lean-zip's `Crc32.Native.updateBytes_eq_updateList` (table = bitwise spec) is proved with `bv_decide`; not copied, so
  no chained `Spec.checksum` corollary.
- One loop per stage reads only arrays of the input or earlier stages (a fold over an array computed by an earlier
  loop is rejected: its `g` would mention the earlier result).

Reproduce: `lake build Frontx` (WaLeanZip ~30 s); `lake env lean --tstack=400000 Testing/asm/emit_wa.lean`;
`for f in wa_crc32 wa_crcupdate wa_countlengths wa_countlengths7; do python3 Testing/asm/frontx_test.py check 50 $f; done`;
`bash Testing/scripts/wa_check.sh`.


## 21. Inductives, part 2: several functions, two-value match, Option results, input keys (branch `feat-ind2`)

Files: `Compiler/Ind.lean`, `IndOk.lean`, `IndMain.lean` (generalised, source level, 3 axioms), `Compiler/IndSup.lean`
(new: decoder, `cellsSup`), `Riscv/Back/CallsImpl1W.lean` (one more premise), `Riscv/Frontx/Ind.lean`
(`implements1_indM`, `implements1_indL`, `implements1_indS`), `Riscv/Frontx/IndCmd.lean` (front end rewritten),
`Riscv/Frontx/Ind2Examples.lean` (targets), tests and bench as before; axioms `Testing/scripts/axioms_w.lean`.

**Language** (`E`, once, proved in `comp_ok` / `loop_ok`):

| new | meaning | code |
|---|---|---|
| `ext j k et ea eb` | call of the `j`-th function after this one (result kind `k`) on any tree, word, tree | `call (fi+1+j)` |
| `me` | the current node | its pointer (`v8`) |
| `fw i e`, `ft ch e` | tag / scalar, left / right child of any tree value (`z`: `255`, `0`, `z`) | one `ld` |
| `bind e₁ e₂`, `var i k` | `let` (de Bruijn; the values in temporaries above the arm's) | `v_n := e₁` |

`Pg` gets `X` / `XA` (meaning / cell count of the later functions, default none); a program is the entry and a
list of later functions (`indProgM`: `main, dec, enc, F₀, F₁, …`), each calling only functions after it
(`Chain`: `Fᵢ.X j = semX (later) j`, checked by `rfl`), so the meaning is plain structural recursion per
function, defined function by function.  `chain_ok` (once, by induction on the list): a call of the function at
position `i` runs within `8 (nl+1) (|W|+1) · (m - i)` bytes of stack (`XOK`, the call's contract: the heap
grows, the cells below stay, the result relates to `semX`).  `loop_ok` takes the later functions' `XOK` as a
hypothesis; `ind_okM` the whole program.  The old `ind_ok` / `implements1_ind` keep their statements (now
corollaries; `Pg.lin` also asks "no `ext`, `var` kinds agree").

**Space.**  One function with at most `M` cells per input node: the old linear bound (`Ind.space M`, or
`Ind.spaceA 1 16 (fun n => M * n)` with the new input/output options, `implements1_indL`).  With calls of other
functions the cells are not bounded by a fixed number per node (`Pos.mul` allocates `|n|·|k|` cells,
`NonTail.reverse` `n²/2`); there the statement is
`Ind.spaceA m nl (cellsSup sh pg bi ain a0)`: `cellsSup … n` is the largest number of cells (`Pg.al`, the
constructor applications the Lean function evaluates) over all inputs of `n` bytes (a definition over all
`256^n` byte strings and the format's decoder `C.dec`, proved inverse to `C.enc`: `dec_enc`, `al_le_cellsSup`).
No hypothesis on the size: `implements1_of_cexecW` now hands the RAM bound (`8 · words < 2^32`) to the program
proof, so a huge `cellsSup` only makes the theorem's precondition (`space ≤ work`) unsatisfiable.

**Other options of the whole program**: the word argument from the input (`ain`: 8 bytes little-endian after the
tree(s), `inBytesA`; read in `main` by `rdB`), an output format other than the input's (`shO`: e.g. `Option Unit`,
`Ordering`).

## 22. Multiply, divide, remainder, shift by a variable (branch `feat-muldiv`)

`Spec/` is untouched (`Op` stays as it is). The new operations live on the compiler side only:

- `Compiler/MOp.lean`: `MOp = mul | divu | remu` with the **hardware** meaning (`divu` by zero = all ones, `remu` by
  zero = the dividend). Middle layer: `Mach.BStmt.mop m v a b` (`v := m.eval a b`, `Compiler/BLang.lean`) and
  `Proven.BStmt.mop` (`Riscv/Direct/Arr2Code.lean`, mapped by `toMS`); optimiser IR `IR.Ins.mop` (every pass:
  selection `BSel.irB`, renaming, liveness, copy propagation, hoisting (the constant operands too), flow facts,
  lowering); wide op `WOp.mop` with the law `Wide.w_mop`. The plain back ends (`compB`, `compileB`) have no
  multiply: their `wf` is `False` for `mop`, so a program with `mop` uses the **checked words** `compBFC` (the
  register choice found by `pickC` at elaboration time, `optB` accepting it checked by `decide +kernel`; no plain
  fallback) through `implements1_of_execC`.
- RISC-V: `mul`/`divu`/`remu` = `encR 1 (0|5|7)` (`Riscv/Back/Wide.lean`), step lemmas `G.step_mul`, `G.step_divu`,
  `G.step_remu` (`Riscv/Steps/GenMul.lean`, by `gstep` on the Sail model plus `mul_low`, `divu_eq`, `remu_eq`).
  Checked in the model (`LeanRV64D/InstsEnd.lean`): `execute_MUL` = `mult_to_bits_half` low half (`= a * b`),
  `execute_DIV`/`execute_REM` unsigned with the by-zero cases above. **M extension**: no hypothesis is needed;
  `Cfg` fixes `misa = 0x800000000014112F`, bit 12 (`M`) set, and the boot path establishes `Cfg`
  (`BootReset.lean`: reset `misa` differs only in `V`, which the stub clears); the step lemmas hold in every `Cfg`
  state. `mulhu` was not needed (not added). The theorems still have exactly the 77 Sail axioms.
- Lean's `x / 0 = 0` (Nat, UIntN, BitVec): `/` is `divu` followed by a select `b = 0 ? 0 : q` (`mopS`, `mStmt`);
  `%` needs no guard. `Nat` operands of `/`, `%`, `-`, `>>>` must be `< 2 ^ 64` (run-time `ok` conditions,
  discharged from invariants / `requires`; `*`, `+`, `<<<` by an amount `< 64` are homomorphic mod `2 ^ 64` and
  need nothing). `UInt32/16/8` products are masked. `Nat` results are encoded mod `2 ^ 64` (`Res.enc`, `encArr`).

**Word arrays** (`WaLang/WaComp/WaExp`): `Op2.den` gained `* / %` on `UInt8/16/32/64` and `<<<` on `Nat`;
`Op2.isM` ops compile to `binS`/`mStmt`; `Op2.side` (`Nat` `<<<`: amount `< 64`) joined `E.ok`. `wa_compile`:
`let`s floated out of helper arguments (so `f (g xs)` with two loops works: the second loop reads the array the
first one built), core `Nat.gcd`/`Nat.lcm` allowed as code (`coreCode`), `wa_facts` (bounds of `%`, `/`,
`UInt8.toNat`, products, `gcd` for `omega`), `implements1_waC`/`implements1_waAC` (checked words) chosen when the
program has a `mop` (`MS.hasMop`).

**List front end** (`Translate.lean`): `*`, `/`, `%` on `Nat`/`UInt64`/`UInt32`/`UInt16`/`UInt8` whose literal
forms do not apply become an `Item.mop` (a `Tree.sub (mopS …)` node, `sim_sub` with `mopS_exec`), representation
lemmas per use (`MulRep.lean`, kept out of the global set: they would pre-empt the literal shift/mask forms);
`Nat` `>>>` by a variable is guarded (`≥ 64` gives `0`), `Nat` `<<< (b % 64)` works; `frontx_md_facts` in
`frontx_disch`. Machine theorems through `frontx_implementsC` (`Checked.lean`, `implements1_resC`). Trees with a
`sub` node get no fast loop (`Tree.calls`), so these loops run through the plain step.

**Compiled verbatim** (each: `Implements1With … Res.enc/encArr … code f space`, no input hypothesis beyond the
`Implements1` frame; QEMU + Sail against executed Lean and a Python reference, `frontx_test.py`; divisor 0, `2^63`,
`2^64 - 1`, Fibonacci pairs, shift amounts 31/32/63/64/65 among the cases):

| entry | library code | path | words | cases |
|---|---|---|---|---|
| `kraftE xs = kraftSumFast (countLengthsFast xs.data 15) 15` | lean-zip @7e10583 `Zip/Native/Inflate.lean:555` (+`:536`) | wa | 142 | 56 |
| `nextCodesE xs = nextCodesFast (countLengthsFast xs.data 15) 15` (`Array UInt32`) | `Zip/Native/Inflate.lean:587` (+`:536`) | wa | 189 | 56 |
| `gcdE xs = Nat.gcd (rd32 xs 0) (rd32 xs 4)` | core `Init/Data/Nat/Gcd.lean:35` | wa | 145 | 56 |
| `ops64E`/`ops32E`/`opsNE` (`a * b ^^^ a / b ^^^ a % b ^^^ a <<< b ^^^ a >>> b`, glue) | — | wa | 223/163/158 | 56 |
| `gcdE xs = Nat.gcd (u64At xs 0).toNat (u64At xs 8).toNat` | core `Init/Data/Nat/Gcd.lean:35` (`frontx_compile Nat.gcd`) | list | 182 | 53 |
| `ops64E`/`ops32E`/`opsNE` (glue, `Nat` shift `a <<< (b % 64)`) | — | list | 291/294/295 | 53 |

(`kraftSumFast`: `count[b]! * (1 <<< (maxBits - b))`, variable multiply and variable shift; `nextCodesFast`:
`(code + count[bits - 1]!) * 2`.) Human input: the loop invariants/measures in `WaMul.lean` (as for
`countLengthsFast`); none for the list path beyond `requires` bounds.

**Speed** (`python3 Testing/asm/mul-bench/bench.py`, `minstret` under `qemu -icount`, gcc =
`riscv64-linux-gnu-gcc -march=rv64im -O2`, `Testing/asm/mul-bench/mul.c`): `wa_gcd` on (F45, F46) 537 vs 206
instructions (2.6×); `wa_kraft` n = 1000: 28 661 vs 10 807, n = 10000: 281 701 vs 106 627 (2.6×; 28.2 vs 10.7 per
byte). Overhead: the plain `fl := 1; while fl` loop form and state copies (no fast loops for `mop` trees in the
list path), the guard of every `/`.

**Not done / why.**
- `Nat.lcm` (`m * n / gcd m n`): the `gcd` loop sits inside an expression; `wa_compile` takes loops only as
  stages (`let` / result). The list path would need the same.
- lean-zip `copyLoopGo` (`k % distance`): needs growing output and read-while-write (section 20, not done).
- fp-lean is not available on this machine (`/home/user/deps` has no checkout); con-leche @6810492 has no
  variable multiply/divide in executable code (only by constants, already supported).
- `Nat` `<<<` by an unbounded variable (`a <<< b` with `b ≥ 64` is not the machine's `sll`); `mulhu`, signed
  `div`/`rem`.

Reproduce: `lake build Frontx`; `lake env lean --tstack=400000 Testing/asm/emit_wa.lean`;
`lake env lean --tstack=400000 Testing/asm/emit_mul.lean`; `bash Testing/scripts/frontx_tests.sh` (or
`frontx_test.py check 56 wa_kraft` …); `bash Testing/scripts/wa_check.sh` (axioms, also the list-path entries).
Statement fingerprints: no `stmt` hash changed; 62 closures changed (the middle layer gained `mop`). Not re-frozen.

## 23. Strings and Names (branch `speed-ind`)

Scope changed by the owner (features first, speed later); the speed finding is kept at the end of this section.

**Inductive path: `String` fields, nested types, `Decidable` functions.**  Files: `Compiler/Ind.lean` (new field kind
`Fld.b`: the scalar `x` as ONE byte, `x < 256`; `C.wf` asks `Fld.b ∈ fs → x.toNat < 256`), `Compiler/IndDec.lean`,
`IndSup.lean` (decoder/encoder/`dec_enc` cases for `.b`: `.load` of one byte, `wrB 1`), `Riscv/Frontx/IndStr.lean`
(new: `Bytes8`, `Bytes8.ofString s = ofList s.toUTF8.data.toList`, `Bytes8.eqb`, `eqb_ofString : eqb (ofString s)
(ofString t) = decide (s = t)`), `Riscv/Frontx/IndCmd.lean` (front end), `Riscv/Frontx/NameExamples.lean` (targets).

- **Byte format** (superseded by section 28: a `String` is now its length, 8 bytes, then its bytes; the chain below
  is only the memory representation) (stated by `C.enc` of the generated shape): a `String` field is the chain `Bytes8.ofString s` of
  its UTF-8 bytes: per byte the tag of `cons` and the byte, then the tag of `nil` (no length prefix: it is the
  Encode-style format of `List UInt8` as an inductive, tag + fields; a `UInt8` field is one byte).  E.g. `Name.str
  .anonymous "ab"` = `01 00 04 61 04 62 03`.
- **Shapes of several types** (`frontx_ind_type T := ty nesting U₁, …`): the constructors of `ty`, then of the types
  of its fields given in `nesting` and of `Bytes8` (for `String` fields), numbered on: `LevelN := Level nesting Name`
  has tags 0-4 `Level`, 5-7 `Name`, 8-9 the bytes.  Generated per type `T`, `T.N1`, `T.N2`, …: `emb`, `small`,
  `fold`, `emb_wf`, and `off` (first tag).  A function over a nested type gets `off` empty arms below its tags.
  Without `nesting`, a field of another inductive is dropped as before (`LevelT` unchanged).
- **Front end**: `s = t`, `s ≠ t`, `s == t` on strings ↦ a call of `Bytes8.eqb` (added to the program);
  `a = b` / `decide (a = b)` on two non-constant values of a declared type ↦ a call of the function of the
  `DecidableEq` instance; a function with result `Decidable p` is a word (`isTrue` 1, `isFalse` 0; its `sem`:
  `= bw (@decide _ (g a b))`); a `match` on a `Decidable` value is a match on an enumeration (proof fields ignored);
  `if h : c then … else …` (`dite`); an entry `f a b := decide (a = b)` or `a == b` (a `BEq` instance, a definition
  that is `decide …`) unfolds to the instance's function.  `Nat` comparisons are now allowed in programs of several
  functions (a caller of a function with range hypotheses gets them too).  In shapes of several types a `match`
  tests only the constructors whose branch differs from the most frequent one (`Level.decEq`'s loop body was 1036
  words, over the 1024-word reach of a forward branch of the plain back end; now 754).
- `wf`: `wf_calls_ind` (as `wf_calls`, with a `simp [glF]` fallback when `decide` cannot be synthesized for a large
  length expression).

Compiled verbatim (con-leche @6810492 `Kernel/Name.lean`, `Kernel/Expr.lean`), machine theorem `f.implements1` (the
Sail axiom set), `sem` 3 axioms; input: two values one after the other (`T.enc2`) in the range subtype (`Nat`
components `< 2^64`), output one byte:

| entry | function | program | test |
|---|---|---|---|
| `name_beq` | `Name.beq` (`Name.lean:115`) = `decide (a = b)` → `Name.decEq` (`:47-61`) | `Name.decEq`, `Bytes8.eqb` | 60 cases |
| `name_bbeq` | `nameBEq a b := a == b` (`instance : BEq Name`, `:117`) | same | 60 cases |
| `level_beq` | `Level.beq` (`Expr.lean:133`) → `Level.decEq` (`:59-83`) → `Name.decEq` for `param` | `Level.decEq`, `Name.decEq`, `Bytes8.eqb` | 60 cases |
| `level_bbeq` | `levelBEq a b := a == b` (`instance : BEq Level`, `:135`) | same | 60 cases |

Test inputs (`emit_frontx.lean`): names of depth ≤ 5 with ASCII, empty, multi-byte UTF-8 (`é`, `λ`, `∀x`) and NUL
strings and numbers `0`, `7`, `2^64 - 1`, random; pairs equal / last component changed / one more component /
unrelated; levels of depth ≤ 5 with such `param` names, equal / leftmost name changed / unrelated.

**List front end (`frontx_compile`): `String` arguments of calls.**  `Riscv/Frontx/Translate.lean`: a call of a
translated function may pass byte-array and `String` parameters when each is the caller's block in the same position
(`s` ↦ `s.toUTF8`); the length variable of a block other than block 0 is passed like a scalar argument (it is in the
callee's renamed range); a call with a `String` argument is not inlined.  lean-svg @df8e663 `findSeq`
(`Bytes.lean:55-60`, calls `startsWith` per iteration) compiles verbatim with an `exec` theorem
(`StringExamples.lean`; `requires bs.size + s.toUTF8.size < 2^64`, loop invariant `j ≤ k`).  No machine entry: the
machine convention has one input block, and a `String` argument needs a second byte block (or a view into the input).

Not done (strings): `String` values computed by a function (`append`, results), `String.length` (`utf8ByteSize` is
the chain length; not wired), `get`/`Char` and iteration over characters, `startsWith` on a `String` field, a string
literal as a value (a constant chain), `Name.hash`/`mixHash` (opaque), the `@[csimp]` pointer versions
(`decEqPtr`: `ptrDecEq`, `withPtrEqDecEq` are unsafe/opaque, the verbatim `decEq` is the specification they are proved
equal to).  An entry for `findSeq`/`startsWith` needs a second input block or `String` views into the input.

### Speed finding (before the scope change)

**Finding: why `Level.simplify` is 169× gcc** (profile of `level_simplify.words` on an RV64I interpreter, input of
`ind-bench/bench.py`, 205 bytes / 205 nodes): `simplify`'s function is called **12 223 times** for 205 nodes
(`combining` 1 679), ~197 instructions per call. Lean's equation `simplify.eq_5` has the `let ls := simplify l` /
`let rs := …` substituted (zeta-reduced), so the `imax` arm evaluates `simplify l` up to 4 times and `simplify r` twice
as real calls: exponential recomputation, not per-call cost. A fix is a common-subexpression `bind` in the front end
(tried: one strict duplicated call → `E.bind`, the `sem` proof and `nl = 20` unchanged); not kept (speed deferred).
The general per-node cost (3.9–9.9× elsewhere) is ~45 % constant building (`li` one bit at a time in the plain
`rv` back end), slot traffic and 2 instructions per zero-initialised local per call.

## 24. Run-time memory (branch `mem-spec`)

Statements: `Compiler/AllocSpec.lean` (owner): `CompileRuns riscv compile` (no memory hypothesis; with the
output-fits hypothesis approved for it) and `CompileCorrect riscv compile` (hypothesis
`memoryNeeded compiled input ≤ workLength`), with `memoryNeeded = cellSize * peak events`, `OutOfMemory = W <
memoryNeeded`, status register `mapping.status` = `a0` on RISC-V (`riscvMapping.status = 10`).

**Proved for the inductive path** (`Riscv/Frontx/IndMem.lean`, every `frontx_ind` program, one or several
functions): `Proven.Frontx.IndMem.compile_runs : CompileRuns riscv compile`,
`Proven.Frontx.IndMem.compile_correct : CompileCorrect riscv compile`, both with exactly the Sail axioms of
`Proven.Top.compile_correct`; `memoryNeeded_le`: the old space bound (`Ind.spaceA … cellsSup`, the hypothesis of
`implements1_indS` / `implements1_indM`) is at least `memoryNeeded`, so the old theorems' hypothesis gives the new
one.  `compile : IndProg → Option CompiledA` takes the program of the inductive path (`indProgM`, unchanged: the
same source program as the entries' `.code`) and compiles it with the run-time checks; it returns `none` unless
`IndProg.Good` (the old side conditions, well-formedness of the new code, `progClean`, and: inputs of at most
`2^20` bytes allocate fewer than `2^50` cells, so the source run's 64-bit pointers do not wrap).
`Program.run` of an `IndProg`: the output bytes (`Kd.out`) of the Lean semantics `Pg.sem` of the values the input
encodes (`inBytesA`), `none` on other inputs.

**The memory model** (source level, `Compiler/MemRun.lean`, machine-independent, address-free):
cells of 8 bytes; the run with events `TExec` (= `CExec` with word block 0 growing): word block 0 (the heap) is
empty at the start and grows with zero words when a word at or above its length is accessed (event `alloc d`), a
call opens a frame of `nlocals + 1` cells (`alloc`) and closes it on return (`free`), the entry stub's two cells
come first (`alloc 2`).  The program frees no heap (owner's default (2)); frames are allocated on call and freed on
return (default (3)); `memoryNeeded` is defined (the events of the run from a canonical start, `IndProg.events`,
`Classical.choose` of the run), not calculated.  `texec_of_cexec`: every `CExec` run on a zero word block is a
`TExec` run, its peak at most start + heap growth + stack need / 8 (this gives `memoryNeeded_le`);
`texec_det`: runs from states that differ only in unread data (base addresses, output contents) have the same
events (so the machine's run and the canonical one agree).

**The generated code** (`Compiler/MemCode.lean`, `MachineM` = `MachineC` + compare-and-branch on two registers,
read `gp`, read the stub's frame address, the exit; `Riscv/Back/MemRv.lean`): heap at the bottom of the work block
(base `a2`, length in words in `a7`), frames from the top (`sp`, `gp`), free space between.
* every access of word `i` of the heap: `r0 := i; bltu r0, a7, ok` (the common case); else (`i ≥ u`): if word `i`
  lies below the current frame (`i < (gp - a2) >> 3`) zero the words `u .. i` and `a7 := i + 1`, else jump to
  the exit;
* every call: `gp - 8 (n + 1) ≥ a2 + 8 a7` (the callee's frame stays above the heap), else the exit;
* entry stub: if the stub's two cells do not fit, `a0 := -1; ret`; globals 4..7 := 0;
* exit: `ra` from the stub's cell (`alignDown(sp) - 16`), `a0 := -1`, `ret`.
So the run fails exactly when heap + live frames exceed the work block (`execCM_ok`, by induction on `TExec`:
either the events fit and the code ends with the relation, or they do not and the code is at the exit; `compPM_ok`
for the whole program; `memRaw` / `memSpec` from the machine facts / `StartCorrect`).  On success `a0` is the input
address (never `-1`), `a1` the output length (tree results), `gp` restored; on the flag `gp` is not restored (not
required).  The input block is never written (`BStmt.clean`: stores only to byte blocks ≠ 0), so the frame clause
holds in both cases.

**Tests** (`Testing/asm/emit_mem.lean`: `memCode` of every inductive entry and per case `memoryNeeded` from an
interpreter of `TExec`, checked against Lean's result; `python3 Testing/asm/mem_test.py check 50 <name>`): every
case twice on QEMU and Sail: work block = `memoryNeeded` bytes (output = Lean's, `a0` = input address, `a1`,
`gp`, `sp`), and `memoryNeeded - 1` bytes (`a0 = 2^64 - 1`); always input and guards unchanged and (Sail) every
write in the output or work block.

**Coverage gap: branch reach.**  `IndProg.Good` contains `WfMem`, and `WfMem` needs every conditional branch over
an `ite` / `loop` body to reach (`bzOK n := 2 n < 2048`, i.e. at most 1023 words).  The inline checks make the code
about twice as long, and in 4 of the 29 entries one function's body is now too long: `pos_comp` (1178 words),
`tree_insert5` (1375), `level_combining` (2037), `level_simplify` (2046).  For these `compile` returns `none`, so the
theorems hold but say nothing about them.  `emit_mem.lean` checks the same spans and skips them.  Fix (not done):
emit a long form `bz r0, +2; jmp then; jmp else` for far branches, or move the slow path of the access check out of
line (one shared routine per function), which also cuts the code size and the cost below.

**Results.**  25 entries, each 50 cases x 2 (at `memoryNeeded`, then at `memoryNeeded - 1`), all ok on QEMU and Sail.

**Run-time cost** (`mem_bench.py`, instructions retired on the largest of the 50 inputs, old code with its static
work bound vs the new code at `memoryNeeded`): `bt_count` +67%, `bt_graftleft` +87%, `bt_mirror` +15%
(`eq_bintree`: the old code took 1.1e9 instructions, the new one 2.2e6).  Code size about 2x.  This is more than
"a compare + branch per alloc / call".  The checks sit on every heap word access: `li; bltu` on the fast path
(about 4 instructions), about 30 on a heap-growing store (it zeroes the new words), and about 10 per call.  A
per-allocation check would need a source-level proof that loads stay below the heap length.

## 25. Expr (branch `feat-expr`)

(Section 24 is reserved for the memory-spec work on branch `mem-spec`.)

**n-ary constructors** (`Riscv/Frontx/IndCmd.lean`, `layout`). Cells stay `[tag, x, l, r]` (`C` unchanged, so the
decoder, encoder and their proofs are unchanged). A constructor whose fields fit one cell (at most two children, one
scalar) is as before; otherwise its cell takes the longest prefix of its fields with at most one child and one
scalar and `r` points to an **extension cell** with the rest (the same rule again, so any arity). Extension cells
have their own tags after the type's constructors (`TExpr`: tags 0-9 `Expr`, 10 the extension of `letE`). Byte
format (stated by `C.enc T.sh`): fields in declaration order, an extension cell starts with its tag byte, e.g.
`letE ty v b` = `07 ‹ty› 0a ‹v› ‹b›`. A recursive call on a field in the first extension cell is the new `E.call2
c₁ c₂` (a grandchild: `Pg.sem` structural with a nested match, `Cx.okg`, `loop_ok3`/`straight_ok3` prove the loop
for a node and its two children); fields deeper than one extension are read (`ft`) but not recursed on.
`E.exts` counts `call2` (outside the linear bound `al_le`: such programs use `cellsSup`). Shared files changed:
`Compiler/Ind.lean` (`E.call2`, `Cn.g`/`Ca.g`, `Pg.st`, `armN`, `dispS`, `fLoopS`, `fLoopX`, `fFn`; `alloc` and the
`call` code are unchanged), `Compiler/IndOk.lean`, `Compiler/IndDec.lean`, `Compiler/IndMain.lean`.

**Types nested in one shape** (`frontx_ind_type TExpr := ConLeche.Expr nesting ConLeche.Level, ConLeche.Name, List
ConLeche.Level, ConLeche.Literal, List ConLeche.Expr, Option ConLeche.Expr`): the nesting types are defined in a
topological order of the field-type relation (`List Level` after `Level`), every type listed is in the shape even
when no field has it (`Option Expr` as a result type), each nested type gets `T.Nk.enc`, constructors are resolved
by name *and* type (`List Level` / `List Expr` share `List.cons`), and a function may take a nested type as its
structural argument.

**`@[computed_field]`s** (`Expr.data`, `Name.hashData`, `Level.hashData`) are kept verbatim with the opaque
`mixHash`: no function compiled here reads them, so no Lean hash was needed. A function reading `e.data` is
rejected (the field is not in the byte format); the owner's decision (any deterministic Lean hash, e.g.
`MixHashPort.mixHashLean` of branch `mixhash-port`) applies when one is compiled.

**F1** (`r1_arm_count`: the loop body over the ±4 KiB reach of `beqz`). Two changes, both at the inductive-path
level (no new machine operation): the decoder and encoder dispatch with one test per tag in sequence (`dDisp`,
`eDisp`: a branch jumps only over its own fields; Expr's 25-tag shape did not fit before), and a function whose loop
would be over 1000 words (`rvC.lenC` evaluated by the front end) is compiled **straight-line** (`Pg.st := true`,
`fLoopS`: no loop, one test per tag in sequence, every call a real call; `straight_ok3`). Each arm must still fit
the reach. Small functions keep their loops and tail calls (codes and theorems unchanged).

**Long branches in general (owner's request; not done here).** The F1 fix above is at the inductive-path level
(statement shapes whose branches are short), not a long-branch form in the shared back end: `Machine.jmp` is
backward only (`law_jmp`: `pc - 4n`) and `bz` reaches ±1023 words, so `bz +2; jmp then; jmp else` needs a FORWARD
jump. What a general fix needs (shared code, covers the memory path of branch `mem-spec` too): (1) an `AOp.jmpF n`
(`jal x0, +4n`, ±1 MiB) with `law_jmpF` in `Compiler/Iface.lean`'s `Machine`, its RISC-V encoding and law in
`Riscv/Back/Iface.lean` (from the step lemma of `iJmp`, the same `jal` with a positive offset), an encoding in
`Arm/CompilerArm.lean` (`b +n`) and the ARM law in `Arm/proofs`; (2) `MachineC.compC` (`Compiler/CStmt.lean`) for
`ite` as `mgen c; bz (lenBz + lenJmpF); jmpF else; then; jmpF end; else` and for `loop` as `mgen c; bz (lenBz +
lenJmpF); jmpF exit; body; jmp head`, with `wfC` asking `jmpOK` instead of `bzOK` for the long ones (or choosing
the short form when it fits, which keeps every existing code word-for-word). The memory path can instead reuse this
section's statement shapes if its code generator emits `Compiler/Ind.lean`'s `dDisp`/`eDisp`/`fLoopS` (sequential
tests, straight-line function bodies): then only an arm longer than ~1000 words exceeds the reach.

**F3** (`r2`, `r3`, `r5`: built terms as call arguments). New tactic `frontx_calls_sem` (a last branch of the
generated `sem` proof): for each call `f t a b` of a program function in the expected value, the meaning theorem of
`f` (or the induction hypothesis) is instantiated at those arguments, its cells written out, and used to rewrite.
`r8` (an `if` as a call argument) still fails. Also: entries with a constructor literal of another type as
argument (`comp e .nil`), entries whose parameters are in another order than `g`'s, `Nat` subtraction
(`natSub`: `if a < b then 0 else a - b`, with the range hypotheses), and a growing word argument (`d + 1` under a
binder: hypothesis `a + nodes < 2^64` in `sem`, `(emb t).nodes < 2^64` in the machine theorem's input subtype).

**Compiled verbatim** (con-leche @6810492c1; `Riscv/Frontx/ExprExamples.lean`; type `Kernel/Expr.lean:400-460`,
`Literal` `:143-146`, `levelsHaveParam`, `levelHash`, `levelsHash` `:194-205`), each `f.implements1` (the Sail axiom
set, `axioms_x.lean`), `sem` at most propext/Classical.choice/Quot.sound; tests: `frontx_test.py check 60`, QEMU +
Sail against executed Lean (`Testing/asm/emit_expr.lean`: 60 expressions of depth ≤ 7 with every constructor,
names with UTF-8/NUL strings and numbers up to `2^64 - 1`, level lists, literals, bound indices 0-5 and `2^64 - 1`):

| entry | function | source | form | test |
|---|---|---|---|---|
| `hasFvar` | `Expr.hasFvar` | `Kernel/ExprOps.lean:60` | loop | `expr_hasfvar` |
| `closed0 e = looseBVarsBounded 0 e` | `Expr.looseBVarsBounded` | `ExprOps.lean:46` | loop, `a + nodes` | `expr_closed0` |
| `inst1 e v = instantiate1 e v 0` | `Expr.instantiate1` | `ExprOps.lean:27` | straight, two inputs | `expr_inst1` |
| `sizeF` | `Expr.sizeF` | `ExprOps.lean:788` | | `expr_sizef` |
| `scopedD e d = wscopedB d e` | `Expr.wscopedB` (WF recursion) | `ExprOps.lean:821` | word from input | `expr_scopedd` |
| `isForallE`, `getAppFn`, `piResult`, `fvarTypeD` | | `ExprOps.lean:836,848,880,905` | | `expr_isforalle` … |
| `numArgs` | `Expr.numArgs` | `Kernel/PropRead.lean:56` | | `expr_numargs` |
| `isLit` | `Expr.isLit` | `Kernel/Core.lean:1119` | | `expr_islit` |

All 11 pass `frontx_test.py check 60` (60 cases each; codes 4150-5271 words, `inst1` straight-line). Self-hoster
reproducers `r1`, `r2`, `r3`, `r5` compile with machine theorems (`Riscv/Frontx/TinyRepro.lean`, `axioms_x.lean`).

Reproduce: `lake build Frontx`; `lake env lean --tstack=4000000 Testing/asm/emit_expr.lean`;
`bash Testing/scripts/frontx_tests.sh 60`; axioms `Testing/scripts/axioms_x.lean` (in `check.sh`). The existing
inductive entries' codes changed (sequential dispatch in `dec`/`enc`; re-emitted with `emit_frontx.lean`, all
re-tested); their `stmt` hashes are unchanged, 62 closures changed (not re-frozen).

**Type gate** (the depth probe's 186 functions whose signatures mention only `Name`/`Expr`; new command
`frontx_ind_gate f on T` in `Riscv/Frontx/IndGate.lean`, no proofs; run over `F2.lean.txt` of branch
`conleche-depth`, 180 resolved, the 6 `beside.*` names are not con-leche functions): **62 pass the type gate**
(before: 0 with `Expr`, the `TExpr` type itself was rejected), 28 of them also translate all arms. Gate failures:
91 "no argument of a declared type" (nullary `Name` constants such as `natAddName`, and functions over scalars
only), 14 more than one scalar parameter (`liftLooseBVars amount cutoff`), 7 other parameter types, 4 two extra
tree parameters, 2 result types. Of the 34 passing the gate but not the arms: 25 overlapping/variable patterns in a
function called from another (`eq_1 has no constructor pattern`), 4 nested patterns (`isStrLit`'s
`.lit (.strVal _)`), 2 patterns on two arguments (`instPisWith`), 2 comparisons of other types, 1 a lambda argument.

**Not done / why**: `liftLooseBVars` (two scalar parameters, one constant: needs specialisation of a constant
parameter); `getAppArgs` (`List.append` is polymorphic and the program's functions are found by name, so its type
is ambiguous between `List Level` and `List Expr`); `mkAppN` (rejected: the head as a tree parameter before the
structural one); `instPisWith`, `piResidual`, `binderDom` (patterns on two arguments / on a `Nat`); `Expr.depth`
(`max`: `sem` not proved); `isStrLit`, `natPred?` (nested patterns); `r8` (an `if` as a call argument).
Codes are large (plain back end; straight-line `inst1` makes real calls for every child).

## 26. Int (branch `feat-int`)

Files: `Compiler/MOp.lean` (`div`, `rem`), `Riscv/Steps/GenMul.lean` (`step_div`, `step_rem`), `Riscv/Back/Wide.lean`
(`w_mop`), `Riscv/Frontx/IntRep.lean` (new: representation, lemmas, `frontx_int_facts`, `frontx_int_abbrev`),
`Translate.lean`, `Sub.lean`, `Impl1.lean` (`Res Int`), `Wa{Lang,Comp,Exp,Upd,Cmd}.lean`, `LeanSvgFixed.lean` (verbatim
lean-svg), `IntExamples.lean`, `WaInt.lean`; tests `Testing/asm/emit_int.lean` → `frontx-words/{int,wa_int}_*`;
axioms in `Testing/scripts/axioms_wa.lean` (`wa_check.sh`). Spec/ untouched; the inductive path (`Ind*`) untouched.

**Lean's semantics.** On `Int`, `/` is `Int.ediv` and `%` is `Int.emod` (checked: `-7 / 2 = -4`, `-7 % 2 = 1`,
`7 / -2 = -3`, `7 % -2 = 1`, `x / 0 = 0`, `x % 0 = x`; `0 ≤ x % y < |y|` for `y ≠ 0`). lean-svg writes `Int.ediv a 256`
(same function).

**Encoding.** A value is its two's complement word `rI x = BitVec.ofInt 64 x` (= `x mod 2^64`); a result is 8 bytes
little-endian of `x % 2 ^ 64` (`Res Int`, `Impl1.lean`), as `Nat` results are `n % 2 ^ 64`: not range checked; for
`-2^63 ≤ x < 2^63` the bytes determine `x`. Word arrays: `Array Int` elements are words the same way (width 8).

**Machine.** `MOp.div` / `MOp.rem` (`Compiler/MOp.lean`): `div a b = if b = 0 then allOnes else ofInt (a.toInt.tdiv
b.toInt)`, `rem a b = ofInt (a.toInt.tmod b.toInt)`. Checked against the Sail model (`execute_DIV`, `execute_REM` in
`LeanRV64D/InstsEnd.lean`): by zero the quotient is `-1` and the remainder the dividend; on `-2^63 / -1` the model
clamps the quotient to `-2^63`, which is the wrap of the true `2^63`, so `div` needs no overflow case (`div_eq`).
Encodings `encR 1 4` / `encR 1 6`; `G.step_div` / `G.step_rem` by `gstep` (the model writes `2 ^ 63` with Sail's
`Int ^ Int` instance, so `step_div0` is stated in the model's form and rewritten by `div_eq`). Every pass of the
optimiser is generic in `MOp` (no other change); the plain back ends still reject `mop`.

**Lean `/`, `%` from the machine's** (`IntRep.lean`): with `q = div a b`, `r = rem a b`,
`x % y = if r < 0 then (if y < 0 then r - y else r + y) else r` (`emodB`),
`x / y = if r < 0 then (if 0 < y then q - 1 else q + 1) else if y = 0 then 0 else q` (`edivB`; the `y = 0` case
uses the machine's `-1 + 1 = 0` when `r = x < 0`). `rI_ediv`, `rI_emod`: `rI (x / y) = edivB (rI x) (rI y)` for
`x, y` in range (proved through `Int.tmod_eq_emod` / `Int.tdiv_eq_ediv`; no overflow case needed: `|tmod| ≤ |x|`).

**Range hypotheses** (visible): `+ - * -x`, `Int.ofNat` / `↑n`, literals need nothing (homomorphic mod `2^64`);
`<`, `≤`, `=`, `Int.toNat`, `Int.natAbs`, `/`, `%` need their operands in `-2^63 ≤ x < 2^63` (side conditions of
`rI_slt`, `rI_inj`, `rN_toNatI`, `rN_natAbs`, `rI_ediv`, `rI_emod`, discharged by `omega`). In `frontx_compile` they
come from `requires` (e.g. `frontx_compile LeanSvg.Fx.mul requires fun a b => -2 ^ 63 ≤ a * b ∧ a * b < 2 ^ 63`), in
`wa_compile` from `E.ok` (`Ty.small .int`; `Op2.exact` is now per type: `Int` `-` needs nothing; `cast.side` for
`Int.toNat`) and the loop invariants. The entries read their arguments as signed 32- or 64-bit words (`i64At`,
`i32At`, `rdI32`, glue), so the machine theorems have no hypothesis beyond the `Implements1` frame:

    LeanSvg.Fx.mul.exec : ∀ a b σ, … → -2 ^ 63 ≤ a * b ∧ a * b < 2 ^ 63 → ∃ σ', BExec … ∧ σ'.env 4 = rI (Fx.mul a b) …
    Proven.Frontx.IntEx.mulE.implements1 : Implements1With (fun xs => xs.data.toList) Res.enc mulE.code mulE (space)
    Proven.WA.IntOps.iopsE.implements1 : Implements1With (fun xs => xs.data.toList) Res.enc iopsE.code iopsE (space)

**List front end** (`Translate.lean`): `Ty.int` (also through abbreviations: `Fx`), `+ - *` (`*` by `mop mul`),
`-x` (`0 - x`), `Int.neg`, `/`, `%`, `Int.ediv`, `Int.emod` (two `mop`s and the adjustment; the quotient / remainder in
a temporary holding its Lean term, so nested quotients do not grow the obligations), comparisons `slt` (compound sides
to temporaries, as for `Nat`), `==`, `=`, `≠`, `min`/`max` (`Int.min_def`), `Int.toNat`, `Int.natAbs`, `Int.ofNat`,
`↑n`, literals and named `Int` constants (`Fx.maxVal`, unfolded in the obligations), `let` inside inlined helpers.
Proof support: `frontx_int_abbrev` (unfold `Int` abbreviations and `Int.ediv`/`Int.emod` to `/`/`%` before `omega`),
`frontx_int_facts` (bounds of `Int`/`Nat` products of non-literals from searched bounds of the factors, `mul_bound`;
`omega` does not multiply variables), `ite_eq_orI` (an `Int` temporary defined by an `if`, with its condition),
`rI_ofNat` as a pre-order simp lemma (else `simp` pushes the cast inside first).

**Word arrays** (`Wa*.lean`): `Ty.int` (`Int`, `rI`, width 8, `Array Int`), `Op2.den` `+ - * / %` on `Int`,
`Cmp.den` with signed `mcmp t` (`slt`), casts `Int.toNat` (`mcast`: `slt`-select) and `Nat → Int`, `iDivS` / `iModS`
(the two `mop`s and the adjustment, temporaries `d + 2`, `d + 3`), reflection of `-x`, `Int.ediv`, `Int.emod`,
`Int.toNat`, `↑n`, `Int.ofNat`. `mop_ok`, `mcmp_ok`, `mcast_ok`, `mword_ok`, `binS_ok` extended (proved once).

**Compiled verbatim** (lean-svg @df8e663, `LeanSvgFixed.lean`; each line checked to occur unchanged in the source;
each function's own `exec` with its `requires`, and an entry `…E` with `Implements1` via `frontx_implementsC`):
| function (lean-svg @df8e663) | source | `requires` of its `exec` | entry arguments | words |
|---|---|---|---|---|
| `Fx.clamp` | `LeanSvg/Fixed.lean:27` | -2^63 ≤ a < 2^63 | i64 | 120 |
| `Fx.inRange` | `LeanSvg/Fixed.lean:32` | a in range | i64 | 99 |
| `Fx.ofNat` | `LeanSvg/Fixed.lean:34` | n < 2^32 | n mod 2^32 | 123 |
| `Fx.mul` | `LeanSvg/Fixed.lean:37` | -2^63 ≤ a*b < 2^63 | i32, i32 | 337 |
| `Fx.floor` | `LeanSvg/Fixed.lean:38` | a in range | i64 | 129 |
| `Fx.ceil` | `LeanSvg/Fixed.lean:39` | -2^63 < a < 2^63 | i32 | 140 |
| `Fx.round` | `LeanSvg/Fixed.lean:40` | -2^63 ≤ a, a+128 < 2^63 | i32 | 136 |
| `Fx.abs` | `LeanSvg/Fixed.lean:41` | a in range | i64 | 116 |
| `Fx.min / Fx.max` | `LeanSvg/Fixed.lean:42-43` | a, b in range | i64, i64 | 291 / 291 |
| `Fx.scale16` | `LeanSvg/Fixed.lean:50` | a*s in range | i32, i32 | 337 |
| `clampLin` | `LeanSvg/Geom.lean:74` | v in range | i64 | 120 |
| `linInRange` | `LeanSvg/Geom.lean:82` | v in range | i64 | 99 |
| `Image.clampIx` | `LeanSvg/Image.lean:406` | i in range, n < 2^64 | i64, n mod 2^32 | 307 |
| `Image.round32` | `LeanSvg/Image.lean:426` | s in range | i64 | 131 |
| `Image.bicFar` | `LeanSvg/Image.lean:416` | 0 ≤ t < 2^17 | (exec only) | – |
| `Woff.fitsI16` | `LeanSvg/Woff.lean:175` | v in range | i64 | 100 |
| `Raster.insideW` | `LeanSvg/Raster.lean:85` | w in range | bit, i64 | 290 |
| `Grad.norm2` | `LeanSvg/Shader.lean:153` | |x|, |y| ≤ 2^31 | i32, i32 | 333 |
| `Grad.clampTo` | `LeanSvg/Shader.lean:163` | -2^63 < lim < 2^63, a in range | i32, i64 | 366 |
| `Filter.morphCeil` | `LeanSvg/Filter/Morphology.lean:110` | -2^63 ≤ r < 2^31, sc < 2^32 | i32, n mod 2^32 | 308 |

Each entry `…E` (`IntExamples.lean`): QEMU + Sail against executed Lean, 70 cases each (edge words `0`, `±1`, `±2^31`,
`2^63 - 1`, `-2^63`, `Fx.maxVal ± 1`, `linMax + 1`, multiples of 256, random 64/32/20/17-bit), all ok.
Word arrays (`WaInt.lean`, glue entries over core / lean-svg operations): `iopsE` (`* / % -x + -`, `Int.ediv`,
`Int.emod`; 372 words), `icmpE` (`<`, `≤`, `Int.toNat`; 329), `fxRoundsE` (`Fx.floor`/`ceil`/`round`; 492),
`sumDevE` (an `Int` loop state with a linear invariant; 85): `good` + `implements1` each, 70 cases each, all ok.
Axioms (`wa_check.sh`): every `implements1` exactly the Sail set, every `exec`/`good` ⊆ {propext, Classical.choice,
Quot.sound}. `check.sh`: ALL CHECKS PASSED; statement fingerprints: no `stmt` hash changed, 62 closures changed
(`MOp` gained `div` / `rem`; not re-frozen). `emit_int.lean` is slow (> 50 min for the list entries' code at `#eval`).

**Not done / why.**
- con-leche `Level.leq` / `Level.rest` / `Level.byCases` (`Kernel/Level.lean:87-145` @6810492c1): their `diff : Int`
  goes with `Level` arguments, i.e. the inductive path (another agent's files): an `Int` field / argument kind in
  `Compiler/Ind*.lean` is needed there (the representation lemmas of `IntRep.lean` apply unchanged).
- lean-svg `Image.bicNear` (`Image.lean:410`): the obligation of the third nested quotient did not close (the
  term of `(b * t).ediv 65536` with `b` itself a quotient is large); `bicFar` compiles alone (its `exec`), its entry
  did not (`simp` nested error): not kept.
- lean-svg `Fx.hypot` (`Nat.sqrt`), `scaleDecimal` (`10 ^ exp10.toNat`, unbounded), `parseNumber`/`parseDecimal`
  (`Option (Fx × Nat)` results, loops), `expSmall` (`lnScale = 2 ^ 128`: beyond 64 bits), and everything with `Mat`/`Pt`
  structures of `Int` fields (needs structure parameters of `Int` fields; `resultComps` takes them, not tried).
- `Fx.clamp` inside a `wa_compile` loop: the reflection panics (`index out of bounds` in `wa_compile`'s meta code); a
  plain `Int` loop state works (`sumDevE`).
- `Int` shifts / bitwise operations, `Int.sign`, `Int.fdiv`/`Int.tdiv` as source operations (only `/`, `%`).
- Non-vacuity corollaries for the new `Implements1With` theorems: the existing one is for `StartCorrect`
  (`Riscv/Examples/VacuityTop.lean`); no front-end generator for per-function corollaries exists yet.
- Axioms: the new theorems are listed in `axioms_wa.lean` (checked by `wa_check.sh` with the same rule as the other
  word-array / list-front-end theorems), not in a branch-named file.
- Speed: every `/` is two M-extension instructions plus a select; `x / 256` is not yet a shift (`ediv` by `2^k` is
  an arithmetic shift right: a later pass).

Reproduce: `lake build Frontx`; `lake env lean --tstack=400000 Testing/asm/emit_int.lean`;
`for f in Testing/asm/frontx-words/{int,wa_int}_*.cases; do python3 Testing/asm/frontx_test.py check 50 $(basename $f .cases); done`;
`bash Testing/scripts/wa_check.sh`.

**State (paused, 2026-11-16).** Round complete on `feat-int` (merged with origin/main @69ebe82): `check.sh` ALL CHECKS
PASSED, 20 list-path + 4 word-array `Int` entries tested (70 cases each, QEMU = Sail = Lean). Next steps:
1. `Int` fields/arguments in the inductive path (`Compiler/Ind*.lean`), then con-leche `Level.leq`/`rest`/`byCases`.
2. `bicNear`: keep nested quotients' obligations small (generalise more eagerly, or one lemma per `edivB` level).
3. `Fx.clamp` inside `wa_compile` loops: find the `index out of bounds` in `WaCmd.lean`'s reflection.
4. `Int` structures (`Mat`, `Pt`) as parameters/results; `Option Int` results (`Filter.n16At`, `parseNumber16`).
5. Speed: `x / 2^k` on `Int` as an arithmetic shift; make `emit_int.lean` fast (precompute the codes).
6. Non-vacuity corollaries once a per-function generator exists; re-freeze fingerprints (owner).

## 27. Higher-order arguments by specialisation (branch `feat-hof`)

Files: `Riscv/Frontx/SpecHof.lean` (new: the pass and the commands), `Riscv/Frontx/HofExamples.lean` (new: targets),
`Testing/scripts/axioms_x.lean` (new). Shared files touched: `Riscv/Frontx/Translate.lean` (two proof tactics of
`frontx_view`, below), `Testing/scripts/check.sh` (`axioms_x` in the loop), `Testing/scripts/expected-axioms.txt`
(39 lines appended), `Testing/asm/emit_frontx.lean` (one `#eval` block), `Testing/asm/frontx_test.py` (`LISTS`).
No `Compiler/`, `Spec/` or `Ind*` file changed.

**The pass** (`frontx_hof h`, front end only; everything after it is the existing translator):
- A **site** is a call `F a₁ … aₙ` of a definition `F` where some argument is a function known at compile time
  (function-typed, not a proof or type family, and no free variable of it is itself a function: a lambda, a
  named function, a partial application `BOp.eval .xor 0x55`, `f ∘ g`). Fixed positions: types, instances, proofs,
  known functions. Matchers, recursors, `ite`/`dite`/`cond`/`bind`/projections are never sites.
- A recursive `F` gets a **first-order copy** `h.hof<k> c₁ … cₘ y₁ … yₚ := F a…` (the `cᵢ` the first-order free
  variables the fixed arguments capture, e.g. `k` in `(· > k)`; the `yⱼ` the non-fixed arguments), and
  `h.hof<k>.eq`: `F`'s own unfolding equation at these arguments, the recursive calls with the same fixed arguments
  folded to the copy (a call that changes a fixed argument is rejected), the known function beta-reduced,
  `Function.comp` unfolded. This step is definitional: the proof term is `F`'s equation, the kernel checks the
  folded statement by delta. A non-recursive user `F` (`Array.find`) and `List.countP` are unfolded instead.
  Equal sites share one copy; sites inside a copy's body are specialised in turn (depth ≤ 8).
- **Rewriting steps** (`simp only` with the listed lemmas, the proof kept, so not definitional but kernel-checked):
  before: `Array.foldl_toList` (reversed), `List.foldl_nil/cons` (a fold over a literal list, e.g. a pipe of
  stages), fusion `List.map_map`, `foldl_map`, `foldr_map`, `any_map`, `all_map`, `countP_map`; after, on each copy:
  `cons_append`/`nil_append` (`[x, x] ++ r`), `pure_bind`, `Option.pure_def`, `failure = none`, `some a >>= f = f a`
  (`do` in `Option`), `cond_eq_if`, `a || r` / `a && r` → `if` when `r` holds the recursive call (marked first,
  definitionally, `hofMark`), and per `Bool` matcher `m` a generated lemma `m.hof_ite : m _ b x y = if b = true
  then x () else y ()` (by cases; Lean's `List.filter`/`find?` match on `p a`).
- **Partial evaluation**: user definitions applied to a closed constructor term (`Stage.denote (.map e)`,
  `ByteExp.denote 0 x e`, `BPred.denote`, `BOp.eval .xor`) are rewritten by their own equation lemmas until nothing
  changes. That is how the compiler core's pipeline semantics at a known stage becomes a first-order loop.
- Three once-and-for-all lemmas replace unfolding equations whose `match` also binds the function (`List.any`,
  `List.all`) or that have none (`List.flatMap := flatten ∘ map`): `hof_any_eq`, `hof_all_eq`, `hof_flatMap_eq`
  (`cases l <;> rfl` / `simp`).
- Result `h.hof : h ys = body'` (`body'` calls the copies). `frontx_hof_entry g [measure μ] [with inv]` for an
  entry `g : ByteArray → R`: `frontx_hof g`; the copy on the input (`frontx_view`, or `c.ba B … := c B.data …` for
  an `Array UInt8` parameter: sizes and reads of `B.data` are those of `B`, definitionally); `frontx_compile` (measure
  default `B.size - i`); `g.hof.entry : g xs = c.view xs 0 …` (`rw [g.hof]; rfl`); `frontx_entry g from
  g.hof.entry`. Then `frontx_implements[_list|_bytes] g` as before, so `g.implements1` is about `g` itself.

`Translate.lean` hook (proofs only, no generated code changes): `frontx_view`'s simple path tried `simp only [copy]`
before `rw [eq]`; for an equation that is not definitional (the rewriting steps) `simp only` made progress and left
the goal open. Now `first | rfl | (rw [eq] <;> rfl) | …` (the old `(rw [eq]; rfl)` failed whenever `rw` itself closed
the goal), and the general path's leaves (`veqGo`) also try `rw [eq]` / `simp only [eq, Nat.add_sub_cancel]`.

**Compiled, machine theorem** `g.implements1` (the Sail axiom set, compared with `crcRaw.implements1`'s), `g.exec`
and `.hof` at most `propext`, `Classical.choice`, `Quot.sound`; test `frontx_test.py check 50` on QEMU and Sail
against executed Lean (`emit_frontx.lean`), all ok, lengths up to 2769:

| entry | higher-order function, known argument | source | words |
|---|---|---|---|
| `nonFindGt3` | `EarlyReturn.Non.List.find? (· > 3)` | fp-lean @0abeea5 `MonadTransformers/Do.lean:93` | 77 |
| `findGt3` | `EarlyReturn.List.find? (· > 3)` (`do`, `failure`, `return`) | `Do.lean:105` | 77 |
| `filterGt3` | `NonTail.filter (· > 3)` (no hand `def` any more, cf. §12 `filterAll`) | `ProgramsProofs/TCO.lean:183`, use `:204` | 65 |
| `foldrSum` | `ListExtras.List.foldr (· + ·) 0` on `map UInt8.toNat` (two copies) | `DependentTypes/Finite.lean:118`, use `:126` | 79 |
| `arrFindGt3` | `Array.find · (· > 3)` → `findHelper` (`Array UInt8` as the input, result `Option (Nat × UInt8)`) | `ProgramsProofs/Arrays.lean:293-306` | 106 |
| `mapInc`, `mapComp`, `mapXor` | `List.map (· + 1)`, `map ((· ^^^ 0x5A) ∘ (· + 7))`, `map (BOp.eval .xor 0x55)` | Lean core; `BOp.eval` `Compiler/Front/Pipe.lean:27` | 57, 61, 59 |
| `sumFoldl` | `List.foldl (fun acc x => acc + x.toNat) 0` (`with` invariant, as `Tail.sum`) | core | 73 |
| `xorArr` | `Array.foldl (· ^^^ ·) 0` on `xs.data` | core | 52 |
| `dupAll` | `List.flatMap (fun x => [x, x])` | core | 63 |
| `filterNZ`, `anyNL`, `allAscii`, `findHigh`, `countSp` | `filter (· != 0)`, `any (· == 10)`, `all (· < 128)`, `find? (· ≥ 128)`, `countP (· == 32)` (`with` invariant) | core | 68, 68, 65, 78, 83 |
| `countAbove100` | `countAbove l k := l.countP (· > k)`: the closure captures `k`, a parameter of the copy | ours | 84 |
| `stageMap` | `Stage.denote (.map e)` = `l.map fun x => e.denote 0 x`, `e` known | `Compiler/Front/Pipe.lean:125` | 61 |
| `pipe2` | `Pipe.denote [.map e₁, .map e₂]` (`foldl` over the stages unrolled, the maps fused) | `Pipe.lean:137` | 61 |
| `xstageFilter` | `XStage.denote (.filter p)` = `l.filter p.denote`, `p` a known `BPred` | `Compiler/Front/PipeStd.lean:171` | 67 |

Human input: `with` invariants for `Nat` accumulators (`sumFoldl`, `countSp`, `countAbove100`; the same bound as
`Tail.sum`/`Tail.length`); `countAbove100` is written out (`frontx_hof`, `frontx_view`, `frontx_compile`, an entry
equation `rw [countAbove100, countAbove.hof]; rfl`) because its entry is not itself the higher-order call.

Not done / why:
- `Mine.List.flatMap` (`DependentTypes/DB.lean:458`) verbatim: in Lean 4.29 the `xs.flatMap f` in its body resolves to
  core `List.flatMap`, so the book's function is a non-recursive wrapper whose body is a `match`; the entry's body is
  then a `match`, not a call of a copy (`frontx_hof_entry` wants one call). The core function compiles (`dupAll`).
- `EarlyReturn.Desugared.List.find?` (`Do.lean:123`, `runCatch` over `ExceptT … Option`), `Many.orElse`,
  `Monads.Writer.andThen`, `listMonoid`: monad transformers / function-valued data, not first-order after
  specialisation of one argument.
- `TailRec.Array.map`/`arrayMapHelper` (`Arrays.lean:274-287`), `Array.map`: `Array` results (no array output).
- Compiler core (`SELFHOST_DEPTH.md` row 1): no function there is blocked by higher-order arguments alone; the
  closures sit inside passes over `IR.Code`/`BStmt` (n-ary inductives), lists of non-bytes, `Fin`, sized `BitVec`
  (e.g. `runLi` folds `LiStep.eval` over a `List LiStep` of sized bit vectors, `loB`'s predicate is a parameter).
  The pipeline semantics above (`Stage/XStage/Pipe.denote`) are the core functions where specialisation alone
  suffices, at a known stage.
- con-leche (`CONLECHE_DEPTH.md` row 6): the closures are monadic continuations (`k : Expr → m Expr`), environment
  lookups (`Name → Option ConstantInfo`) and records of closures (`CoreFns`); every function there fails the type
  gate first (`Expr`, `m α`). Not attempted.
- **Escaping closures** (out of scope, reported): closures stored in data (`CoreFns`, `WideF`/`MachineF` records,
  `Base.get`), returned (`IR.color : … → Option (Nat → Reg)`, `envB`/`svB` in `Opt/BSel.lean`), or passed down a
  recursion that changes them (rejected: "a recursive call changes a fixed argument").
- A site inside a loop body of a compiled function whose list argument is not the input (`xs.any …` on a second
  list) compiles only as far as the translator's calls allow (§12.4: callee blocks are the caller's first block).

Reproduce: `lake build Riscv.Frontx.HofExamples`; `lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean`;
`for f in Testing/asm/frontx-words/hof_*.cases; do python3 Testing/asm/frontx_test.py check 50 $(basename $f .cases); done`;
axioms: `Testing/scripts/axioms_x.lean`.

## 29. Monads by specialisation (branch `feat-monad`, on `feat-hof`)

Files: `Riscv/Frontx/SpecMonad.lean` (new: the pass, its lemmas, `frontx_monad`, `frontx_monad_entry`,
`frontx_monad_fn`), `Riscv/Frontx/MonadExamples.lean` (new: targets), `Testing/scripts/axioms_y.lean` (new).
Shared files touched: `Riscv/Frontx/Translate.lean` (three lines, below), `Testing/scripts/check.sh` (`axioms_y` in the
loop), `Testing/scripts/expected-axioms.txt` (32 lines appended), `Testing/asm/emit_frontx.lean` (one `#eval` block).
No `Compiler/`, `Spec/`, `Ind*` or §27 file changed (`SpecMonad.lean` imports `SpecHof.lean` and reuses its helpers).

**The pass** (`frontx_monad h`, front end only; the copies are compiled by the existing translator):
- A **site** is `StateT.run (F a) s`, `ReaderT.run (F a) r`, nested (`StateT.run ((F a).run r) s`: a list of `run`
  layers), or `F a` of type `Except ε α` / `Option α` / `Id α` with an instance or a known function among its
  arguments (a definition polymorphic in `[Monad m] [MonadState σ m]` / `[MonadExcept ε m]` used at a concrete
  monad), or `forIn l b f` over a list with a known body (`for x in l do`). Fixed positions: §27's plus type formers
  (the monad `m`).
- A recursive `F` gets a copy `h.mon<k> caps ys extras := C[F a]` (`C` the layers, `extras` the state / environment,
  `Id` stripped from the type). Its equation is `F`'s own unfolding equation under `C` (`congrArg`), then `simp only`
  with Lean core's `StateT.run_bind/pure/get/set/modify/modifyGet/map`, `ReaderT.run_bind/pure/read/map`,
  `ExceptT.run_bind/pure/throw`, `List.forIn_cons/nil`, `pure_bind`, `bind_assoc`, `bind_pure` and 55 lemmas of
  `SpecMonad.lean` (each `rfl` or by cases: `run` of `ite`/`dite`/`throw`/`tryCatch`/lifted `get`/`set`/`modify`,
  `ite`/`dite` under `bind`, `Except`/`Option`/`Id` `bind`/`pure`/`map`/`tryCatch` on constructors, projections of
  `ite`, `MProd`, an `ExceptT` action bound in `m` as its `run`), `zeta` (the `do` join points), and two simprocs:
  `monPushMatch` pushes a context (`run`, projections, `bind`, `tryCatch`, `<$>`, an outer `match`) into a `match`,
  proved by the matcher itself (motive `fun d => C[match d …] = match d …`, every alternative `rfl`), `monMatchIte`
  a `match` on an `if` (`apply_ite`). The recursive calls `C[F a']` with the same fixed arguments are folded to the
  copy (definitional), nested sites are specialised in turn, non-recursive monadic definitions (`runCatch`,
  `checkedSub`, `Loops.List.count`) unfolded. So the state is an extra parameter and the second component of the
  result, `Except` the §16 tag-byte payload, a `for` loop a first-order recursion on the list.
- After the loop (the body is `K[c]` with one copy call `c`): `monAbsorb` absorbs the continuation `K` (the `match`
  of an early `return` in a `for`, `failure` after the loop) into a new copy `K[cN zs]` whose equation is `cN`'s under
  `K`; `monConstArgs` drops a parameter that the entry and every recursive call pass as the same closed value (the
  "not returned yet" loop state `⟨none, ()⟩`), its equation `cN`'s at that value.
- `h.mon : h ys = <first-order body>`: at most `propext`, `Quot.sound` (from `List.forIn_cons`), nothing for most.
  `frontx_monad_entry g [measure] [with]` = §27's entry command on `frontx_monad` (`g.mon.entry`, `rfl` after
  `rw [g.mon]`); `frontx_monad_fn g [requires]` for a body without a loop: `g.monb xs (_ : Nat)` (the §16 `…At`
  convention), `frontx_compile`, `frontx_entry g from g.mon.entry`.

`Translate.lean` (generated code of all older entry points unchanged): `resultComps Unit = []` (no component: the
`Unit` of `Unit × σ` / `Except ε (Unit × σ)`); a result with ONE component inside a compound type (`Unit × Nat`) goes
the several-components path (`multi`) in `frontx_compile` and `frontx_entry`, not the scalar one.

**Compiled, machine theorem** `g.implements1` (the Sail axiom set, equal to `nonFindGt3.implements1`'s), test
`frontx_test.py check 50` on QEMU and Sail vs executed Lean (`emit_frontx.lean`), all 17 × 50 ok, lengths up to 2769:

| entry | monadic code | source | words |
|---|---|---|---|
| `countGt3`, `countNotGt3` | `ThenDoUnless.count`/`countNot` (`[Monad m] [MonadState Nat m]`, `if ← p x`, `unless`, `modify`) at `StateM Nat`, `p := fun x => pure (x > 3)` | fp-lean @0abeea5 `MonadTransformers/Do.lean:66,76` | 84, 84 |
| `countGt3Exc` | `count` at `StateT Nat (Except String)`, the predicate `throw`s on 0 | `Do.lean:66` | 111 |
| `desFindGt3` | `EarlyReturn.Desugared.List.find?` (`runCatch` over `ExceptT α Option`, `throw`, `monadLift`; §27 "not done") | `Do.lean:114,123` | 77 |
| `loopFindGt3`, `contFindGt3` | `Loops.List.find?`, `Loops.Cont.List.find?` (`for`, early `return`, `continue`, `failure`) | `Do.lean:324,332` | 77, 79 |
| `loopCountSp` | `Loops.List.count` (`Id.run do`, `let mut`, `for`) | `Do.lean:345` | 83 |
| `twoE`, `threeE`, `sixE` | `Mut.St.two` (a `StateT Nat Id` block applied to `0`), `Mut.three`, `Mut.six` (`for` over `[1, 2, 3]`, unrolled) | `Do.lean:372,386,396` | 48, 48, 48 |
| `sumNZE` | `StateT Nat (Except String)`, `throw`, `modify` | ours | 100 |
| `countZerosE` | `try … catch` in the loop body (`StateT Nat (Except String)`) | ours | 88 |
| `countAboveRE` | `ReaderT UInt8 (StateM Nat)`, `read` | ours | 85 |
| `maxStE` | `get`/`set` in `StateM UInt8` | ours | 61 |
| `splitE` | a structure `Counts` as the state, `modify fun c => { c with … }` | ours | 116 |
| `firstBigE` | `[Monad m] [MonadExcept String m]` at `Except String`, early `return`, `throw` | ours | 77 |
| `trySubE` | `tryCatch` in `Except` around a helper (`frontx_monad_fn`) | ours | 65 |

Human input: the `with` invariants of the `Nat` accumulators (as §27's `countSp`).

Not done / why:
- lean-zip (`LEANZIP_DEPTH.md`, EXC): the functions whose only blocker is EXC (`BitReader.readBit`, `readBits`
  (+ `go`), `readUInt16LE`, `alignToByte`, `readBitsFast`, `takeBits`) already compile through §16 (the probe ran
  `frontx_compile` on the `readBits` wrapper, not on the `rfl` entry). Every other EXC function also needs ARR, BAO,
  BAF, STR, IND or WF (`decodeStored` → `readBytes` (`ByteArray` result), `validateLengths` (arrays), the inflate
  loops); none became reachable.
- con-leche (`CONLECHE_DEPTH.md` row 11): no `CheckM`/`CheckCM`/`[Monad m]` function passes the type gate apart from
  the monad: the `m`-polymorphic kernel functions take `Expr`/`Level`/`CoreFns m`; the only scalar ones,
  `peelFuelM`/`maxNatSizeM`/`flushC` (`Cached/StateC.lean:324,328,508`), live in `CheckCM = StateT CState CheckM`,
  whose state `CState` holds `HashMap`s of `Expr`/`Name`/`Level` (not in this repo; row 1, 2, 8). The pass handles that
  monad shape (`countGt3Exc`, `sumNZE` are `StateT σ (Except ε)`); what is missing is the data.
- fp-lean `countLetters` (`Do.lean:44`, `StateT LetterCounts (Except Err)`): `Char`/`String` (`List Char`,
  `vowels.contains`); the book's own `State σ α := σ → σ × α` monad (`Monads.lean:476`) and `number`
  (trees out).
- Non-tail recursive monadic calls (`helper left` then `helper right`): the copy returns a pair, and the translator's
  calls take one result word (§16).
- `for i in [a:b]` in a monad other than `Id` (the range loop of `For.lean` is `Id` only); `ExceptT` over `StateM`
  contexts (only `ExceptT … Option` through `runCatch` was needed).

Reproduce: `lake build Riscv.Frontx.MonadExamples`; `lake env lean --tstack=4000000 Testing/asm/emit_frontx.lean`;
`for f in Testing/asm/frontx-words/mon_*.cases; do python3 Testing/asm/frontx_test.py check 50 $(basename $f .cases); done`;
axioms: `Testing/scripts/axioms_y.lean`.

## 28. Strings as length + UTF-8 (branch `feat-utf8`)

The owner's layout (ROADMAP): **a `String` is its length in bytes, 8 bytes little-endian, followed by its UTF-8
bytes** (the format of `LList UInt8` in `Spec/Encode.lean`, no terminator, no tags).  It is the format of every
`String` field of a `frontx_ind_type` in input and output; in memory a string stays the chain of cells of
section 23 (`Bytes8`, one byte per cell), which is what the compiled functions (`Bytes8.eqb`, `Name.decEq`, ...) and
their proofs work on; only the decoder and the encoder of the program changed, proved once.

Example (`Riscv/Frontx/NameExamples.lean`, `decide +kernel`): `Name.str .anonymous "aλ"` is
`01 00 03 00 00 00 00 00 00 00 61 ce bb` (tag `str`, the prefix `anonymous` = tag `00`, the length 3, the bytes;
section 23's format was `01 00 04 61 04 ce 04 bb 03`).

**Stated in the Encode style** (`Riscv/Frontx/IndStr.lean`): `encString s = enc (BitVec.ofNat 64 s.utf8ByteSize) ++
s.toUTF8.data.toList`; `LString` (a string of fewer than `2^64` bytes, as `LList`) with `instance : Bytes LString`
(decoder: the length, then that many bytes that are valid UTF-8; `dec_enc` proved); examples for `""`, `"ab"` and NUL
+ 2-, 3-, 4-byte characters (`"\x00λ∀𝔸"`).  Per type the layout of its constructors: `NameT.enc_anonymous : NameT.enc
.anonymous = [0]`, `NameT.enc_str : NameT.enc (.str p s) = 1 :: NameT.enc p ++ encString s`, `NameT.enc_num :
NameT.enc (.num p n) = 2 :: NameT.enc p ++ enc (BitVec.ofNat 64 n)`.  The generic statement is `C.enc`
(`Compiler/Ind.lean`): a field `Fld.sl` / `Fld.sr` (the child `l` / `r` is a string) is `C.senc` = `leN 8 n ++
bytes` of the string's cells; `senc_ofString : (C.str st s.toUTF8.data.toList).senc = encString s`.

**What changed.**
- `Compiler/Ind.lean`: `Fld.sl`, `Fld.sr`; `C.str st L` (the cells of the bytes `L`: per byte `[st + 1, b, rest, z]`,
  then `[st, 0, z, z]`), `C.sb` (the bytes of a chain, read off the cells with a child), `C.senc`; `sTag sh =
  sh.length - 2`: string cells use **the shape's last two tags** (the front end puts `Bytes8` last); `C.wf` per child
  slot: `l.wf` if `Fld.l`, `l.IsStr (sTag sh)` if `Fld.sl`, `z` if neither (conjunctions, so a slot with both is
  consistent).  Decoder `dStr st d`: read the length (into `v_13`, `v_9` kept), allocate the end cell, then a cell per
  byte **from the last byte back** (children below parents, as `Rp` requires), cursor after the bytes; locals 13,
  14 (decoder frame 48 → 64 bytes).  Encoder `eStr p`: count the chain (`eCnt`, loop), write the count with `wrB 8`
  (`v_10` kept), then the bytes (`eBytes`, loop); locals 13-15 (encoder frame 56 → 72 bytes).  The stack bound of
  the statements (`8 (nl + 1) ≥ 136` per level) covers both, so no statement's space changed.
- `Compiler/IndStrOk.lean` (new): `dLoop_ok`, `dStr_ok` (the decoder of a string), `cnt_ok`, `bytes_ok`, `eStr_ok`
  (the encoder), `str_sb`, `IsStr.senc`.  `Compiler/IndBytes.lean` (new): the byte-reading/writing lemmas of
  `IndDec.lean` moved out (`At`, `rdB_ok`, `wr`, `wrB_ok`, ...).  `Compiler/IndDec.lean`: `dFlds_ok` / `eFlds_ok`
  with the two new fields.  `Compiler/IndMain.lean`: `nodes_le` per slot (`slot_le`, `str_le`: `n + 1` cells for
  `8 + n` bytes).  `Compiler/IndSup.lean`: `C.dec` / `decFlds` decode strings; `dec_enc`, `decIn_ok`,
  `al_le_cellsSup` take `length < 2^64` (an 8-byte length cannot describe a longer string), so `implements1_indM`'s
  cell bound is asked only for inputs below `2^32` bytes (`Riscv/Frontx/Ind.lean`; `IndMem.memoryNeeded_le` passes
  its `2^20`).
- Front end (`Riscv/Frontx/IndCmd.lean`): a `String` field is `.sl` / `.sr` in the shape; `Bytes8` is the last type
  of the shape (TExpr: the types after `Name` — `List Level`, `Literal`, `List Expr`, `Option Expr` — move down by
  two tags, the string cells are 28, 29); for `Bytes8`
  `T.Nk.emb_str : (emb t).IsStr off`, used by the other types' `emb_wf`.  New definitions in `wfDefs`.
- Shapes: `NameT` `[], [.l, .sr], [.l, .x], [], [.b, .l]`; `LevelN` `..., [.l, .sr], [.l, .x], [], [.b, .l]`;
  `TExpr` `Name.str` `[.l, .sr]`, `Literal.strVal` `[.sl]`.

**Not done.** `String.length` (Lean's is the number of characters, not bytes: needs the UTF-8 structure of
`String.utf8EncodeChar`, continuation bytes `10xxxxxx`, as a lemma; `utf8ByteSize` would be the chain length) and
string literals as constants (a constant chain `mk … (mk … nul)` in `E`, `=` with a constant side): neither was
cheap here.

Axioms: `Testing/scripts/axioms_utf8.lean` (`dStr_ok`, `eStr_ok`, `dec_ok`, `enc_ok`, `dec_enc`, the `Bytes LString`
instance, `senc_ofString`, `NameT.enc_str` / `enc_num`: propext, Classical.choice, Quot.sound).  Tests (QEMU + Sail
against executed Lean, `frontx_test.py check 60`): `name_beq`, `name_bbeq`, `level_beq`, `level_bbeq` (60 cases each;
the first 8 pairs fixed: `""`, NUL, `"𝔸"` (4 bytes), `"λ∀"`, `"é"`/`"e"`, `"x🙂y"`; the random names now also draw
4-byte strings), the 11 `expr_*` entries (60 each; `inst1` returns trees with strings, so the encoder is exercised),
and every other inductive-path entry re-emitted (their decoder/encoder code changed): all pass; the 25 run-time
memory entries (`emit_mem.lean`, `mem_test.py check 10`) pass.  Statement fingerprints: no `stmt` hash changed; the
`closure` hashes of `ind_ok` and every inductive-path `implements1` changed (C.enc, C.wf, decFn, encFn).

**State (round paused by the owner).** Done: layout, decoder/encoder proofs, front end, Encode-style statements,
tests above.  `bash Testing/scripts/check.sh` passed (ALL CHECKS PASSED) at `dbcc834` (after merging origin/main and
feat-expr); after that only `axioms_z.lean` → `axioms_utf8.lean` (check.sh list updated) and a ROADMAP-only merge of
origin/main — the re-run of check.sh was stopped by the pause, so run it once on resume.  Next steps: (1) re-run
check.sh; (2) optionally `String.utf8ByteSize` (the chain length, cheap) and `String.length` (needs a lemma on
`String.utf8EncodeChar`: count the non-continuation bytes); (3) string literals as constant chains in `E`
(Name constants like `Name.str .anonymous "Nat"`, `=` with a constant side); (4) small linter warnings (unused simp
arguments in `IndStrOk.lean`, `IndDec.lean`, `IndSup.lean`).

## 30. Paged dynamic arrays (branch `feat-paged`)

Software virtual memory beneath the spec (ROADMAP "Variable-size blocks"): arrays that grow (`push`, `extract`,
`Array.replicate`, copies) take fixed-size pages from a pool, so no fragmentation and `memoryNeeded` is exact in pages.

**Layout.** Pages of P = 1024 words (8 KiB; shift 10, mask 1023) at word 0 of the work block (`wheap[0]`), the frame
of the back end at the top of the work block.  Pool state in the registers `a4 .. a7` (middle-layer variables 4..7):
`vCap` = pool end in words, `vBump` = end of the pages handed out, `vFh` = head of the free list (linked through word 0
of each free page, no extra memory), `vOk` (1, or 0 once a request found no page).  An array = a size variable + one page
table page (up to P entries: at most 2^20 elements); element `j` is `W[W[pt + (j >> 10)] + (j & 1023)]`.  Every work
array owns its pages; arrays of the input stay read-only views (`inp`).
**Cost per access**: one load more than a flat array (page-table entry), and `srl; add; ld; and; add; ld` (2 loads, 4 ALU
instructions) instead of one `add; ld`; a `push` does the same for the store plus a check `size & 1023 == 0` and, on a
page boundary, one allocation (free-list pop or bump, no loop); there is no per-access bounds check beyond the
source's own (`a[i]!` guard).  Memory: one page table page per array (8 KiB) on top of `⌈n / 1024⌉` data pages.

**Entry** (`Riscv/Frontx/WpImpl.lean`): the code is `mv a4, sp` (the work block's end) followed by `compBFO` of the
program; the program starts with `cap := ((a4 - a2) >> 13 - 1) << 10` words (`capCode`: whole pages of 8192 bytes, one
page is left for the frame), `bump := 0`, `fh := NIL`, `ok := 1`.  Every later stage is guarded by `vOk`.  The
statement `Implements1Pg` (WpImpl) is `Implements1With` for ANY work length `L ≥ 8192` (not a fixed `space n`): the
output when the run fits (`fits a L`), and `a1 = 2^64 - 1` (output untouched, nothing outside output + work changed,
ABI registers kept) when it does not.  `memoryNeeded` (AllocSpec form, `WpMem.lean`): events `E.reverse ++ [.alloc 1]` (the
frame page comes first), cell size 8192, so `memoryNeeded = 8192 * (pk 0 E + 1)` and `fits ⟺ memoryNeeded ≤ L`
(`fits_iff_memoryNeeded`, `copy_fits_iff_memoryNeeded`, `lz_fits_iff_memoryNeeded`).

**Proved (no sorry, no new axiom; `bash Testing/scripts/paged_check.sh`, `axioms_paged.lean`).**
- `WpPool`: the pool.  `alloc_ok` (free list else bump, `vOk := 0` exactly when all `C` pages are in use), `free_ok`,
  `alloc_spec` (a returned page is a block of the work block meeting `AllocSpec` of `Compiler/AllocSpec.lean`).
- `WpRep` .. `WpPg`: get / set / push / new / free of a paged array, expressions (`WpExp`), in-place updates (`WpUpd`),
  loop bodies and whole loops with page events (`WpStmt`: `T.runP_ok`, stops with `vOk = 0` exactly when the events' peak
  exceeds `C`), fill loops (`WpFill`), fresh arrays (`F.compP_ok`: empty, replicate, extract, copy/view).
- `WpProg`: loop starts, programs: **`Pg.compP_ok`** (the loop stage was the open item): the code ends with the result and
  the page events (`Pg.GoodE`) within `C` pages, or with `vOk = 0` exactly when they exceed `C`.  (Fix found on the way:
  a scalar slot and an input-view slot had `pt = 0`, which `LoopLayP.p8` (`8 ≤ pt`) rejects, so no loop with a scalar
  state passed `Pg.wfP`; their `pt` is now `d + 1`.)
- `WpTop`: the whole programs `wholeS_ok` (scalar result) and `wholeA_ok` (array result through the page table:
  `outLoopP`, bytes of the elements to the output block, `a1` = their number), `capCode_ok`.
- `WpImpl`: `pg_core` (= `implements1_of_spec` for a work block of any length), `pg_of_spec` (the `mv a4, sp`),
  `pg_of_execOW`, `implements1_pgS` / `implements1_pgA` (a program with `Pg.GoodE` events, `wfP`, `wfB`).
- `WpMem`: `peak_pages`, `fits_iff_memoryNeeded`, `pgCompiled`, `memoryNeeded` of the examples.
- `WpBridge`: **`Pg.goodE_of_good`**: a word-array program (`wa_compile`, `Pg.Good`) without `push`/`extract`, constant
  `replicate` sizes and input views only is a paged program, with the events of its fresh arrays (`Pg.evsC`).

**Theorems and tests** (each: `Implements1Pg` machine theorem with exactly the Sail axiom set; the work block per input
is exactly `memoryNeeded` (run ok), one page less and one byte less than `memoryNeeded` (`a1 = -1`, output untouched); QEMU and
Sail, `python3 Testing/asm/frontx_test.py check N pg_<name>`, words and cases from `lake env lean Testing/asm/emit_pg.lean`):

| entry | what | theorem | memoryNeeded | cases (QEMU = Sail = Lean) |
|---|---|---|---|---|
| `copyE` | `ByteArray` grown by `push` (bytes + 1) | `PgEx.copy_implements` | `8192 (2 + ⌈n/1024⌉)` | 165 (n up to 70000) |
| `lzE` | `extract 0 16`, then LZ77 copy `out.push out[out.size - d]!` (reads the array it writes) | `PgEx.lz_implements` | `8192 (2 + ⌈(min 16 n + n)/1024⌉)` | 162 (n up to 20000) |
| `countLengthsE` | lean-zip `countLengthsFast xs.data 15` VERBATIM (Inflate.lean:536; `Array.replicate`, `set!`) | `LeanZip.countLengthsE_implements` | `24576` | 162 |
| `countLengths7E` | same, `maxBits = 7` | `LeanZip.countLengths7E_implements` | `24576` | 162 |

`copyE` / `lzE` are written directly as `Pg` terms (`WpEx.lean`, `WpEx2.lean`) with a hand proof of `Pg.GoodE`
(`copyPg_good`, `lzPg_good`: the loop's `RunsE` with its events `pushFrom`, the invariant, `okP`); the lean-zip entries
come from `wa_compile` (`WaLeanZip.lean`, unchanged) through `Pg.goodE_of_good`.

**Not done (and why).**
- **Verbatim lean-zip rows with growth** (`ByteArray.copyWithin`, `copyLoopGo`, `storedCopyLoop`, `fillDouble`, `Array.map` of
  fp-lean): `wa_compile` (`WaCmd.lean`) still rejects `push` / `extract` / `++` and `ByteArray` results (`A.ok` is `False` for
  `push`).  The paged back end handles `push`, `extract`, `replicate`, a read-while-write push (shown by `lzE`), but the
  front end that turns a Lean function into `Pg` + `Pg.GoodE` (with the capacity obligation `size < P * P`, `Prop`
  parameters of `copyLoopGo`, `k % distance`) is not extended; only hand-written `Pg` terms reach the paged back end.
  `nextCodesFast` (`F.alias` of a work array copies it: events depend on the array's size, `PlainP` rejects it),
  `kraftSumFast` (variable `*` needs `compBFC`, no paged variant), the Crc32 tables (`F.const`) are not covered either.
- `++` (append), arrays as parameters / results of inner functions (stages' arrays are `let`s / loop states only).
- **`a0` flag**: the status of `CompileRuns` / `CompileCorrect` (`Compiler/AllocSpec.lean`) is `a0 = -1`; the middle layer
  cannot write `a0` (`HeapB` keeps `a0` = the input base), so the flag is `a1 = -1`; to get `a0`, wrap the body in a
  stub that saves `ra`, calls it and sets `a0` from `a7` (`vOk`).  Work blocks below `8192` bytes are outside the
  theorem (the frame would not fit; the stub would have to test `sp - a2 < 8192` before the frame).  So there is no
  `compile_runs` / `compile_correct` for the paged compiler (the `IndMem.lean` pattern: `PgProg`, `compile`, events).
- Freeing at program level: `free_ok` / `freeArr_ok` exist; a loop's leftover work array (the state's other array) stays
  allocated (needs the final state in `RunsE`), so peaks may exceed the minimum for programs with several stages.
- Speed: not measured.

**State.** origin/main merged (Int, monads, strings, IR); `bash Testing/scripts/check.sh` ALL CHECKS PASSED (the statement
fingerprint WARNING comes from main's changes; not re-frozen).  Merge fixes: `E.ok` of casts gained `cast.side`, `mcmp`
takes the type, `Ty.int` in `AK` matches.  Next steps: (1) `a0` flag via a stub that saves `ra`, calls the body and sets
`a0` from `a7`, plus an `sp - a2 < 8192` test, then `compile_runs` / `compile_correct` as in `IndMem.lean`; (2) extend
`wa_compile` for `push` / `extract` / `++` and `Pg.GoodE` so the BAO rows (copyWithin, copyLoopGo, storedCopyLoop) compile
verbatim; (3) free a loop's leftover work array at program level.

**Session pause (WIP).** origin/main merged into feat-paged (NOTES conflict resolved keeping both; check.sh took main's
loop incl. feat-struct/harvest; paged check stays in `paged_check.sh`). Build cache restored, `lake build
Riscv.Frontx.WpImpl Riscv.Frontx.IndMem` passes (toolchain via elan, Lean 4.29.0). No new code yet for the goals.
Next: (1) `a0` stub in a new `Riscv/Frontx/PgMem.lean` after `IndMem.lean`'s `PgProg`/`compile` pattern: save ra, test
`sp - a2 < 8192`, call body, set `a0` from `a7`; prove `compile_runs`/`compile_correct`; (2) extend `A.ok`/`wa_compile`
in `WaCmd.lean`/`WaImpl.lean` for `push`/`extract`/`++`/`ByteArray` results via `Pg` + `Pg.GoodE`, then the four lean-zip
rows (copyLoopGo, storedCopyLoop, copyWithin, fillDouble) with `Implements1` and >=50 QEMU/Sail cases; (3) full
`check.sh` once at the end.

## 32. User structures (branch `feat-struct`)

Files: `Riscv/Frontx/StructExamples.lean` (lean-svg, list front end), `Riscv/Frontx/WaStruct.lean` (lean-zip,
word-array front end), `Testing/asm/emit_struct.lean` (words and cases), `Testing/scripts/axioms_feat-struct.lean`
(in `check.sh`'s list; `check.sh` now also splits `'LeanSvg…` lines). Changes in `Translate.lean`, `MulRep.lean`,
`WaCmd.lean`, `WaImpl.lean`.

**Targets** (rows of the target lists, verbatim; the source of each block is in the files):
- LEANSVG_TARGETS.md @ `origin/leansvg-targets` (lean-svg @ `df8e663`): §1.1 #107 `Rgba.mk` (Canvas.lean:16), #99
  `PngDecode.Hdr.mk` (PngDecode.lean:43); §1.2 #12, #13 `Canvas.h`, `Canvas.w` (Canvas.lean:24,25); §1.1 #14
  `Css.Compound.hasType` (Css.lean:54) and the other `Compound` fields; §1.5 #16-#23, #30, #34 `PngDecode.Hdr.w/h/
  depth/ctype/interlace`, `Rgba.r/g/b/a`, `Shape.GInfo.lig` (and `cp`, `gc`, `gprops`, `ngid`). Not in the lists but
  in the same blocks (Shape.lean:107-129): `GInfo.isIgnorable`, `ligNumComps`, `ligatedAndDidntMultiply`,
  `setLigForLigature`, `setLigForMark` (`{ g with lig := … }`, a 13-field result).
- LEANZIP_TARGETS.md @ `origin/leanzip-targets` (lean-zip @ `7e10583`): STR #1-#3 `DecodeTable.entryAt`, `lenAt`,
  `symAt` (Zip/Native/Inflate.lean:260, 228, 234; with `packEntry`, `unpackSym`, `unpackLen` :190-198 and the
  structure :221).

**What was missing, and the fix** (each a few lines; the first failures of the probes):
- *Constructor as a function* (`no unfolding equation for Rgba.mk`): `ctorEqn?` adds `C.mk.eqx : C.mk xs = C.mk xs`
  (`rfl`); the context's function name is cleared for a constructor, so its body is not a tail call of itself; `runs`
  uses `unfold … | skip`.
- *Projection as a function* (`recursive call not in tail position self.r`): the unfolding equation's body is the raw
  projection `self.1`; the test "is this field read" (`f.dropped`) compared it with the key `Rgba.r self` and dropped
  every field. `readsOf` normalises raw projections to projection functions and also unfolds non-recursive user
  helpers (to depth 8), so a field read inside a helper (`g.ligated` → `g.gprops`) keeps its variable (before, such a
  field was dropped and the translator looped between `GInfo.gprops g` and `g.7` until out of memory). A projection of
  a parameter without a variable is now a loud error. `isRecFn` is false for projections and constructors.
- *Fields that are not scalars* (`unsupported parameter type Canvas`; `unknown free variable` for structures with a
  `String` field): in a parameter (`resultComps (param := true)`), a field that is not made of scalars (`Array`,
  `String`, `Option String`, …) gets no variable; a proof field or one whose type depends on another field
  (`String.isValidUTF8`, the cause of the `unknown free variable` rows: its type escaped the local context) is skipped.
  A body reading such a field fails loudly ("a field of a parameter without a variable"). Results stay strict.
- Proofs of the `GInfo` tests: `a &&& b ≤ a, b` in `frontx_md_facts` (a temporary `x = u &&& 64` lost its bound), and
  0/1 tests with a negated side in `simp` normal form (`c_not_n`, `c_and_n*`, `c_or_n*`).
- *Word arrays*: `wa_compile` splits `let t : S := S.mk a…; b` into one `let` per field and reduces the projections
  of the constructor (`splitStructLet?`, `normPC`); a `dite` read `a[i]'h` in the result stage is closed with
  `← getElem!_pos, dite_eq_ite` (as in loop bodies); `Res UInt16` (2 bytes) for `UInt16` results.

**Compiled verbatim**: every library definition above by `frontx_compile` on the definition itself (source-level
`f.exec`, 3 axioms). **Machine theorems** (`Implements1`, the Sail set; QEMU + Sail vs executed Lean, 50 cases each,
all ok; entry glue reads the arguments from the input bytes):

| entry | library code exercised | result | words | test |
|---|---|---|---|---|
| `rgbaE` | `Rgba.mk` (Canvas.lean:16) | `Rgba`, 32 B | 169 | `st_rgba` 50 ok |
| `hdrE` | `PngDecode.Hdr.mk` (PngDecode.lean:43) | `Hdr`, 33 B | 242 | `st_hdr` 50 ok |
| `rgbaGE` | `Rgba.g` of a constructor | `Nat` | 61 | `st_rgbag` 50 ok |
| `interlaceE` | `PngDecode.Hdr.interlace` | `Bool` | 41 | `st_interlace` 50 ok |
| `canvasHE` | `Canvas.h` (an `Array Nat` field, no variable) | `Nat` | 73 | `st_canvash` 50 ok |
| `compoundValidE` | `Css.Compound.valid` (`String`, `Option String`, `Array` fields) | `Bool` | 42 | `st_compoundvalid` 50 ok |
| `setLigE` | `Shape.GInfo.setLigForLigature` (`{ g with lig := … }`, 13 fields) | `GInfo`, 104 B | 633 | `st_setlig` 50 ok |
| `ligNumCompsE` | `Shape.GInfo.ligNumComps` (+ `ligatedInternal`) | `Nat` | 85 | `st_lignumcomps` 50 ok |
| `isIgnorableE` | `Shape.GInfo.isIgnorable` | `Bool` | 72 | `st_isignorable` 50 ok |
| `rgbaHdrE` | tuple of two structures `Rgba × Hdr` | 65 B | 593 | `st_rgbahdr` 50 ok |
| `entryAtE` (wa) | `DecodeTable.entryAt` (Inflate.lean:260) | `UInt32` | 1323 | `wa_entryat` 50 ok |
| `lenAtE` (wa) | `DecodeTable.lenAt` (:228, `unpackLen`) | `UInt8` | 1315 | `wa_lenat` 50 ok |
| `symAtE` (wa) | `DecodeTable.symAt` (:234, `unpackSym`) | `UInt16` | 1325 | `wa_symat` 50 ok |

**Not done / why.**
- A structure *result* with an `Array` field (`Canvas.mk`, `Canvas.new`): the list front end has no arrays; the
  word-array front end returns a scalar or one array, not a structure. Splitting a structure result into its scalar
  fields and one array (one length in `a1`) is the natural next step.
- A table built from the input inside a structure on the word-array path: the later stages need a fact about the
  loop's result (`(fillW …).size = 256`) that `Pg.Good` does not carry (only the invariant of the states); a
  `result` clause (invariant of the returned value, proved from the loop invariant by `Runs` induction) would do it.
  The entries use a constant table (packed by lean-zip's own `packEntry`).
- `GInfo` with 13 fields from the input at once: `setLigAt` with 15 input-derived components took 8.6 GB and failed
  a `simp` heartbeat limit; with 5 input fields (the others the structure's defaults) 1.7 GB, 26 slots.
- Enum `instBEq….beq` rows of §1.2 (inductives without payload, not structures) and `deriving BEq` on structures.

Reproduce: `lake build Riscv.Frontx.StructExamples Riscv.Frontx.WaStruct`; `lake env lean --tstack=400000
Testing/asm/emit_struct.lean` (do not pipe its output into `head`: the `xs.data[0]!` panics of the empty input then
block it); `for f in st_rgba st_hdr st_rgbag st_interlace st_canvash st_compoundvalid st_setlig st_lignumcomps
st_isignorable st_rgbahdr wa_entryat wa_lenat wa_symat; do python3 Testing/asm/frontx_test.py check 50 $f; done`.
`lake build Frontx` (all earlier examples) passes with the translator changes.

## 31. con-leche blockers (branch `conleche-blk`)

**Done** (front end `Riscv/Frontx/IndCmd.lean`; `check.sh` ALL CHECKS PASSED on the branch merged with origin/main).
- (2) Constants of a declared type: `frontx_ind f on T` for a zero-argument `f` (`natAddName := natName.str "add"`) generates
  `f.cst (t : root) : ty := f` (the input tree is ignored) and compiles that; constants are unfolded in `reify`. String
  literals: `let x := nil; let x := T.lit.s<k>_<bytes> t x; …` over generated chunk functions (6 bytes each, once per literal
  and shape; one function body holds at most ~8 cells, because conditional branches reach 4 KiB: `bzOK`). Chunk functions are
  discovered through the arguments of recorded calls.
  `Riscv/Frontx/ConLecheBlk.lean`: the 40 `: Name` constants of the con-leche batch (@6810492c1, verbatim, file:line comments).
  Each: `f.cst.implements1` (axioms = the Sail set, `axioms_conleche-blk.lean`, entries in expected-axioms.txt) and 50 cases
  on QEMU and Sail equal to executed Lean (`Testing/asm/emit_conleche_blk.lean`, `blk_*`; all 40 pass).
- (1, partly) A non-recursive function whose body is a `match` is its own function (by cases). A match on a variable field of a
  constructor application (nested pattern `.const c []`) splits on the field the matcher is stuck on. `==` on declared types
  goes through `decide (a = b)` and `Name.decEq`.

**Not done.**
- `Expr.isBoolTrue` (nested pattern + `==` constant) now translates (5 functions) but its `sem` proof fails (the generic tactic
  does not case-split on the `List Level` field and does not evaluate the nested chunk-function calls). Same family: `isNatZero`,
  `natPred?`. `Expr.headIsProj` / `ioNeutral` (match on a call result): `sem` proof exceeds 16M heartbeats (> 15 CPU min).
  `peelPis`, `binderDom` (match on a `Nat` and an `Expr`): item (4). `rawNatLit?`, `piSortTeleLen?`: result `Option Nat`.
- (3) specialisation of one of two scalar parameters, (4) matches on two arguments: not started.
- Expr constants and `uN`/`vN`/`u1N` (helpers `bn`, `lm`, `cnst` with `String` parameters).
- statement_check warns (hashes changed by regenerated proofs/merge); not re-frozen, as instructed.

Batch functions now compiling through `frontx_ind` with theorem and tests from this branch: 40 (all `Name` constants).

## 34. IR stage S2: calls with frames, `switch`, the inductive path on the IR (branch `ir-s2`)

Design: `Testing/notes/IR_DESIGN.md` (branch `ir-design`) §4 stage S2, on top of S1 (`Ir.compile`, branch `ir-s01`).

**Back end with calls** (`Compiler/Ir/`, proved, any `Target`; RISC-V instance `rvT` in `Riscv/Back/IrTarget.lean`):
* `Target` gained `call` (`jal`), `enterC` / `leaveC` (frame below the caller's, cell 0 the return address), the
  out-of-memory `exit` (return through the stub's cell, `a0 := -1`) and `keepC`; RISC-V laws from `Riscv/Back/Call.lean`
  and `MemRv.lean` (no new Sail reasoning).
* Code (`Emit.lean`: `emitP`): a stub (check its two cells fit, else `a0 := -1; ret`; `enter 0` saves the caller's
  `gp`, `enterC 0` the return address; call `main`), every function (prologue `enterC n`, slots zeroed, parameters
  from `r0 ..`), the exit.  A call: arguments into `r0 ..`, check that the callee's frame fits above the heap (else the
  exit), frame limit down, `jal`; after it the limit back up and the results from `r0 ..` into their slots.  `ret`:
  results into `r0 ..`, `leaveC n`, `ret`.  `switch x ls d`: `r0 := x`, per index a compare-and-branch (long form when
  out of reach), then the default.  Layout of all functions by an untrusted fixpoint (`layout`), re-checked by `emitP`.
* Relation (`EmitStep.lean`): the top frame's `MR` in the context `C.fa n fb sv M` (slots at `fb`, cell 0 `sv`, `M` the
  memory above the frame as it must stay; `MR.above`), the suspended frames `Stk` (each at the code after its call, its
  slots in `M`), the cells in use `= cells + (top - fb) / 8` and the peak `≤ work / 8`.  `step_ok` (instruction, call,
  `jmp`/`br`/`switch`, return into the caller), `done_ok` (return of `main` through the stub), `sim`, `stub_ok`,
  `emit_ok`.  Out of memory at an `alloc` or a call is exact (`peak (events) > work / 8`).
* Allocation (`Rename.lean`): every function renamed (slot = position in its register list, untrusted; checked), with
  `slots` set; the simulation relates frame stacks (destinations renamed by the caller's choice); `alloc_runs`: same
  values and memory.  Fixed `Sem.lean`: a return assigns the RETURNING frame's destinations (it used the caller's).
* `Riscv/Back/IrTop.lean`: `Ir.compile`, `ir_compile_runs`, `ir_compile_correct` (same statements as S1, now for
  programs with calls; `memoryNeeded = 8 · peak (Lin events ++ [stub + main frame])`); `machine_run` takes the meaning
  only at inputs of at most `2^20` bytes (what `StartCorrect` allows).

**Inductive path lowered to RTL** (`Compiler/Ir/IndLow.lean`, definitions): cell = `alloc 4` + four `st`, `z` = word 0,
field read = test for `z` + `ld`, dispatch = `switch` on the tag, an arm that is a call on a child = jump to the entry
(loop), other calls = `call`, `ite` / `bind` in tail position continue in tail position; `dec` (recursive descent,
strings as length + UTF-8 bytes into chains of cells built from the last byte back) and `enc` (strings: count the cells
with a child, then their bytes) are RTL functions; `main` decodes, calls, encodes.  Generated through structured code
(`Compiler/Ir/Struct.lean`: `SC` / `TC`, flattened into blocks with fresh labels); `Compiler/Ir/StructOk.lean` proves
the flattening against big-step meanings (`flatS_ok`, `flatT_ok`) and the call rule (`reach_call`).

**`IndIr.compile`** (`Riscv/Frontx/IndIr.lean`, beside `IndMem.compile`, which is unchanged): `CompileRuns` /
`CompileCorrect` proved with exactly the Sail axioms (`Testing/scripts/axioms_ir-s2.lean`).

**The lowering is proved** (`LowerOk`, the `ind_rtl_ok` of the design; no condition left on the RTL side).  Files:
* `Compiler/Ir/StructLbl.lean`: the labels of flattened code are distinct (`flatS_fr`, `flatT_fr`: new blocks get the
  open label or fresh counter labels), so every region of `mkFunc` is found by `lookup` (`mkFunc_region`, the `GS.OkT`
  of `flatT_ok`); `rs3` = entry / one region per index / last region (the shape of `lowPg`, `decF`, `encF`).
* `IndLowMem.lean`: `Rv m v c` (a value is a pointer to a live 4-cell block `[tag, x, l, r]`, tag < 256, `z` the word
  0), `MLe` (input, block table, written cells stay), `mkCell` = `push4`, `fld`.
* `IndLowE.lean`: `lowE_ok` by induction on `E`: the code puts `ev` into `d` (`RvK`), grows memory, keeps the output
  and every register below `n` but `d`; hypotheses `Regs` (registers of the arm), `Binds` (`let` values by kind),
  `Calls` (recursive calls on children/grandchildren, later functions `ext j`, each "for any memory").
* `IndLowT.lean`: `lowT_ok` (an arm returns its value or jumps to the entry with a child: `TRes`), `pg_ok` (a function
  returns `Pg.sem`, by induction on the node's depth: the tail call is the induction hypothesis on the child).
* `IndLowDec.lean`: `rd8` (8 bytes little-endian), `decStr` (length + bytes into a chain of cells, from the last byte
  back: `str_loop`), `decFld_ok` / `decFlds_ok` (invariant `DInv`: a field register holds its value or 0 with no field
  for it; `wf` closes the gaps), `dec_ok`.
* `IndLowEnc.lean`: `put`, `put8`, `encStr` (count loop `cnt_loop`, bytes loop `byt_loop` = `C.senc`), `enc_ok`.
* `IndLowMain.lean`: `chain_ok` (each function `3 + i` returns its meaning, the later ones first, `Chain` + `okL`),
  `main`, **`lower_ok`**: `(lower …).meaning (inBytesA …) = some (Kd.out …)` for well-formed inputs of at most `2^20`
  bytes and outputs of at most `2^32` bytes (decision: the output cursor is a 64-bit word, so the bound is needed; a
  start state's output block lies in RAM, `ramEnd = 2^32`, so `IndIr` gets it from `StartCorrect.inRam` + `outputFits`).
* `compile` now checks `LGood` = `Chain` ∧ `IndLow.goodB` (shape < 255 tags, `okL`, fresh constructor tag < 256,
  `nb ≤ 8`): the conditions of `IndMem.compile` the lowering needs (not `WfMem`, so `pos_comp`, `tree_insert5`,
  `level_combining`, `level_simplify` are accepted).  `frontx_ind` entries have `Chain` by `rfl` (`{P}.X`);
  `Testing/asm/emit_ind_ir.lean` fails to elaborate an entry whose `goodB` is false.

**Tests** (`Testing/asm/emit_ind_ir.lean`: the RTL program of every inductive-path entry's `.code` arguments, its words,
per case Lean's result and `memoryNeeded` from a fast array interpreter checked against `Ir.interp`;
`python3 Testing/asm/ir_test.py check 50 <name>`): all 40 entries (the 29 of `emit_mem.lean` incl. `pos_comp`,
`tree_insert5`, `level_combining`, `level_simplify`, which the old route rejects (`WfMem`), and the 11 `expr_*`),
50 cases each (60 for `expr_*` where generated, tested 50) at `memoryNeeded` (output = Lean, `a0` = input address,
`gp`/`sp` restored) and `memoryNeeded - 1` (`a0 = -1`), QEMU and Sail, writes only in output + work.  Codes 300–1250
words (Expr 3270–3700; the old route 4150–5271): no inline heap checks, one check per `alloc` and per call.

**State (LowerOk proved):** `ir_test.py check 50` passed for all 40 entries incl. `expr_islit` (QEMU + Sail at
`memoryNeeded` and `memoryNeeded - 1`, after re-emitting with the `goodB` check: words unchanged);
`bash Testing/scripts/check.sh` ALL CHECKS PASSED (statement-fingerprint warning only, not re-frozen).  Next: switch
`frontx_ind` to the IR route (an `Implements1` from `IndIr.compile_correct` per entry, `Chain` by the `{P}.X` rfl).

## 35. Paged front end (branch `feat-paged2`)

**(1) `a0` flag, `CompileRuns` / `CompileCorrect` for the paged compiler (done; no sorry, no new axiom).**
- `WpTop`: `wholeS_ok` / `wholeA_ok` also give `vOk` (variable 7, `a7`) at the end: 1 when the pages fit, 0 when not.
- `WpImpl`: `pg_core` / `pg_of_spec` / `pg_of_execOW` take `Q : α → Nat → BitVec 64 → Prop` (a fact about `a7` at
  the return); `Implements1PgQ` = `Implements1Pg` plus `∃ v, a7 = v ∧ Q a L v`; `implements1_pgSQ` / `implements1_pgAQ`
  with `Q = okQ fits` (`a7 = 1` iff fits); `implements1_pgS` / `implements1_pgA` are their weakenings (unchanged
  statements).
- `PgMem.lean`: the entry stub `pgStub` (10 words): `t0 := (sp - a2) >> 13`; `t0 = 0` (no whole page) → `a0 := -1`,
  `ret` without running the body; else `mv s1, ra; jal ra, body; mv ra, s1; addi a0, a7, -1; ret`.  Decision: `ra`
  is kept in `s1` (the body keeps the callee-saved registers), not in the work block, so the body still gets the whole
  work block and `memoryNeeded` stays `8192 * (peak + 1)` exactly; cost: the stub does not preserve `s1` (the
  `AllocSpec` statements ask nothing of callee-saved registers).  `stub_run` (machine level, any work length, also
  below 8192), `stub_top` (from `StartCorrect`).
- `PgTop.lean`: `PgProg` (a `Pg [.ar .ba] R`, scalar or array result), meaning `PgProg.run` = `Pg.Den` (deterministic:
  `Pg.den_det`; `GoodE` runs agree: `Pg.goodE_den`), `compile` (stub ++ paged code, cells of 8192 bytes, events
  `E.reverse ++ [.alloc 1]` of the run's `GoodE` events, which are allocations only: `Pg.goodE_allocs`), `Good` (the
  checks of `implements1_pgSQ/AQ` + every input up to `2^20` bytes has a `GoodE` run).  **`compile_runs :
  CompileRuns riscv compile`, `compile_correct : CompileCorrect riscv compile`** (statements of
  `Compiler/AllocSpec.lean` unchanged).  Axioms: exactly the Sail set (`Testing/scripts/axioms_feat-paged2.lean`, in
  check.sh's loop).

**(2) Paged front end `wp_compile` (`Riscv/Frontx/WpCmd.lean`; reflection shared with `wa_compile` in `WaCmd.lean`
behind the flag `waPagedRef`, so `wa_compile` entries are unchanged).**  `wp_compile f max N (invariant P measure μ)*`
reflects `f : ByteArray → β` into `f.wa : Pg [.ar .ba] R` and proves `f.goodE : ∀ xs, xs.size ≤ N → ∃ E,
f.wa.GoodE [inLocP] 9 (xs, ()) (f xs) E` directly (no `Pg.Good` + bridge), then `f.pg : PgProg` (inputs up to `N`
bytes), `f.pgGood`, `f.compiles : compile f.pg = some …`, `f.computes : Computes f.pg (fun a : {xs // xs.size ≤ N} =>
f a.1) …`: with `compile_correct` / `compile_runs` the `AllocSpec` statements for `f`.  New in the reflection (paged
mode):
- a loop's `ByteArray` state that the loop changes starts as a copy (`F.extract m 0 m.size`); an array parameter the
  loop never changes, given an array of the environment, is that array (not state, no copy: the back end allows one
  work array per loop state);
- `let t := a.extract lo hi` (fresh array), `a ++ b` (a loop of pushes onto a copy of `a`, `appendGo`,
  `append_appendGo'`), `a.push x` at program level (`pushGo`), a computed array argument of a loop is named first;
  an array result that is a computed expression is named first;
- `Prop` parameters of loop functions (lean-zip's `hd_pos`, `hsd`) are not state: the loop's function is
  `if h : C then fn … h … else default` with `C` the conjunction of their types, discharged from the invariant
  (`wp_dif`, `wp_side`);
- `ByteArray.get!`; `WellFounded.Nat.fix` (single-argument WF recursion) recognised as recursion;
- programs with `mop` (`*`, `/`, `%` by variables, also `/` by a constant): the checked words `compBFC` with a register
  choice found by `pickC` (`PgProg.ch`, `implements1_pgSQC/AQC`, `pg_of_execOC`).
- `nat_types` (a definitional change of numerals / `≤` / `+` typed `Ty.nat.T` to `Nat`, so that `omega` reads them).

Back-end changes: **flat guards** (`WpFlat.lean`): each paged stage sat inside the previous stage's `vOk` guard (a
`loop` run once), so the outermost guard's body was the whole rest of the program and overran the 12-bit loop-exit
branch (`wfB`: bodies below ~1000 words; every multi-stage program failed).  `flatG` (fuel-indexed, structural, so
`decide` reduces it) rewrites `guard (A; guard B)` to `guard A; guard B`; `flatG_exec` (soundness, one direction is
enough); `pgProgS` / `pgProgA` are flattened.  **Scalar-result loops**: `LoopC` required the result location to be
the work array; a scalar loop's result location is now `rlNone = ⟨0, true, 0⟩` (read-only), so the condition is
vacuous (`WpProg`, `WpBridge`, proofs unchanged).  `Pg.evRun` (`WpRun.lean`): the page events computed with fuel;
`Pg.evRun_of_goodE`, **`memoryNeeded_eval`**: the memory the compiled code needs on an input is
`8192 * (pk 0 E + 1)` for the computed `E` (used by the test emitters).

**(3) lean-zip @7e10583 compiled VERBATIM (text copied with `file:line`, entry points fix the other arguments):**

| row | source | entry | file | max | QEMU+Sail |
|---|---|---|---|---|---|
| BAO `storedCopyLoop` | Zip/Native/InflateFast.lean:596 | `storedCopyE xs = storedCopyLoop xs xs (n >>> 1) 0 n` | `WpLeanZip2` | 2^20 | 114 |
| BAO `ByteArray.copyWithin` | Zip/Native/CopyWithin.lean:37 (the `@[extern]` attribute line left out; body copied) | `xs.copyWithin (n >>> 2) (n >>> 1)` | `WpLeanZip2` | 2^19 | 114 |
| BAO+PRFARG `copyLoopGo` | Zip/Native/Inflate.lean:710 | `copyLoopGo (xs.push 0) (n + 1 - (n % 7 + 1)) (n % 7 + 1) 0 n` | `WpLeanZip2` | 2^19 - 1 | 114 |
| ARR `kraftSumFast` (+`.go`) | Zip/Native/Inflate.lean:555 (with `countLengthsFast` :536) | `kraftSumFast (countLengthsFast xs.data 15) 15` | `WpLeanZip3` | 2^20 | 114 |
| ARR `nextCodesFast` (+`.go`) | Zip/Native/Inflate.lean:587 | `nextCodesFast (countLengthsFast xs.data 15) 15` | `WpLeanZip3` | 2^20 | 114 |
| ARR `countLongCodes` (+`.go`) | Zip/Native/InflateTreeFree.lean:94 (`fastBits` Inflate.lean:144) | `countLongCodes (countLengthsFast xs.data 15) 15` | `WpLeanZip3` | 2^20 | 114 |
| ARR `Huffman.Spec.nextCodes` (+`.go`) | Zip/Spec/Huffman.lean:83 | `nextCodes (countLengthsFast xs.data 15) 15` | `WpLeanZip3` | 2^20 | 114 |

Each entry: `f.goodE`, `f.pgGood`, `f.compiles`, `f.computes` (axioms: the Sail set for `pgGood` / `compiles`, the
standard three for `goodE` / `computes`; `Testing/scripts/axioms_feat-paged2.lean`).  Tests: `lake env lean
Testing/asm/emit_pg2.lean` / `emit_pg3.lean` write `pgs_<name>.words` (`pgs L`: the stub and the paged code) and
`.cases` (57 inputs, each at exactly `memoryNeeded` (`a0 = 0`, the result) and one page less (`a0 = a1 = -1`, output
untouched)); `python3 Testing/asm/frontx_test.py check 114 pgs_<name>` (the harness now also stores and checks `a0`
for `pgs` words).

**Not done (and why).**
- `ByteArray.fillDouble` (ExtendWithin.lean:48): the loop's state update is `seed ++ seed`, a loop inside a loop
  body; loop bodies (`T`) have no inner loops.  Needs nested loops in the IR / back end (or a proved rewrite of
  doubling into one flat loop, which would not be a general compiler step).  `extendWithin` / `copyLoop` call it.
- `hasLongCode` (InflateTreeFree.lean:176): `count[len]! > 0` compares a `Nat` element of a computed array; `E.ok`
  asks for `< 2^64`, which needs a fact about the earlier loop's result (`countLengthsFast`) that the generated
  invariants cannot carry from one loop to the next.  Also its nested `if … then true else go …` leaves a
  `Decidable.rec` the step tactic cannot invert.
- `fixedLitCount` / `fixedDistCount`, Crc32 tables: constant tables (`F.const`) are rejected by `F.wfP` in the paged
  back end; `Huffman.Spec.countLengths` takes a `List Nat` (no lists on the `wa` path); `fillSlots` needs `Nat`
  powers / nested loops; HuffTree (inductive) and tuples of arrays: not started.
- Reflection prints `Error: index out of bounds` (a `!` access in the meta code returning a default) for the
  entries with a dropped array parameter; the generated terms and proofs check (kernel), the source of the panic is not
  found yet.
- Compile time: each `wp_compile` with loops takes 3 to 6 minutes (the `GoodE` simp proofs and `decide +kernel` on
  `wfB` / `optB`).

**State.** origin/main merged (notes only); `bash Testing/scripts/check.sh` ALL CHECKS PASSED (the statement fingerprint
WARNING as before, not re-frozen).  QEMU + Sail: the 7 `pgs_*` entries 114 cases each (57 inputs at `memoryNeeded`
and one page less, `a0` and `a1` checked), the 4 older `pg_*` entries (regenerated after `flatG`) 120 cases each.
Next: nested loops in loop bodies (`fillDouble`, `extendWithin`, `copyLoop`); facts about an earlier loop's result in
a later loop's invariant (`hasLongCode`); constant tables in the paged back end; then HuffTree (`frontx_ind`) and tuples
of arrays toward `inflate`.

## 36. con-leche hard blockers (branch `conleche-hard`)

Front end only (`Riscv/Frontx/IndCmd.lean`); no change to `Compiler/`, the back end or `Spec/`.  Targets in
`Riscv/Frontx/ConLecheHard.lean` (con-leche @6810492c1, verbatim, `file:line` per block), each with `implements1`
(axioms = the Sail set, `Testing/scripts/axioms_conleche-hard.lean`, in `check.sh`'s loop and expected-axioms.txt)
and QEMU + Sail runs equal to executed Lean (`Testing/asm/emit_conleche_hard.lean`, `frontx_test.py check`):

| entry | con-leche function | source | feature | cases | words |
|---|---|---|---|---|---|
| `lift1 e c = liftLooseBVars 1 c e` | `Expr.liftLooseBVars` | `Kernel/ExprOps.lean:677` | (2) `amount` fixed | 81 | 6939 |
| `abs0 e k = abstract1 e 0 k` | `Expr.abstract1` | `Kernel/ExprOps.lean:739` | (2) `d` fixed | 81 | 6924 |
| `Expr.isStrLit` | | `Kernel/Core.lean:791` | (1) `.lit (.strVal _)` / `_` | 81 | 5706 |
| `Expr.isNatZero` | | `Kernel/Core.lean:1528` | (1) `.lit (.natVal 0)`, `.const c []`, `c == natZeroName` | 81 | 19896 |
| `Expr.isBoolTrue` | | `Kernel/CoreDefs.lean:449` | (1) `.const c []`, `c == boolTrueName` | 81 | 20718 |
| `peelN e k = peelPis k e` | `Expr.peelPis` | `Kernel/PropRead.lean:44` | (3) `0` / `k+1` with the tree, (4) `Option Expr` | 60 | 7960 |
| `domN e k = binderDom k e` | `Expr.binderDom` | `Kernel/PropRead.lean:51` | (3), (4) | 60 | 7960 |
| `hasLB e i = hasLooseBVar i e` | `Expr.hasLooseBVar` | `Kernel/CoreDefs.lean:810` | (already in the language) | 81 | 6269 |
| `Expr.sizeB` | | `Kernel/ExprOps.lean:719` | (already in the language) | 81 | 6281 |
| `Level.isNonZero` (on `LevelT`) | | `Kernel/Level.lean:181` | (already in the language) | 60 | 898 |

The last three were found by a gate run over all of `F2.lean.txt` (branch `conleche-depth`) with the new front end
(`gate_all`: every `ConLeche` definition whose type mentions `Expr`/`Name`/`Level`, through `frontx_ind_gate`'s
logic; 1319 definitions, 63 "arms ok"); they translated before this branch but had not been compiled.
Reproduce: `lake build Riscv.Frontx.ConLecheHard`; `lake env lean --tstack=4000000
Testing/asm/emit_conleche_hard.lean`; `python3 Testing/asm/frontx_test.py check 81 hard_<name>` (60 for `hard_peeln`,
`hard_domn`, `hard_isnonzero`); axioms `Testing/scripts/axioms_conleche-hard.lean`.

**(2) Specialisation.**  An entry `f xs = g … lit …` where `g` has two scalar parameters and one argument is a literal
that every recursive call of `g` passes unchanged (checked on `g`'s equations): `specialise` generates
`f.spec := fun rest => g … lit …` (a plain definition) and its equations `f.spec.eq_k`, one per `g.eq_k`, with
`g … lit …` replaced by `f.spec` — each proved by `g.eq_k` itself (the kernel unfolds `f.spec`).  Lean takes
`f.spec.eq_1 …` as `f.spec`'s equations (`getEqnsFor?` finds them as already generated), so the rest of the front end
sees a recursive function with one scalar parameter; the entry `f` is definitionally `f.spec …`, so the machine
theorem is about `f` (e.g. `lift1 p.1 p.2`).  `sem` proofs `simp` with `g` too (`simp [f.spec]` unfolds it).
Not done: specialising a parameter from the input (both scalars at run time), more than one fixed parameter.

**(1) Wildcards in nested patterns.**  `reifyMatch` on a constructor application stuck on a field: if no field
reduces the matcher for every constructor (`.lit (.natVal 0)` vs `_`), it splits on the first field of a declared
type or `Nat` (fields searched inside nested applications, `fvarsIn`); a `Nat` (parameter, field or local) splits
into `0` and `n + 1` with `n := natSub d 1` bound (`.bind`).  **Named constants inside a function** (`c ==
natZeroName`): a nullary constant of a declared type is now a call of a generated `cn.cst_<T> (t : T) := cn` on the
current node (one more program function, whose own `sem` states the value), unless the function is itself a constant
(`.cst`/`cst_`, as in §31: there the value is still unfolded).  The caller's proof (new last alternative of the
generated `sem` tactic): the later functions' meaning theorems are rewritten before the cells are unfolded, the
constants' `small` side conditions are discharged by unfolding the constants (`String` byte chains: `True` by
evaluation), `x == y` on a type whose `BEq` instance is `decide (x = y)` by a local `rfl` lemma (`simp` does not
rewrite instance arguments), `frontx_emb_cases` / `simp_all`, and `decide p = decide p` with different
`Decidable` instances by `congr`.

**(3) A match on a scalar together with the tree** (`| 0, e => … | k + 1, .forallE _ b => …`): the `Nat` split
above; the `sem` proof gets an alternative `rcases a with _ | a` (`ofNat_succ_eq0`: `n + 1 ≠ 0` below `2^64`).

**(4) `Option Expr` results.**  The existing `TExpr` shape DROPS fields of the root type in nested types: `some e`
is encoded as the bare tag (`TExpr.N6.emb (some e) = C.c 26 0 z z`) and `List Expr`'s heads are dropped too
(`N5.emb (e :: es) = C.c 24 0 (N5.emb es) z`).  No compiled function before this branch returned or took
`Option Expr`/`List Expr`, so no existing theorem was wrong, but such results would have been specified as their
shape only.  New option `frontx_ind_type (full) T := …` (marker `T.full`, also read by `rTyOfName`): such fields are
children.  Opt-in so that the codes and statements of every existing `TExpr` entry stay as they are; the new
`Option`-result entries use `TExprF` (byte format identical to `TExpr` for values without `List Expr`/`Option Expr`).

**Count.**  con-leche functions compiled verbatim through `frontx_ind` with a machine theorem: 71 before this branch
(68 named directly in `frontx_ind` commands — `IndExamples` 2, `Ind2Examples` 2, `NameExamples` 2, `ExprExamples` 8,
`ConLecheBlk` 40, `ConLecheS1`–`S3` 6, … — and 3 through entries: `looseBVarsBounded`, `instantiate1`, `wscopedB`),
now **81** (+ `isStrLit`, `isNatZero`, `isBoolTrue`, `liftLooseBVars`, `abstract1`, `peelPis`, `binderDom`,
`hasLooseBVar`, `sizeB`, `Level.isNonZero`).  (`Name.beq`/`Level.beq` of `NameExamples` are counted as in their files.)

**Not done / why.**
- `Expr.isEagerReduce` (`Kernel/CoreDefs.lean:440`, `.app (.app (.const c _) _) _`): translates (6 functions); the
  `sem` proof fails: after the case splits on the nested children, the generic `simp_all` unfolds the constant's cells
  (`eagerReduceName` = `.str .anonymous "eagerReduce"`) before the `Name.decEq` meaning theorem is applied, and
  `frontx_emb_cases` then generalizes the closed `Bytes8.ofString "eagerReduce"` (losing its value).  Tried (reverted,
  not in the tested front end): a variant of `frontx_emb_cases` that never generalizes closed terms, plus folding
  (`T.fold_k`) before rewriting with the later functions' theorems; the remaining goals were not closed.
- `Expr.natPred?` (`Kernel/Core.lean:1535`): translates; `sem` proof hits `maxRecDepth` in `simp`.
- `sameConstHeads` (`Kernel/CoreDefs.lean:148`, a match on two trees with `getAppFn` calls): translates (4 functions),
  `sem` proof fails (item 3 for two trees is not done; the two-tree arms are only translated through the `b` parameter).
- `Cached.iotaNumArgs` (`Cached/CoreC.lean:141`, accumulator `n + 1` with a wildcard tree pattern): `sem` proof fails.
- `openPisAtFvars` (`Option (List Expr × Expr)`: pair results), `rawNatLit?` (`Option Nat`), `instPisWith` (a pattern on
  the second argument, a `List Expr` structural argument with an `Expr` parameter): not attempted.
- Specialisation fixes literals only; a fixed parameter from the input (two scalars at run time) is not done.
- In the gate run, 167 of 1319 definitions fail with an `enableRealizationsForConst` error (realizing auxiliary
  constants from inside the command); not investigated (the generated `spec` / `cst_` definitions call it).

## 37. Round 1: compile-time constants, monomorphisation, translator gaps (branch `round1`)

Owner priority (ROADMAP "Next Opus rounds", BLOCKER_YIELD.md): con-leche + complete self-hosting. Every function below is
compiled verbatim (source copied from con-leche @6810492c1 with file:line comments, or the repository's own definitions).

### A. Compile-time constants as data (`frontx_const`)

* `Riscv/Frontx/Const.lean` (proved once): `dataB ys` = one byte store per byte into the output block, then `v1 := |ys|`
  (a `Mach.BStmt`, back end `compBF`); `data_implements1`: for every byte list `ys`, encodings `encA`/`encB` and value `c`
  with `encB c = ys`, the code implements `fun _ => c` (`Implements1With …  (fun _ => 15) maxLen retLen`; any input,
  ignored; work 15 bytes; `a1` = length). `wf_dataB` (well-formedness for every `ys`), `exec_dataGo` (the run).
* Kernel-reducible byte format: `C.sb` (bytes of a string cell chain) is well-founded recursion, which the kernel does not
  reduce; `sbS` / `encS` are the same functions by structural recursion, `enc_eq_encS` (proved once). A constant of a type
  declared by `frontx_ind_type` is checked as `encS sh (emb c) = ys` and turned into `T.enc c = ys` (`enc_of_encS`).
* `Riscv/Frontx/ConstCmd.lean`, `frontx_const f [on T]`: (1) `f` must be 0-ary (else rejected: "only 0-ary definitions are
  folded"; applications with arguments are never folded); (2) result encoding: `Nat` = 64-bit word (`encWord`, with the
  kernel theorem `f.data.lt : f < 2^64`), `Fin k` (`k ≤ 256`) one byte (`encFin`), a type of `T` its `enc`, else a
  `Bytes` instance; input: `T`'s root (`T.enc`) or raw bytes; (3) candidate bytes by evaluation (`Meta.evalExpr`,
  UNTRUSTED), at most `capBytes = 4096`; (4) the KERNEL checks `encB f = bytes` (`of_decide_eq_true rfl` added with
  `addDecl`, `Elab.async false`, `maxHeartbeats = kernelBudget = 50000`); failure = rejection, nothing generated.
  Generated: `f.data.enc_eq`, `f.data.bytes`, `f.data.code`, `f.data.implements1`.
* Rejections tested (`/home/user/scratch/t/c2.lean`, `c4.lean`, not committed): a function (`fn x := x`): rejected; `2^70 : Nat`:
  rejected (`f < 2^64` not confirmed); a value through `C.sb` (well-founded, does not reduce in the kernel): rejected;
  a fold over `List.range 30000`: kernel `deep recursion`, rejected. A well-founded definition that DOES reduce in the
  kernel (`go 10` by `termination_by n`) is folded (the kernel confirmed it). Caveat: a value whose kernel evaluation
  needs much memory (`List.range 3000000`) ran out of memory (OOM kill) before the heartbeat budget stopped it: a
  visible crash, not a wrong compile. The candidate evaluation (`evalExpr`) has no budget either; only the kernel check
  is trusted.
* `Riscv/Frontx/ConstExamples.lean`: 85 con-leche constants (the 40 `Name` constants of `ConLecheBlk.lean`, now also as
  data, and 45 more: `Name`, `Expr` (`natT`, `natRecMotive`, `natRecSucc`, `andRecMinor`, `quotLiftF`, …, the `BasisDSL`
  builders copied verbatim) and `Nat` (`whnfLoopFuel` = 2^62 and the other fuels, `satRange`, `bvarPoolSize`, …)) and the
  self-hoster's `Ir.R0`, `Ir.R1`, `Ir.RLim` (`Reg = Fin 15`, one byte). Codes 4–127 bytes of data. All 88:
  `f.data.implements1` with exactly the Sail axiom set; `f.data.enc_eq` ⊆ {propext, Classical.choice, Quot.sound}
  (`Testing/scripts/axioms_round1.lean`, in `check.sh`); 60 cases each on QEMU and Sail equal to executed Lean
  (`Testing/asm/emit_const.lean`, `cst_*`; all 88 pass).
* Callers. `frontx_ind` already unfolds constants inside bodies (section 31), so a caller compiled by `frontx_ind` uses
  a constant inline (recomputed). Folded constants are not yet callable as data from compiled functions (that needs the
  IR route: a call to a 0-argument function returning a pointer to a static block; next round, IR S3). Probe of three
  callers (`/home/user/scratch/p/callers.lean`): `Expr.isBoolTrue`: arms translate, `sem` proof fails (as in section 31);
  `Expr.isNatZero`, `Expr.isEagerReduce`: nested patterns (not supported). So none of the ~20 non-constant functions of
  the con-leche "0-ary" unlock set compiles yet; their blockers are nested patterns / `Option`/`List` results.

### B. Monomorphisation of type variables (`frontx_mono`)

* `Riscv/Frontx/Mono.lean`, `frontx_mono f at τ… on T [using U…]`: for `f : {ρ… : Type} → …` generates the specialised
  copy `f.at_τ (x_i : A_i[ρ:=τ]) : R[ρ:=τ] := @f τ… x_i…`, the equation `f.at_τ.eq : f.at_τ = @f τ…` (`rfl`), and runs
  `frontx_ind f.at_τ on T using U…`: the source of `f` is compiled through its own equations with the type argument fixed
  (the entry mechanism of `frontx_ind`). The command warns when a declared type drops a constructor field from its byte
  format (see the caveat).
* `Riscv/Frontx/MonoExamples.lean` (types: `Mach.IR.Tst Nat`, `Mach.IR.Ins Nat`, `Mach.IR.Arg Nat`, `Ir.Tst Nat`,
  `Ir.Block Nat`, `Option Nat`, `List Nat`): `Mach.IR.Tst.a/b/c`, `Ir.Tst.a/b/c`, `Mach.IR.Ins.dst` (result `Option Nat`),
  `Mach.IR.Arg.regs` (result `List Nat`), `Ir.Block.term/params/body` — 11 of the self-hoster's lowest blockers (all in
  the top 60). Each `f.at_Nat.implements1` (Sail axioms) and 60 QEMU+Sail cases equal to Lean (`Testing/asm/emit_mono.lean`,
  `mono_*`; all 11 pass).
* **Caveat (pre-existing, made visible):** `frontx_ind_type` leaves fields of types other than children, `Nat`, `UInt64`,
  `Bool`, `UInt8` out of the byte format (`Role.drop`). `Arg.i (c : BitVec 64)` is encoded as `[1]` for every `c`, and
  `Ins.lbu/sb/ld/sd` lose their `off`. The theorems above are correct but about encodings that forget immediates.
  Fix (next): a `BitVec 64` scalar kind in `IndCmd.Sc` (touches the field emitters and the `sem` tactics; every
  example's byte format with such a field changes, so the `.cases` files must be regenerated).
* Not done: recursive generic functions (the copy is an entry; recursion over `Code ρ` with `ρ := Nat` untested),
  `Ir.Func.*`, `Ir.Prog.funcs` (tuples `Lbl × Block ρ`).

### C. Translator gaps (minimal reproducers first)

* (ii) arity bug `invalid instantiateForall, too many parameters`. Reproducer (`/home/user/scratch/p/arity.lean`):
  `def g3 : UInt64 → UInt64 → UInt64 := HAdd.hAdd`, `def g1 (n : Nat) : Nat → Nat := Nat.add n`, a structure field of
  function type. Cause: `compileCmd` instantiated the unfolding equation (fewer binders) with all binders of the type.
  Fix (`Translate.lean`, `etaEqn`): `f.eq_eta : ∀ xs, f xs = rhs xs` by `congrFun`, used when the equation has fewer
  binders. Now `g3` compiles; `g1` is rejected properly (`Nat.add` on unbounded `Nat`); `E2.fp` (function field)
  rejected as `unsupported term self.1 a`.
* (iii) kernel `Sim argument has type Type 1`. Reproducer (`/home/user/scratch/p/univ.lean`): `structure W1 where S : Type;
  n : UInt64`, `frontx_compile W1.n`. Cause: a parameter in `Type 1` reached the simulation statement (`LOut A`,
  `A : Type`). Fix: every parameter must live in `Type` or `Prop` and the result in `Type`, else
  `frontx: unsupported parameter type W1 (it lives in Type 1 …)`. These rows (`Mach.Wide.lenBr`, `lenJ`, `maxSlots`, …)
  are fields of the record of laws `Mach.Wide : Type 1`: a correct rejection, not compilable data.
* (i) heads `ite` / `HAppend.hAppend` taken as entry calls (`frontx_ind`). Fix (`IndCmd.lean`, `notEntryHeads`): a body
  whose head is `ite`, `dite`, `cond`, `++`, `&&`, `||`, `!`, `==`, `decide` is not an entry `f xs = g c₁ …`; `f` itself is
  the function (by cases); `id` likewise. The entry body is now `v.beta xs` (was `instantiateLambda`: the same arity
  bug in `frontx_ind`). Reproducer `def shIte (t : Sh) : Sh := if true then t else .a 0`: compiles now; `def shK : Sh →
  Sh → Sh := fun t _ => t`: compiles now. `List.brecOn` / `Nat.brecOn`: not done
  (the functions are structural recursions over `List Nat` / `Nat`, not over a declared type; they need `List` as a
  declared type of the call and the `brecOn`-free equation lemmas).

### Ledger: probe rows re-run (round 1)

Commands as in the probes (`frontx_ind f on T [using …]` with the selfhost-depth2 type mapping, `frontx_compile f`),
`/home/user/scratch/p/P2c.lean` (not committed; regenerate with `mkP2.py`'s mapping over the rows below).

| rows (selfhost-depth2) | before | now |
|---|---|---|
| 23 P1 rows `invalid instantiateForall/Lambda, too many parameters` + kernel `Sim argument has type Type 1` (`Mach.Wide.*`, `Mach.Base.*`, `Ir.Target.lenCall/top/callOK`, `Ir.Env.*`, `Ir.Lay.posF`, `Ir.Func.σ`, `Op.toCtorIdx`, `Op.raw`, `WideF/MachineF.frameAt`) | crash / kernel error | 23 clean rejections: `unsupported parameter type` (records in `Type 1` or with function fields) or `unsupported term self.k a` (function-valued field) |
| 35 P2 rows: 28 `equation ite.eq_1 / HAppend.hAppend.eq_1 has no constructor pattern` + 7 `invalid instantiateLambda, too many parameters` in `frontx_ind` | head symbol unfolded as the function / crash | no row misreads its head or crashes any more; each stops at its real blocker: `unsupported parameter type` (12 + 6 of the 7: `Ir.Frame.regs`, `Mach.Wide.wenc`, `Ind.Pg.X`, `Ind.Cn.f/X/g`: records with function fields or `Type 1`), `no argument of a declared type` (12, scalar-only functions such as `vIdx`, `jW`, `liCode`), `unsupported result type` (3), `more than one scalar parameter` (1), `List.brecOn` (1, `Ir.setMany`) |
| self-hoster 0-ary `Ir.R0`, `R1`, `RLim` | `unsupported result type X` | compiled (`frontx_const`, data) |
| self-hoster `Mach.IR.Tst.a/b/c`, `Ir.Tst.a/b/c`, `Mach.IR.Ins.dst`, `Mach.IR.Arg.regs`, `Ir.Block.term/params/body` | `unsupported result type X ρ / List α / Option α` | compiled (`frontx_mono … at Nat`) |
| con-leche 0-ary constants (85: `Name`, `Expr`, `Nat`) | `has no argument of a declared type` | compiled (`frontx_const`, data) |
| con-leche `Expr.isBoolTrue`, `isNatZero`, `isEagerReduce` (callers of constants) | gate / arms fail | `isBoolTrue`: arms ok, `sem` proof fails; the other two: nested patterns. Not compiled. |

**Counts against BLOCKER_YIELD.md** (graphs and states of the two probes, the compiled functions above marked OK;
script: `Testing/dashboard/yield.py` with the unlock lists exported, `/home/user/scratch/yl.py`):

| | lowest blockers before | of them compiled now | in the top 60 | OK before → now | blocked functions now fully clear (whole closure OK) |
|---|---:|---:|---:|---:|---:|
| con-leche | 201 | 63 (all 0-ary constants) | 29 | 46 → 131 | 85 |
| self-hosting | 259 | 14 (11 monomorphised, 3 constants) | 14 | 31 → 45 | 14 |

Lowest blockers after round 1 (same rule, compiled nodes OK): con-leche 170, self-hosting 251. The 106 con-leche functions
that "0-ary constants" alone was predicted to unlock: 85 compiled (all constants of type `Name`/`Expr`/`Nat`); the other
21 are functions or constants of other types (`Array Expr`, `EqPair`, `NatBinOp → Name`, `Expr → Bool` with nested
patterns, `Option`/`List` results) and stay blocked. Self-hosting "translator shape": the crash classes (arity, universe,
`ite`/`++` heads) are gone from the rows above; none of those rows compiles yet, each now names a feature
(records of laws in `Type 1`, function-valued fields, scalar-only functions, `List`/`Nat.brecOn`).

**Blocked, and why.**
* Constants as callees from compiled code as DATA (not recomputed): needs a static data block on the IR route (IR S3).
* `BitVec 64` constructor fields are dropped by `frontx_ind_type` (see B, caveat): a new scalar kind is needed before
  the `Arg`/`Ins` results are fully informative.
* `List.brecOn` / `Nat.brecOn` rows (16 + 3): structural recursion over `List Nat` / `Nat` with the list not a declared
  type of the call; not attempted this round.
* Probe caveat kept: the con-leche edges are read from source text (BLOCKER_YIELD §5), so "fully clear" counts inherit it.

