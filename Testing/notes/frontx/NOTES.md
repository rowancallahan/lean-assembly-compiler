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
