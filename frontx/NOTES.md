# frontx: from list pipelines to ordinary recursive Lean definitions

Branch `frontx`, started from `9310b1a` (not tracking `main`). No existing file is changed.
Files: `Proven/Frontx/{Tree,Rep,Translate,Examples,Machine}.lean`, `asm/emit_frontx.lean`, `asm/frontx_test.py`,
`asm/arr-words/crc.words`, `frontx/NOTES.md`, `frontx/SURVEY.md`.

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
   and has no machine theorem.
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
Not built; the 340 `Id.run` defs of lean-svg depend on it.

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
