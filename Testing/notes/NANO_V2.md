# NANO v2: grow nano until its compiler is written in nano (branch `nano-v2`)

Goal (ROADMAP "DIRECTION", NANO_V2_ASTRA.md decisions, binding): ONE nano-written compiler for ONE frozen subset, compiled by
compiler 1 into B₁; B₂ = B₁(s), B₃ = B₂(s), B₂ = B₃; `ImplementsBytes B₂ Cκ` proved without compiler 1 in its dependency
closure. This file = (A) the plan (construct set, order, per-increment work, estimates, recompiles), (B) increment 1 as
done on this branch, (C) findings for the owner's spec review.

## A. Plan

### A1. What the compiler's own source needs (nano-friendly rewrite, Astra state shape)
Each stage is a byte machine over a state `(input, cursor, tokenBuffer, workStack, output, status)` with flat buffers and
token tags (no recursive ASTs, nested parsing with an explicit work stack). Concretely, per v1 stage:

| stage (v1 Lean) | what it does on bytes | constructs it needs |
|---|---|---|
| lexer `lexB`/`lexA` (Nano/LexS3.lean) | classify a byte (letter / digit / `( ) + - * ; : =`), span a word, keyword test, numeral value `a * 10 + d - 48`, column-0 rule | comparisons + `if` (class tests, keyword bytes), a fuel loop over the input, byte read at cursor, append to token buffer |
| parser 2a/2b (Nano/ParseS3*.lean) | recursive descent as a state machine with a frame stack (`Ctl`, `Fr`, `runS` on fuel) | fuel loop, `if` on tags, work stack = buffer (push = append, top = read at len-1, pop = shrink), small products for the state |
| inliner `inlB` (Nano/InlS3.lean) | def table (bodies as byte strings), copy a body per call, renumber variables | buffers with read-by-index + length, nested loops (copy loop inside the token loop), arithmetic on depths |
| expander `mexp` (Nano/ExpandM.lean) | one micro-op → a fixed chunk of records | `if` on the opcode, append of constants (buffer append), a loop |
| assembler `asm` (Nano/Asm.lean) | record `[op,a,b,c]` → 4 bytes by bit packing | shifts and masks (`>>>`, `<<<` by constants, `&&&`, `|||`), `if` on the opcode, a loop |
| driver | byte input → stages → byte output, error status | Result/status contract, capacities, I/O at the boundary only |

### A2. Minimal construct set and ORDER of increments (one construct per proved link)
1. **Comparisons + `if`** (`==`, `<`, `<=`; UInt64, Int64 kept but optional). DONE on this branch (part B).
2. **Bit operations**: `&&&`, `|||`, `^^^`, `<<<`/`>>>` by a numeral `< 64`. Needed by the assembler and byte packing.
3. **Fixed products**: `(a, b)`, `.1`/`.2` on nested `UInt64` products (state of loops; consuming decomposition rule).
4. **Fuel loops** (the ONE pattern of round 2: `def run (fuel : Nat) (s : St) : St := match fuel with | 0 => … | n + 1 =>
   if … then … else run n (…)`), lowered to a real loop (zero test, decrement, state update, backward branch). This is the
   increment that brings BRANCHING code; the branch-free `if` of increment 1 stays for pure expressions only (see B3).
5. **Buffers**: the approved `Array UInt64` wrapper API (create, size, checked/defaulted read, append / checked write),
   affine ownership check in the elaborator, functional semantics in `Prog.eval`, in-place code proved under ownership.
   Input bytes as a read-only buffer, output buffer serialized at the end.
6. **Result/status + capacities** (user program contract `Bytes → ok output | error code`, error ⇒ output length 0).
7. (only if measurements demand) **direct non-recursive calls** with frames, instead of inlining (inlining explosion).
Then: rewrite the five stages in the subset (one module per stage), bootstrap B₁ with compiler 1, fixed point.

### A3. Per increment: what changes
Columns: E = `nanoElab` (lexer/parser/inliner, i.e. the spec text side), M = `Prog.eval` (the spec meaning), G = code
generator (stack gen `genE`, records, `asm`), P = proofs (elaborator ⊆ Lean; compile correctness), S = stage compiles
(through S3, ≤ 5 min per module), est = effort for one box.

| inc | E | M | G | P | S (at the end of the group, ONE GO) | est |
|---|---|---|---|---|---|---|
| 1 cmp+if | tokens `if then else == < <=`, `if` at expression start, typing guard | `E.ite k a b t e`, `Cmp.test` | branch-free: X, c, Y, `X + c(Y-X)`; `<` by shifts+arithmetic; no new record | oracle fuzz + 20 agreement proofs; `genE_ok`/`genE_fail` `ite` case, `ops_ok`; families unchanged | lexA (new tokens), stage2b (new grammar/tags), inliner (new tag), mexp (new micro-ops = SOp chunks); asm UNCHANGED | done (~1 day) |
| 2 bits (DONE, part B6) | tokens `&&& \|\|\| ^^^ <<< >>>`, precedence (Lean: `\|\|\|` 55, `^^^` 58, `&&&` 60, `<<< >>>` 75), shift by numeral | `E.band/bor/bxor/shl k/shr k` | new records AND/XOR (R-type t0,t1), SLLI/SRLI t0 exist as families | oracle fuzz (precedence!), `bin_node` per op; new families + `case_r` with `G.step_and`/`step_xor` (exist) + `w_*` by `decide +kernel` | asm (new ops in X0..X3, ≤ 7 clauses per macro), mexp, lexA, stage2b | 1–2 days |
| 3 products | `(e, e)`, `.1`/`.2`, product types in signatures | values become trees of words (`V := w \| pair V V`) or flattened k-word tuples | k stack slots per value, `dup k`/`slide` generalised | `genE_ok` with k-slot values (Stk of lists of words); ownership not yet needed (no buffers) | stage2b, inliner (k-slot arity), mexp | 2–3 days |
| 4 fuel loops | recognise the ONE pattern (structural Nat fuel, tail calls only, predecessor fuel), reject everything else | `Nat` fuel as a word under a proved `< 2^64` bound; equations of the def | real branches: BEQ/BNE/JAL records with offsets (≤ ±4 KiB per branch, or JAL trampolines), loop = header + body + back jump; `if` lowered with branches inside loop bodies | record-machine loop invariant (induction on fuel); new Sail cases (`wB` step lemmas exist in Riscv/Steps/Branch.lean); `CodeAt` with jumps (pc arithmetic both ways) | all five (stage formats get loop tags) | 4–6 days |
| 5 buffers | wrapper API names only (closed prelude), affine ownership checker | functional `Array UInt64` semantics, capacities, checked reads (default 0) | buffers in the work block with a header (len, cap); append/read/write records (ld/sd with index registers) | memory invariant (buffer regions disjoint from the value stack), in-place = functional under ownership | all five | 5–8 days |
| 6 result/status | `Result`-shaped entry (status word + output buffer) | `Bytes → ok/error`, error ⇒ length 0 | exit sequence writes status, a1 = length (CompileCorrectL) | `ImplementsBytes` (round 3) | driver/linking | 2–3 days |
Then the rewrite of the stages in nano (one module each, ~1 week with 2–4 boxes), bootstrap + fixed point (~1 week).

### A4. Recompiles needed (ONE GO, not done on this branch)
- Increment 1 alone: the v1 self-hosted binary (`Nano.selfHosted`) is UNCHANGED and still proved; v2 lives beside it
  (`Nano.V2.*`). When v2 replaces v1 in the self-hosted chain: lexA (tokens `if then else == < <=`, the space rule),
  stage2b (grammar: `if` at expression start, the typing guard, the `Cmp` kind, the binder-group fix below), the
  inliner (an `ite` tag through the serialised format), mexp (the micro-ops of `SOp` chunks: `dup j`, `shr k`, `lit`,
  `slide`, `bin` already exist as record shapes) must be recompiled; asm needs NO recompile for increment 1 (no new record).
- Every later increment: see column S above. Per the ONE GO rule, all of them are recompiled together from one tagged
  revision at the end of the group, with `Nano.selfHosted` re-proved for the v2 language.

## B. Increment 1 on this branch: comparisons + `if`

### B1. Language (DRAFT spec, owner confirms): `Nano/V2Ast.lean`, `Nano/V2Elab.lean`
```
expr ::= 'let' x ':=' expr ';' expr | 'if' sum cmp sum 'then' expr 'else' expr | sum        (v1's grammar otherwise)
cmp  ::= '==' | '<' | '<='                    each followed by a space
```
- `if` only where `let` may stand (start of a def body, a `let` body, an `if` branch, inside parentheses): `x + if …` is
  rejected (Lean accepts it).
- `<`/`<=` are unsigned in a `UInt64` file, signed (Lean's `Int64` order) in an `Int64` file (`sgn`).
- TYPING GUARD (exact-subset rule): a comparison is accepted only if one operand is TYPED (contains a parameter, a call, a
  typed `let` variable, or a parenthesised `let`/`if` with a typed body/branch: `typed`). Reason, confirmed by the
  oracle: Lean elaborates an untyped comparison at `Nat` (`if 1 - 2 < 1 then x else y` is `x` in Lean, the words say
  `y`; `let z := 0 - 1; if z < 5 …` likewise).
- `Prog.eval` (`Nano.V2.den`): `.ite k a b t e ↦ if k.test (den a) (den b) then den t else den e`, `Cmp.test` = Lean's
  `==`, `<`, `≤` on `UInt64`, and on `UInt64.toInt64` for `lts`/`les`. v1 programs embed with the same meaning
  (`Nano.V2.eval_ofEx`).
- Fixed in v2 (v1 bug, see C1): a binder group needs at least one name.

### B2. Subset evidence (elaborator ⊆ Lean)
- Oracle `Testing/nano/oracle2.lean` (Lean's REAL frontend vs `Nano.V2.nanoElab` + `Prog.eval`), driver
  `Testing/nano/fuzz2.py N seed`: 105 hand-written boundary cases × {UInt64, Int64} (token adjacency `x<y`, `x<=y`, `=<`,
  `===`, `!=`, `>=`, `<-`, `<<<`, chained comparisons, missing `else`, `Nat` defaulting, numerals ≥ 2^64, 2^63 edges,
  unary minus, nested/parenthesised `if`, `if` in `let` values and branches, layout incl. `then`/`else` on new lines and
  column 0, `if1`/`iff`/`then1`, empty binder groups), the v1 corpus (v2 accepts it unchanged), random programs with
  `if` nodes and token mutations. Runs: seeds 1–5 (100 + 4×3000 random; seed 3 again and seed 5 after the fix): **0 "nano accepts, Lean rejects", 0 "meanings
  differ"** after the binder-group fix (seed 3 found it before). Table: `python3 Testing/nano/fuzz2.py 0 1 --table`.
- Per-program proofs `Nano/V2Agree.lean` (generated by `Testing/nano/gen_agree_v2.py`): 20 sources (UInt64 and Int64,
  all comparison kinds, nesting, calls, `let`, layout); each text is ALSO the Lean definition in the file; `elabEq`
  (`decide +kernel`) and `agree` (∀ inputs, the v2 program = Lean's function; Int64 on the bits). Two more sources agree in
  the fuzz but their generic `simp` proof does not close (listed in the generator).

### B3. Code generator (`Nano/V2Gen.lean`) and its proof
- Branch-free: `if a ⋈ b then t else e` = X, then c ∈ {0,1}, then Y, then `X + c·(Y − X)`, with (X, Y) = (e, t) for `==`/`<`
  and (t, e) for `<=` (`a ≤ b` = ¬ `b < a`). Correct because v1/v2 nano is pure and total (both branches evaluate, no
  effects, no non-termination). Cost: both branches run. NOT valid once branches contain loops/errors: increment 4
  brings branching `if` for those.
- `<` without new instructions: `a <u b = ((a>>1) − (b>>1) − (b&1)(1 − (a&1))) >> 63` with `x&1 = x − (x>>1)·2`
  (`Nano.V2R.ltu_bits`), signed = unsigned after adding 2^63 (`lts_bits`), `a == b` = `(a − b) <u 1`. Stack operations
  `SOp` (`dup j`, `shr k`, `bin k`, `lit n`, `slide k`) are short sequences of v1's records; **every record of
  `Nano.V2.genR p` is in v1's families** (`Nano.V2.af_genR`), so v1's Sail refinement is reused unchanged and `asm` is
  unchanged.
- Proofs: `Nano/V2Ops.lean` (`op_ok`, `ops_ok`, `ops_fail`, `ltu_run`, `lts_run`, `eq_run`, `sel_run`),
  `Nano/V2Rec.lean` (`genE_ok` = v1's plus `ite_node`), `Nano/V2Run.lean` (`genE_fail` with `ite_fail`, `genR_ok`,
  `genR_oom`), `Nano/V2Fam.lean` (`af_genR`), `Nano/V2Top.lean`:
  **`Nano.V2.nano_stack_correct : CompileCorrect riscv Nano.V2.nanoCompileA`** and
  **`Nano.V2.nano_stack_runs : CompileRuns riscv Nano.V2.nanoCompileA`**, for the `Program Nano.V2.Prog` instance
  (`Nano.V2.nanoRun`: 8-byte LE argument words, `Nano.V2.Prog.eval`, 8 LE result bytes). Axioms: exactly the Sail set +
  propext/Classical.choice/Quot.sound, the same list as v1's `Nano.nano_stack_correct` (checked by diff;
  `Testing/scripts/axioms_nano-v2.lean` is in check.sh's loop).
- Domain: `stackOk p = ScE p.2 p.1 ∧ depth p ≤ 256` as in v1 (each `if` needs up to 10 extra slots: `peakOps`).

### B4. Tests (QEMU + Sail)
`bash Testing/asm/nano_v2_test.sh` (emitter `Testing/asm/emit_nano_v2.lean`): 52 random/hand programs (all five
comparison kinds, nested `if`, `let`, calls, `&&& ||| ^^^`, shifts incl. amounts ≥ 64; up to ~40000 words) + 14 sources
through `Nano.V2.nanoElab` (min/max, abs, clamp, sign, digit test, bit packing; UInt64 and Int64), 8 inputs each around
0 / 2^63 / 2^64, three alignments (MIS 0,0 / 1,3 / 5,7), each at `memoryNeeded` (result == `Prog.eval`, QEMU == Sail)
and at `memoryNeeded − 1` (a0 = −1): **1584 program × input pairs ok** (increment 1 alone: 1344).

### B5. Build times (cold, `lake env lean`, deps built)
See the table at the end (filled from the measurement); all modules far below 5 min.

### B6. Increment 2: bit operations (same branch, after increment 1)
- Syntax: `a &&& b`, `a ||| b`, `a ^^^ b`, `a <<< k`, `a >>> k` (`k` a numeral `< 64`), each operator followed by a space;
  Lean's precedences (`|||` 55 < `^^^` 58 < `&&&` 60 < `+ -` 65 < `*` 70 < `<<< >>>` 75); `-n <<< k` rejected (prefix `-`).
  Meaning: Lean's `UInt64` operations (`BOp.app`; shifts by `k.toUInt64`, i.e. `k % 64`). In an `Int64` file `>>>` is
  rejected (Lean's `Int64` `>>>` is the arithmetic shift).
- SHIFT GUARD (found by the oracle, `Nano.V2.sm`/`good`): Lean's `<<<`/`>>>` are not `binop%` operators, and Lean
  REJECTS a `binop%` tree or comparison that mixes a shift with a numeral (`1 + x <<< 3`, `x + 1 + x <<< 3`,
  `1 < x >>> 63`, `3 * (let l := p <<< 63; p)`, a shift in an `if` branch or call argument inside such a tree), and a
  shift of an untyped operand (`255 >>> 31`, `let z := 1 <<< 3`). nano rejects: a tree of two or more leaves with a leaf
  that contains a shift anywhere AND a leaf that is not a typed variable / call / shift; a shift whose operand is untyped.
  This is conservative: Lean's verdict depends on the leaf order (`x <<< 7 ||| 3` and `x >>> 63 == 1` are accepted by
  Lean, rejected by nano).
  Workaround for constants next to shifts: a zero-arity def (`def c : UInt64 := 3`, a call leaf).
- Code: `|||` = v1's OR record (`binop 14`), shifts = v1's SLLI/SRLI records, `&&&` = `(a + b) − (a ||| b)`, `^^^` =
  `(a ||| b) − (a &&& b)` (`Nano.V2R.and_eq_add_sub_or`, `xor_eq_or_sub_and`, from core's Nat bitwise lemmas); every
  record still in v1's families, `asm` unchanged. `Nano.V2.nano_stack_correct` re-proved for the extended language, same
  axioms.
- Evidence: fuzz2 (69 bit-op boundary cases × 2 types + random programs with bit ops) seeds 11–13 and 21–23 (2000 random
  each): 0 differences after
  the shift guard (before it: 6–20 "nano accepts, Lean rejects" per seed, all shift typing); 25 agreement proofs
  (5 with bit ops); QEMU + Sail: see B4 (rerun with bit-op programs).

## C. Findings for the owner (spec review)
1. **v1 bug (exact-subset violation, NOT fixed in v1)**: v1 `nanoElab` accepts an empty binder group, e.g.
   `def g1 ( : UInt64) : UInt64 := 5` and `def g1 (x : UInt64) ( : UInt64) : UInt64 := 5`; Lean rejects both (oracle,
   2026-11-17). NANO.md says empty binder groups were fixed, but `pParams`/`pNames` accept `( : T)`. Not changed here:
   v1's `nanoElab` is the spec the five self-hosted stages are proved against (changing it means recompiling them).
   Fixed in `Nano.V2.nanoElab`. Fix v1 at the next ONE GO, or state it in `Nano.selfHosted`'s domain.
2. Int64 comparisons are in (cheap: the kind is chosen by the file type); Astra round 2 says "skip Int64 unless needed".
   Owner decides whether the frozen subset keeps them.
3. Rejected on purpose (nano may reject): `>`, `>=`, `!=`, `=`, `x<y` without the space, `if` as an operand without
   parentheses (`x + if …`), `(x < y)` parenthesised conditions, untyped comparisons, `then`/`else` at column 0.
4. The branch-free `if` makes `Prog.eval`'s `ite` (lazy, Lean's) and the code (eager) agree only because nano has no
   effects; the plan (A2.4) replaces it by branching code inside loops.

## check.sh
2026-11-17 on nano-v2 (after merging origin/main 97b0907): ALL CHECKS PASSED (only the pre-existing statement-fingerprint WARNING, on
Frontx statements not touched here; not re-frozen). `Nano.V2.*` axioms appended to expected-axioms.txt.
Again after increment 2 and merging origin/main 0128534 (nano v1-S3 FINAL, Astra rounds 4–5): ALL CHECKS PASSED (same
pre-existing WARNING only).

## Build-time table
`/usr/bin/time timeout 10m lake env lean Nano/<m>.lean` (deps built; seconds, peak memory):

| module | time | memory |
|---|---|---|
| V2Ast | 1.0 s | 0.5 GB |
| V2Elab | 1.0 s | 0.5 GB |
| V2Gen | 0.5 s | 0.5 GB |
| V2Ops | 5.5 s | 0.7 GB |
| V2Rec | 11.0 s | 0.9 GB |
| V2Run | 8.2 s | 0.7 GB |
| V2Fam | 3.2 s | 1.7 GB |
| V2Top | 4.5 s | 1.8 GB |
| V2Agree | 34.6 s | 2.9 GB |
(after increment 2; all far below 5 min.)

## HANDOFF (2026-11-17, worker 1 → merged worker-1/2 box)
DONE (branch nano-v2, check.sh passed, all pushed):
- Increment 1 (`==`, `<`, `<=`, `if`) and increment 2 (`&&&`, `|||`, `^^^`, `<<< k`, `>>> k`): `Nano.V2.nanoElab`,
  `Nano.V2.Prog.eval`, branch-free stack generator on v1's records (`asm` unchanged), `Nano.V2.nano_stack_correct` /
  `nano_stack_runs` (v1's axiom set), oracle fuzz 0 differences, 25 agreement proofs, QEMU + Sail 1584 pairs.
- NANO_V2_SPEC.md = the owner's working freeze (aligned with NANO_V2_SKELETONS.lean / ROUND5).
NEXT (worker-1 side, in spec order):
1. Elaborator: the fuel-loop pattern (both `match fuel with` + `termination_by structural fuel` and the equation form
   `def f : Nat → … | 0, … | n + 1, …`), Nat fuel expressions (`len' xs`, `+`, `*`, numerals), oracle-checked.
2. Elaborator: types `List UInt8` (input, output) and `Array UInt64`, prelude ops (`rd`, `len`, `put`, `readD`,
   `writeChecked`, `appendChecked`), the affine ownership check, `&&`/`||` in conditions, `≤`.
3. `Prog.eval` for loops/buffers (functional, fuel recursion) and the ONE-SOURCE certificate generator
   (NanoProofs.Meaning pattern); `Nano/V2/ABI.lean` from `NanoABI.ImplementsBytes`.
4. Backend: replace the branch-free `if` by worker 2's branching backend (`Nano.V2B`, branch nano-v2-backend) for
   loops/buffers; translate `Nano.V2.E` into it or adopt it as the shared AST (one owner).
OPEN PROBLEMS:
- v1 `nanoElab` accepts empty binder groups `( : UInt64)` (C1); fix at the next ONE GO.
- Shift guard is conservative (rejects `x <<< 7 ||| 3`, which Lean accepts); worker 3's asm style needs constants as
  zero-arity defs or a typed-ascription construct `(n : UInt64)` (not in the subset yet).
- Two agreement sources do not close with the generic tactic (listed in gen_agree_v2.py); the Int64 meaning has no
  `denI` for v2 (Int64 dropped for milestone 1 anyway).
- Increment 3 (products): NOT started; no code exists.

## MERGED BOX (workers 1+2), 2026-11-17: increment 3 (products)
- Merged `nano-v2-backend` into `nano-v2`. DECISION: ONE AST = worker 2's typed `Nano.V2B.Ex`/`Tl` (Nano/V2/Lang.lean);
  the increment-1/2 path (`Nano.V2.E`, v1 records, `nano_stack_correct`) stays as the proved link for pure words.
- Front end `Nano/V2/Front.lean` (`frontElabK κ`, `frontElab` = κ 65536): surface AST `S` (calls kept, for the guards),
  lowered to `Ex` with calls inlined (`let` chains, `Ex.lift`). Products: `T × T`, `(a, b)` / tuples, `.1`/`.2`,
  `let (a, b) := e;`. I/O prelude: `rd x i`, `len x`, `put o b`, `[]` (output = buffer `mk κ`). Main = last def
  `def m (x : List UInt8) : List UInt8`; empty output ↦ status 1. Rules: input = a def's first `List UInt8` parameter;
  every pair component TYPED; conservative ownership (a buffer-holding variable occurs ≤ 1 time, larger `if` branch);
  declared types checked with `tyOf` (bodies, call arguments); v1 identifier rule; shift guard ported.
- Proof `Nano/V2/Comp.lean` **`Nano.V2B.cE_ok`**: `cE` correct on the loop-free, buffer-free fragment `Ex.Pure`
  (words, bin, ite, let, pair, fst, snd, split, isize, iget): typing (`Val.HasTy`) + run (`Post` with `Val.flat`)
  from `EnvRep`. Axioms propext/Classical.choice/Quot.sound; module < 3 s. `cE` now also checks `ρ.size ≤ Lim` in
  `let_`/`split` (the slide's 12-bit offsets).
- Tests: `Testing/nano/v2f/fuzz.py N SEED` (random product programs vs Lean `#eval`; hand cases p*.lean; negatives
  neg*.lean must be rejected): 101 programs × 12 inputs agree, 7 negatives rejected (local). `EMIT=1` writes
  `nv2f_*` words/cases for `v2b_test.py` (QEMU + Sail).
- NOT yet: machine-level theorem for a whole front-end program (needs buffers: the output is a buffer, increment 5).

## Increment 4 (fuel loops), merged box
- Front end: the equation form `def f : Nat → T₁ → … → R | 0, x₁, … => e₀ | n + 1, x₁, … => e` (zero arm first;
  input = first parameter if `List UInt8`; ≥ 1 state parameter); self calls `f n a₁ …` only in TAIL position (`if`
  branches, after `let`/`let (a, b) :=`), fuel exactly `n`; any other use of `f` is rejected (unknown name). Lowered
  to `Ex.loop fuel (a₁, (a₂, …)) z t` with the state unpacked by `split`s (`unE`/`unT`, scope `bScope`). Call sites:
  `f FUEL x a₁ …`, FUEL = `len' x`, numerals < 2^32, `+`, `*`, parentheses (word value = Lean's Nat iff < 2^64: the
  admitted-domain condition). The `match fuel with` form: NOT yet.
- Proof: `cE_ok` + `cT_ok` (mutual, Nano/V2/Comp.lean) now include `Ex.loop` and every `Tl` form: invariant at HEAD =
  fuel word `ofNat n` + state words over the frame, `run … n st = V`, `Keep`; instance of worker 2's `loop_ok`.
  `cE` gained `ρ.size ≤ Lim` checks (loop exit and `ret` slides). Axioms propext/Classical.choice/Quot.sound, 4.4 s.
- Tests: fuzz.py generates random loop helpers too (+ hand cases p2/p3, negatives neg8–11: non-tail self call,
  fuel ≠ n, aliasing through a loop, fuel variable used as a value): 83 programs × 12 inputs agree, 11 negatives
  rejected (local).

## Increment 5 (buffers), merged box — front end
- Prelude (§3, the `List UInt64` version): `Buf`, `bnew`, `bsize`, `bget`, `bset`, `bpush` ↦ `mk κ`/`size`/`get`/`set`/
  `push` (meanings equal: `getD … 0`, `List.set` = `lset`, append). `bpop` not added (no stage needs it yet).
  §8's `Array`/`writeChecked`/`appendChecked` form: NOT implemented (the `List` prelude maps 1:1 to the backend).
- Front-end types `FT` (`w | out | buf | prod`): the output `List UInt8` and `Buf` are both `Ty.buf` in the backend but
  distinct in Lean; `S.ty` checks bodies, `let`s, call/loop arguments, tails; `tyOf`/`tyT` re-check the lowered term.
- OWNERSHIP = liveness in evaluation order (`Ex.lv`/`Tl.lvT`): a buffer-holding variable is consumed by every use
  except a borrow (`bsize v`, `bget v i`, and `v` in `bset v i x`/`bpush v x`/`put v x` while `i`, `x` run); a dead
  variable may not be used; `if` = union of the branches' dead sets; loop bodies may not touch outer buffers.
  Conservative: a buffer MOVED (into a pair / loop state / `let`) is dead even if not mutated, so write
  `let v := bget b i; f n (i + 1, b) (put o v)`, not `f n (i + 1, b) (put o (bget b i))`.
- Tests: p4 (histogram, `(i, Buf)` loop state), p5 (bubble sort), p6/p7; negatives neg12–16 (use after `bset`,
  use after `bpush`, `Buf` vs `List UInt8` both ways, aliasing through a pair): 67 programs × 12 inputs agree.
- Back-end proof for buffers: NOT yet (next: BufferRep/SameOutside, NANO_V2_SKELETONS.lean `Buffers`).
