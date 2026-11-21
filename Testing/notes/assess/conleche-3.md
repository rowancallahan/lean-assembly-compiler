# con-leche, slice 3 of 3 (assess-03)

Repo `leanprover/con-leche` @ `cd2ecea`, toolchain `v4.36.0` (`lean-toolchain`). Clone OK (no network block). Not built.
Split: `git ls-files '*.lean' | LC_ALL=C sort` = 1 146 files / 308 209 lines; last third starts at cumulative line 205 473
(file `ConLeche/Verify/Denote/OpenRevDenote.lean`). **Slice = 636 files, ~102.7k lines.** Counts below are grep-based (approximate).

## 1. Size and content
| part | files | lines | theorems | defs/abbrevs | inductive/structure/class |
|---|---:|---:|---:|---:|---:|
| `ConLeche/Verify/**` (rest of it, from `Denote/OpenRevDenote`) | 127 | 56 323 | ~2 545 | ~349 | ~82 |
| `whitepaper/Fragment/**` | 52 | 30 755 | ~1 366 | ~271 | ~58 |
| `tests/e2e/src/*.lean` (+ ndjson inputs, 35 MB) | 338 | 9 885 | | | |
| `tests/ConLecheTests*`, `tests/olean`, `scripts`, `pinners`, `bridge`, `Main.lean`, `lakefile.lean`, `PinDump`, `OleanCompare` | ~110 | ~5 800 | | | |

- **This slice is ~93 % proof, not program.** Whole slice: ~4 300 `theorem`/`lemma`, ~1 950 `def`/`abbrev`; 5 697 `by` blocks, `simp` 8.9k, `omega` 1.6k.
- `ConLeche/Verify/*` proves things about the checker defined in the other two slices (`ConLeche/Kernel`, `Cached`, `Frontend`, `Driver`): subst/shift/infer/whnf lemmas
  (`InferLemmas.lean` 2 981 l., `Subst.lean`, `Shift.lean`), the `.olean` reader (`Frontend/Olean/*`, 16 files), the NDJSON parse/rounds (`Frontend/Rounds*.lean`, `Local`, `Chunks`), inductive-block checks (`Inductives/*`, 35 files), driver (`Driver/Main.lean`, `Driver/Oleans.lean`).
- `whitepaper/Fragment/*` is a **separate, smaller proof model** (own `Syntax`, `Env`, `Rules`, `Sound.lean` 2 306 l.; `NestIota`, `IndSem`, `InstallInd`…) for the Typst whitepaper. It checks a "fragment" of the logic, never the shipped code. Only `import Lean`-free `Fragment.*` + `Init`/`Std`.
- Executable/Lean-program code in the slice is small: `Main.lean` (103 l., `IO`, `Std.Async.System.setEnvVar`, exit code), `PinDump.lean` 70, `OleanCompare.lean` 206, `scripts/*.lean` (5 files, 460 l., meta-programs, `partial def`), `tests/ConLecheTests*` (`#guard` tests, 2 565 l.).
- **Program** (whole repo, from `OVERVIEW.md`): `con-leche [--verified|--trusted] [--jobs=n] FILE.ndjson` or `--olean --search-path=DIR… MODULE…`; input = a `lean4export` NDJSON stream (or `.olean` files) → one verdict line + exit code 0 accepted / 1 rejected / 2 declined / 3 error. Entry: `Main.lean` → `ConLeche.Driver.runArgs` (`ConLeche/Driver/Cli.lean`, other slice).

## 2. Lean features in this slice (counts / examples)
| feature | count | where | needed? | cheapest encoding |
|---|---:|---|---|---|
| theorem/lemma, tactic proofs | ~4 300 | everywhere | proof only; erased | **none: not compiled** |
| `List` | ~6 500 mentions | specs/lemmas over `List UInt8`, `List Expr` | mostly spec-side | in compiled code: Buf |
| `Nat` | ~6 000 | indices/sizes (`Emit.lean`, `Local.lean`) | needed in executables as indices | UInt64 + assert `< 2^63` |
| `Option` / `Except` | ~1 000 / ~900 | `CheckM`-style results (`Frontend/ModelIO.lean`, `ExceptBind.lean`) | core to checker | tagged result in Buf / status word + abort |
| `Array`, `ByteArray` | 524 / 336 | `Olean/Reads.lean`, `Prefix.lean`, `Rounds.lean` | core (parse of byte input) | Buf of bytes/words |
| `String`/`Char` | 183 / 47 | `Driver/Main.lean:37` `parseArgs`, names | incidental in slice | bytes in Buf |
| `UInt64`/`UInt8`/`USize` | 311 | `Region.PtrOk`, `Seg.hit` (`Olean/*`, byte-level reads) | **already in subset** | direct |
| `IO` / `do` | 178 / 371 | `Main.lean`, tests, scripts | `Main.lean` only | byte-in/byte-out loop |
| `StateT`/`StateM` | 0 here (in other slices via `CheckM`) | | | state-passing explicit |
| `mutual` | 61 | proof-mutual (`Sound.lean`) | spec-side | – |
| `termination_by` / `decreasing_by` | 6 / 3 | few | – | fuel loop |
| `partial def` | 6 | only `scripts/*`, `tests/.../ScanTests.lean:124` | incidental | not needed |
| `unsafe`/`@[extern]`/`@[implemented_by]` | 0 real in `ConLeche/**`; `lakefile.lean:199` mentions `natHash` extern as a *PR plan*; `pinners/*/Kernel/PtrDecEq.lean` uses `withPtrEq` | pointer-equality caches | optimisation, droppable |
| macros/notation/syntax | ~180 | proof-side notation; `tests/trust-surface`, scripts | spec-side | – |
| `HashMap`/`HashSet` | 38 | `Emit`/`Mark` visited sets (`Olean/Emit.lean`) | core (dedup of constants) | open-addressing in Buf |
| `Int`, `Float` | 12 / 0 | – | – | – |
| `sorry` | 0 in `ConLeche/**` (hits are test fixtures `tests/e2e/src/*.lean`) | | | |
| `axiom` | 0 in `ConLeche/**`; fixtures only (`tests/olean/src/*`) | | | |
| `native_decide` | 0 in proofs; fixtures `tests/e2e/src/native_decide_axiom.lean` | | | |
| imports | `ConLeche.*` 458, `Fragment.*` 147, `Lean` 91, `Init` 42, `Std` 6, `Lake` 5, `Mathlib` 3 (fixtures only) | | | |
- Positive: **no Mathlib, no axioms/sorry in the proved code**; permitted axioms (`comparator.json`) are only `propext`, `Classical.choice`, `Quot.sound`.

## 3. Hard blockers (ranked, for compiling this slice's *programs*)
1. **There is almost nothing to compile here**: 93 % of the slice is theorems. The slice's value is the proof side (see §7), not code to accept. The checker code it talks about lives in slices 1–2.
2. **The programs these proofs are about use `Expr`/`Name`/`Level` inductives, `Option`, records, `HashMap`, `CheckM` monad, higher-order `CoreFns` record** (`CONLECHE_DEPTH.md` §2, rows 1–11: 6 of 1 093 probed functions compiled with the old front end). Same blockers apply to the nano v2 subset; encoding = tagged Buf nodes (Expr 10 ctors, `letE` 3 recursive fields) plus hash-consed node ids, as in `CONLECHE_KNOT.md`. Real compiler work: (a) user inductives or an agreed tagged-node convention with a verified `casesOn` encoding, (b) records/monadic code → state-passing, (c) higher-order record fields (`coreKnot`) → defunctionalise to a tag dispatch, (d) recursion other than fuel loop (`termination_by` 81 in other slices).
3. **Proof inheritance mismatch**: the proofs are about Lean definitions (`checkDecls`, `Cached.checkDecls_sound`); a rewrite into the nano subset would need a refinement proof (nano IR output ≈ original function), otherwise the main theorem does not transfer.
4. **Big-Nat / `.olean` reading**: `--max-nat-size` default 128 MiB numerals; `Nat.div/mod/gcd/pow` over arbitrary `Nat` (11 functions in DEPTH). Exceeds UInt64; needs a bignum-in-Buf library or a declared bound. (uncertain whether tests need it beyond the `natop_*` fixtures).
5. **Scale**: 1 GiB work memory vs real-world inputs (see §5).

## 4. Easy wins (close to the subset)
- Byte-level, `UInt64`-scalar code in `Frontend/Olean/*` (`Region`, `Seg.hit`, `isScalar`, 8-byte reads: `ConLeche/Verify/Frontend/Olean/Reads.lean`, `Nodes.lean`, `Prefix.lean` specs) — the reads are `ByteArray` + `UInt64` arithmetic + fuel-like index walks. Likely the best first candidate (the *definitions* are in slice 2 `ConLeche/Frontend/Olean/*`; here are their specs).
- `Driver/Main.lean:37–120` `parseArgs`/`flagValue`: string-prefix logic, trivial in a byte Buf; incidental (could be replaced by a fixed argv).
- `bvarOfData`, `fvarOfData`, `lpOfData`, `Level.isNeverZero/combining/simplify` (DEPTH §1): already compiled with old frontx; re-check with nano v2.
- `Main.lean`: only `setEnvVar` + flush + exit code; replace by byte-out of the verdict line.

## 5. Runtime needs (partly uncertain)
- Input: NDJSON export or `.olean`s. `tests/e2e` = 614 fixtures, 35 MB total, small. The real use is whole `Init`/`Std`/`Mathlib` (`OVERVIEW.md`: "at Mathlib …"); a Mathlib export is GBs; **input ≤ 1 MiB and work memory 1 GiB** only fits the test fixtures (`tests/e2e/*.ndjson`) and tiny modules, not Init (tens of MB).
- Def count: the checker closure was 1 103 functions (DEPTH §0) **> 511 cap**; ~2× over before inlining. Node count 16 384: the Kernel/Core closure alone is 22 160 source lines ⇒ **will exceed the parser node cap** (estimate: ≥ 100k nodes after desugaring; uncertain).
- Output: one verdict line (+ optional `--progress`): trivial.
- Heavy compute: `whnf`/`defeq` with caches (HashMap), `--jobs=n` parallelism (not representable: single-threaded subset), `LEAN_ABORT_ON_NONLINEAR` in-place array discipline (the parse tables must be updated in place; Buf `bset/bpush` is naturally linear).

## 6. Slice-specific hazards
- `whitepaper/Fragment/**` and `ConLeche/Verify/**` are not part of the shipped binary; compiling them is meaningless. A "compile con-leche" claim should be scoped to `ConLeche/{Kernel,Cached,Frontend,Driver}` + `Main.lean`.
- `tests/ConLecheTests*.lean` use `#guard` (compile-time evaluation): a possible differential-test oracle: run nano-compiled checker on the same inputs and compare verdicts with `#guard`ed expectations.
- 614 e2e fixtures with expected verdicts (`tests/e2e/src/*.lean` + ndjson; 35 MB) = ready-made acceptance suite.

## 7. Proof angle
con-leche carries its own proofs, which a verified compile would only inherit if code is not rewritten (see §3.3). Key theorems:
- `ConLeche.model_exists` (`ConLeche/MainTheorem.lean:102`): `checkDecls .verified pins maxNatSize ds = .ok env → Nonempty (Model V env)` for every `SetTheory V`.
- `ConLeche.no_False_declaration` (`MainTheorem.lean:~116`): a file declaring a theorem of type `False` is rejected.
- `ConLeche.main_no_False` (`MainTheorem.lean:152`) via `Driver.runArgs_accept` (`Verify/Driver/Main.lean:188`), `runArgs_oleans_accept` (`:126`), `runArgs_olean_accept` (`:173`): the driver's `runArgs`, in the model.
- `Cached.checkDecls_sound` (used at `MainTheorem.lean:~105`): cached checker ⇒ model; `oleanStep_spec`, `oleanWorker_reach` (`Verify/Driver/Oleans.lean:239,254`) for the parallel `.olean` workers.
- Intentionally *not* proved (`Main.lean:12`): `main` itself (env vars, flush, exit) — "read, not proved".
- Fragment theorems (`red_sound`/`defeq_sound`/`infer_sound`, `whitepaper/Fragment/Sound.lean`) are about an idealised calculus, not the code.
- Trust: Lean 4.36 kernel + 3 standard axioms; the compiled binary is not covered (`implemented_by` free per `Olean/Equiv.lean:17`, i.e. "nothing is implemented_by").

## 8. Recommendation (short)
Do not target this slice. Target the executable closure (slices 1–2): first the byte/UInt64-heavy `Frontend/Olean` readers and NDJSON lexer, then the `Expr` core via tagged Buf nodes. Raise the def cap (>1 100) and parser node cap (≥ 100k) first; plan for 1 GiB memory limit and 1 MiB input against Init-size exports.
