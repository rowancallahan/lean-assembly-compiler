# nano onto the S3 calculus, one construct per link (branch nano-s3, 2026-11-17)

Goal (owner, ROADMAP "INTERPOLATE"): a second, S3-based back end for nano, proved by design: a chain of calculi,
each differing from the previous by ONE construct, each link a proved meaning-preservation lemma.

## Setup notes
- Branch base: origin/ir-s3 merged with origin/main and origin/nano-parse. Conflicts only in
  Testing/scripts/expected-axioms.txt (two appended blocks, both kept: ir-s3 then nano) and check.sh's axiom loop
  (ir-s3 placed before the nano-* files, matching that order).
- Toolchain: elan.lean-lang.org was DENIED by the network policy (403 at the proxy). Not routed around: the Lean
  4.29.0 release tarball was taken from releases.lean-lang.org (an allowed host), lean/lake symlinked into
  /usr/local/bin. Build cache restored per build-cache README (zstd).

## The chain
| link | calculus | the one construct | translation | theorem |
|---|---|---|---|---|
| L0 | nano `Ex` (`den`, `Prog.eval`) | — | — | — (spec) |
| L1 | `E1` (Nano/S3L1.lean) | no `call` (own environment) | `tr1`: call ↦ lets + `shift` args + `cut` body | `tr1_eval` |
| L2 | `A` (Nano/S3L2.lean) | operands are variables (ANF; add/sub/mul → `bin o i j`) | `tr2`: `a ⊕ b` ↦ `let x := a; let y := b↑; x ⊕ y` | `tr2_eval` |
| L3 | S3 `Expr S Γ .w` (Nano/S3L3.lean), `Ev` | typed scoped variables `Var Γ .w` (no "out of range = 0") | `tr3 σ`: index `i` ↦ `σ[i]`, out of range ↦ `lit 0` | `tr3_ok`, `tr3_prog` |
| L4 | S3 `Prog` on bytes (Nano/S3L4.lean), `Prog.run` | the byte-list datatype (`mk`/`cas`) for I/O | `toS3`: `main` = decode `n` 8-byte LE words (`rdB`/`wdW`), `tr3`, encode 8 bytes (`outB`) | `toS3_run` |

Deviation from the suggested chain (decided): the owner's "L1 = explicit lets" is split in two links, because nano's
`call` (an inlined callee with its OWN environment) and A-normal form are two different constructs: L1 removes the
call (lets + `shift`/`cut`), L2 makes operands variables. L3 (typed, scoped variables) and L4 (byte-list I/O) as
suggested. One function only (no S3 `call`): the decoder leaves the words in the context and `tr3` takes a context
map `σ` (nano index → S3 variable), so the body sits directly under the decoder's matches; this also avoids the IR
back end's 7-parameter limit on calls.

## Composition (Nano/S3Top.lean)
- `nanoToS3 = toS3 ∘ tr2P ∘ tr1P` (pure, computable); `nanoCompileS3 = S3.compile ∘ nanoToS3` (noncomputable only
  through S3's `Accepted` test; `accepted` proves it always holds, `nanoCompileS3_eq` = `Ir.compile ∘ lowerP ∘ nanoToS3`).
- `nanoToS3_run : nanoRun p input = some out → (nanoToS3 p).run input = some out`.
- **`nano_s3_correct : CompileCorrect riscv nanoCompileS3`**, **`nano_s3_runs : CompileRuns riscv nanoCompileS3`**
  (S3's `compile_correct`/`compile_runs` applied to `nanoToS3 p`; `Computes` transferred by `nanoToS3_run`).
- `nano_s3_chain` (`chain_of`), `nano_s3_chain_int` (`chain_int_of`, Int64 via `nanoRun_int`).
- Axioms: link theorems ⊆ {propext, Classical.choice, Quot.sound}; machine theorems exactly the Sail set.
  `Testing/scripts/axioms_nano-s3.lean` in check.sh's loop, lines appended to expected-axioms.txt.

## Tests (`python3 Testing/asm/nano_s3_test.py 10 4`, ≈10 min; removes Testing/asm/ctest)
Sources: nanolib CORPUS + INT_CORPUS, chain_test's adversarial EDGE_SRC, 6 boundary sources (10 parameters, shadowing
lets, an 8-argument callee called twice, a doubling chain inlined 32×, a constant entry, deep nesting), 10 + 10 random
UInt64/Int64 sources; 8 inputs each (edge values + random); plus 46 random `Ex` trees (emit_nano's generators: calls,
out-of-range variables, large frames).
- Lean side (`Testing/asm/emit_nano_s3.lean`), every case, every link: L1 `(tr1P p).eval`, L2 `(tr2P (tr1P p)).eval`,
  L3 (test evaluator of S3 expressions on `tr3 (idVars n)`), L4 (test evaluator on `main`, bytes) and the IR
  interpreters of `lowerP (nanoToS3 p)` all equal `p.eval` / `nanoRun p`; emitted words == `compileW` (the code of
  `Ir.compile`). Result: **146 programs (10 sources rejected by nanoElabT), 1168 cases, mismatches 0**.
- QEMU, all programs in one image: **146 programs, 1168 cases × 2 ok** (output == Lean at `memoryNeeded`, a0 = flag
  at `memoryNeeded - 1`, sp/gp restored, nothing outside output + work changed); code 495..9367 words.
- Sail smoke (`ir_test.py check 2`, QEMU == Sail == Lean, Sail writes traced): **4 programs × 2 cases × 2 ok**.

## Findings / decisions during testing
- First decoder kept every byte's temporaries in scope; S3's lowering numbers registers by context depth, so arity ≥ 7
  overflowed the IR back end's 254 frame slots (`compileW = none`; theorems unaffected, `none` is allowed). Fixed by
  reading each word inside a `let`'s bound expression returning a (word, rest) pair (datatype `d 1`): 3 registers per
  argument. Remaining limit (as for nano's IR route): context depth (nano lets + inlined arguments + ANF nesting +
  3·arity) ≤ ~250, else `nanoCompileS3 p = none`.
- `memoryNeeded` must count call frames (S3's wrapper calls `main`): the reference `interp` does not record them,
  so the cases use emit_s3's fast interpreter (copied), whose events match `Ir.events`.
- Code size: the S3 route is larger than the stack route (unrolled 8-byte decoder per argument, list construction
  for the output). No optimisation attempted (not in scope).
