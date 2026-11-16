# nano integration (branch `nano-int`): closing the loop on proven self-hosting

Integrator notes. Branch = `nano-mvp` + `nano-e2e` + `nano-proof` + `main`, merged every 30–45 min.

## Target (not yet proved)
`Nano/SelfHost.lean`: let `B` = the RISC-V binary our compiler produces from the Lean definition of the whole stack-path
compiler `nanoCompileS = asm ∘ genR ∘ nanoElab`. For every `src`, `p` with `nanoElab src = some p`: `B` run on `src` on the
Sail model outputs `c`, and `c` run on the Sail model computes `p.eval` (UInt64 and Int64), OOM flag exactly when the
work block is too small. L1 = `B` computes `nanoCompileS`; L2 = `CompileCorrect`/`CompileRuns riscv` for `asm ∘ genR`.

## Live status
| piece | state |
|---|---|
| L1 `asm` compiled, machine theorem | was done for the 9-op `asm`; BROKEN since nano-e2e 4c64d61 (15 ops: `frontx_compile` capacity condition, simp step limit); nano-e2e is on it |
| L1 `genR` compiled | not yet (nano-e2e: byte-level rewrite in progress) |
| L1 `nanoElab` compiled | not yet (nano-e2e) |
| L1 one binary from the stages | glue done: `Nano.Link.link_implements` (this branch) |
| L2 stack generator `asm ∘ genR` correct | not yet (nano-proof); the IR generator `nanoGen` is proved but is not the self-hosted path |
| composition `Nano/SelfHost.lean` | statement `SelfHosted` + `selfHosted_of` (target from L1 and L2 as hypotheses) done; instance waits for L1 and L2 |
| tests | see log below |

## Naming (one consistent set; follows the lanes' latest pushes, 22:16–22:24)
* `genR`, `nanoGen = asm ∘ genR`, `nanoCompile`: the stack generator = the SELF-HOSTED path (`Nano/Gen.lean`, nano-e2e).
  (The owner prompt calls these `nanoGenS`/`nanoCompileS`.)
* `nanoGenIR`, `nanoCompileIR`, `nanoCompileSrcIR` (`Nano/GenIR.lean`, `ProofTop.lean`, `ProofSrc.lean`, nano-proof):
  the PROVED IR-route generator; noncomputable, not the self-hosted path. `Nano/Chain.lean` (nano-mvp) still said
  `nanoGen`/`nanoCompile` for it: renamed here to the `…IR` names; `nanoCompileSrc` (Chain) kept.
* `Nano.Self.*`: stages compiled by the big compiler (`….implements1`). `Nano.Link.*`: linking. `Nano.SelfHost.*`: the target.

## Decisions
* 2026-11-16 22:15. Critical-path gap found: the front end cannot compile a composition of passes as one entry
  (TINYSELF2 F11), so ONE binary `B` for `asm ∘ genR ∘ nanoElab` needs a linker with a machine proof. Done here:
  `Nano/Link.lean`, `link cf cg` = 18-word stub ++ `cg` ++ `cf`; `link_implements`: `Implements1With` for `f` (with
  `retLen = true`) and for `g` give `Implements1With` for `g ∘ f`, work space `4 * M n + 96` where `M n` bounds the
  intermediate length and both stages' work space; needs `cg.length < 2^17` (one `jal`) and the intermediate result
  within `g`'s input bound. The result is again `Implements1With`, so three stages = two links. Axioms = the Sail set.
  Design notes: `f`'s output block and work, the stub's 32-byte frame and `g`'s work are four disjoint parts of the work
  block (`Implements1With` does not say the work block stays mapped after a call, so `g` gets a part `f` never touched);
  `g` is entered by fall-through with the caller's `ra`/`a3`/`sp`, so no epilogue.
* Consequence for the lanes: every stage but the last must be compiled with `retLen = true`; intermediate encodings must
  be byte lists whose length is bounded by a function of the input length (inlining in `genR` is exponential in call
  nesting, so the target will carry a size hypothesis or the stages a larger `maxLen`).
* 2026-11-16 22:40. Merge of nano-e2e 4c64d61, nano-proof 1b1c4fe, nano-mvp 6374c37. `expected-axioms.txt` conflicts
  resolved with `Testing/nano/fix_axioms_conflict.py` (keep both sides, theirs first = check.sh's loop order).
  `Nano/AsmSelf.lean` does not build (see table); everything else in `Nano` builds. Sent the e2e session the linking
  interface (retLen = true for non-final stages, output-length bounds).
* `Nano/SelfHost.lean`: `SelfHosted B space D compile` (fields `code`, `emits`, `correct`, `correctInt`, `runs`) and
  `selfHosted_of` from (L1) `Implements1With` for a byte function `cb` on the domain `D` with `cb src = nanoGen p`,
  (L2) `CompileCorrect`/`CompileRuns riscv compile` with `c.code = nanoGen p`. `D` = the size side conditions.
* 2026-11-16 22:45. Merged nano-proof 777323f (`Nano/StackRec.lean`: record machine, `genE_ok`/`genA_ok`). Its `Nano.S`
  is a copy of `Nano/Gen.lean`; instead of editing either lane's file, `Nano/Bridge.lean` proves `S.genR p = genR p`
  and `S.depth p = depth p` (and the pieces), so nano-proof can keep its copy and the composition uses e2e's `genR`.
* `Nano.Link.link_stage`/`comap`: the linker for stages in the front end's theorem form
  (`Implements1With (·.data.toList) id code f space (2^20) true`, as `frontx_implements_listC` produces).
