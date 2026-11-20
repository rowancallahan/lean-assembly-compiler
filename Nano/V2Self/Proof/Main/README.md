# Proof/Main — C's top-level theorems

Last stage: joins the front end (lexer, parser, ownership), Gen's codegen facts and the machine layer into the
owner's `CompileCorrect` / `CompileRuns` (Spec), for RISC-V and for any other `JT.JTarget`.

## Input (from earlier stages)
* `Compile.lean:compiler_correctG` (front end): an accepted text's RV bytes `mC x` are Gen's bytes for a parsed
  linear program (`TopOn.lean:GenFacts`).
* `Machine/HostOk`, `HostOom` (`host_ok`, `host_tiny`, `host_room`): for a target `T` with `T.Laws`, code bytes
  `tbytes T Cj` of Gen's J program `Cj` run correctly / report out of memory.
* `Bridge/MainShift4` (`shiftInv`, `lt_room`), `ParCapBnd.lean` (`bndStage`, `capStage`), `DBStageE.lean:dbStage`.

## Output
| file:name | statement |
|---|---|
| `TopOn.lean:compileGen gen` | compiler whose code is `gen s.text` (memory bound `spaceC`) |
| `TopOn.lean:GenOK T gen` | generator interface, below |
| `TopOn.lean:C_correct_on`, `C_runs_on` | `GenOK T gen` → `CompileCorrectP` / `CompileRunsP T.M T.loader (compileGen gen)` |
| `TopOn.lean:EncOK`, `compileOn enc`, `genOK_of_enc`, `compileOn_gen` | post-translator `enc` of Gen's RV bytes = the generator `enc ∘ mC` |
| `RvTop.lean:rv_gen`, `C_correctLO`, `C_runsO`, `C_runs` | RISC-V: `gen = mC`, `compileGen mC = compileC` (REVIEW roots) |
| `ArmTop.lean:C_correct_armG`, `C_runs_armG` | AArch64 for any `GenOK (armTarget M X W) gen` (native generator plugs in here) |
| `ArmTop.lean:C_correct_arm`, `C_runs_arm`, `C_correct_rv2arm`, `C_runs_rv2arm` | AArch64 via a translator with `EncOK` (rv2arm) |
| `SelfC.lean`, `SelfLink.lean`, `RunsTopO.lean` | C compiled by itself, for C's own source text |

## The generator interface
```
GenOK T gen := ∀ x, gen x ≠ [] → mC x ≠ [] ∧
  ∀ c Cj, Cj.length < 2^18 → (∀ j ∈ Cj, JOK j) → mC x = g40 16777216 c (Cj.map encG) 0 [] →
    gen x = tbytes T Cj ∧ T.valid Cj
```
A generator owes: its bytes for `x` are the target's bytes of `x`'s J program, and that program is valid for the
target. It owes nothing about instruction width, block size or jump range; those live in `T` (`tbytes`, `valid`,
`Laws`). `Cj.length < 2^18` and `JOK` are facts it may use, not obligations.

## Known limits
* `Cj` is identified through Gen's RV words (`mC x = g40 … (Cj.map encG)`), and `gen x ≠ []` must imply
  `mC x ≠ []`: a native generator must still be related to C's RV output until Gen's proof is factored over an
  abstract emitter (CLEANUP_PLAN step 9).
* `tbytes T Cj` (Machine/HostGen.lean) is `T.enc j` as 32-bit little-endian words, `blockLen` words per J
  instruction (`addr`): a variable-length target (x86-64) needs
  `JTarget` generalised (Machine/Target.lean), not `GenOK`.
* `hwin : 2^31 ≤ T.M.ramStart` on `C_correct_on` / `C_runs_on` (position lemmas of the exact work bound).
* `compileC s = some _` is not kernel-proved for any text (see REVIEW.lean).

## Build / check
```
lake build Nano.V2Self.Proof.Main.RvTop Nano.V2Self.Proof.Main.ArmTop Nano.V2Self.REVIEW
Testing/scripts/review_axioms.sh        # "OK: 8 theorems, axioms as pinned"
```
