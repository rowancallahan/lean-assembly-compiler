# Nano/Main: the compiler C assembled, and the final theorems

## Where to start
`REVIEW.lean`: the final theorems, their `#print axioms`, every definition to trust (`lake build Nano.Main.REVIEW`, notes `Testing/notes/NANO_V2_REVIEW.md`). `Testing/scripts/review_axioms.sh` checks the axioms against the pin.

## Contents
| file | what |
|---|---|
| `Prelude.lean` | buffers and prims of the self-language (the nano subset) |
| `Chain.lean` | the chained stages' shared definitions (was `C/Base`) |
| `Sem.lean` | driver `mC x = g41 x (o41 (y16 (s10 x)))`, the meaning `Sem`, stage props |
| `Compile.lean` | `compileC`, `spaceC` (work bound) |
| `TopOn.lean` | generic top theorems over a `JTarget`: `C_correct_on`, `C_runs_on` |
| `RvTop.lean`, `ArmTop.lean` | RISC-V (`C_correctLO`, `C_runsO`) and AArch64 instances (`C_correct_rv2arm`, `C_runs_rv2arm`) |
| `SelfC.lean`, `SelfLink.lean`, `RunsTopO.lean` | C compiled by itself (`self_correct_C`, `self_runs_C`) |
| `ParCapBnd.lean`, `DBStageE.lean` | parser width cap ⇒ Gen's field bounds |

## Role
Composes `Nano/Lexer`, `Parser`, `Ownership`, `Codegen` through `Run`/`SelfHost` into `CompileCorrect` / `CompileRuns` for C (namespace `NanoMain`). Anything built on C starts here.

## Decisions
Top theorems are target-generic (`TopOn`), instances thin; the final theorem is on Sail for RISC-V, interim abstract-step for ARM. Fixpoint is a test (`Testing/nano/v2self/boot/fixpoint.sh`), not a proof.

## Rebuild
Everything: `lake build $(find Nano/{Lexer,Parser,Ownership,Codegen,Run,SelfHost,Main,Tests} -name '*.lean' | sed 's|/|.|g; s|\.lean$||')` (~12 min cold). Rules: no `sorry`, no new axioms, no `native_decide`/`bv_decide`/`extern`; module ≤ 5 min, ≤ 8 GB; `Spec/` is the owner's.

## Limits
See `REVIEW.lean` for what is trusted; ARM final theorem is modulo `A64Sem` for now.

---

# Proof/Main — C's top-level theorems

Last stage: joins the front end (lexer, parser, ownership), Gen's codegen facts and the machine layer into the
owner's `CompileCorrect` / `CompileRuns` (Spec), for RISC-V and for any other `JT.JTarget`.

## Files
* `Sem.lean` — driver `mC`, meaning `Sem` of a resolved program, stage hypotheses (no machine model).
* `Compile.lean` — source texts `SrcC`, `srcRun`, work bound `spaceC`, `compileC`, `compiler_correctG`.
* `DBStageE.lean` — Gen's field bounds for parsed programs (`dbStage`).
* `ParCapBnd.lean` — parser width cap ⇒ `bndStage`, `capStage`.
* `TopOn.lean` — generic top theorems over a target and a generator (`GenOK`, `C_correct_on`, `C_runs_on`).
* `RvTop.lean` — RISC-V instance (REVIEW roots `C_correctLO`, `C_runsO`, `C_runs`).
* `ArmTop.lean` — AArch64 instance over `A64Sem` (used by Arm/apc and Arm/sail).
* `SelfC.lean`, `SelfLink.lean`, `RunsTopO.lean` — the theorems for C's own source text.

## Design decisions
* The top theorems quantify over a generator `gen : source → code bytes` (`GenOK`), not over a re-encoding of
  Gen's RV bytes (`EncOK`): a native generator need not be a post-translator of RV output. Rejected: keeping only
  `EncOK` (forces every backend through RV bytes).
* `compileOn enc` and `EncOK` are kept with their definitions unchanged, as the instance `gen = enc ∘ mC`
  (`compileOn_gen` is `rfl`), so the statements in ArmTop, Arm/apc and Arm/sail are unchanged. Rejected:
  redefining `compileOn` over `gen` (same text `compileOn rv2arm` would silently mean something else).
* `GenOK` carries no width, block-size or jump-range condition; those stay in the target (`tbytes`, `valid`,
  `Laws`), so a target with other encodings changes `JTarget`, not this interface.
* `GenOK` includes `gen x ≠ [] → mC x ≠ []` because the front-end theorem `compiler_correctG` is stated for `mC`.

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
lake build Nano.Main.RvTop Nano.Main.ArmTop Nano.Main.REVIEW
Testing/scripts/review_axioms.sh        # "OK: 8 theorems, axioms as pinned"
```

---

# Nano/V2Self/C: the compiler, written in the self-language S

The compiler is S source (restricted nano v2 style: words, `Buf`s, `def`, fuel loops), so Lean runs it and it compiles itself.
Driver: `mC x = g41 x (o41 (y16 (s10 x)))` (`Proof/Main/Sem.lean`). Each stage reads the previous stage's `Buf`; namespace `C`.

| file | stage |
|---|---|
| `Base.lean` | constants `k0 k1 k255` and the byte writer `q0` |
| `Lex2.lean` | lexer `s10`: bytes → tag stream (tags listed in the header); empty output = reject |
| `Par1.lean` | parser `y16` (`y13` for fragments): tags → flat pre-order AST (IR v2.1, `NANO_V2_IR.md`); 2^20 width cap |
| `Own.lean` | ownership stage `o41`: AST unchanged if buffers are used linearly, else empty; slot kinds are inferred (heuristic) then checked (`OwnSpec.chk`) |
| `Gen.lean` | code generator `g41`: AST → RV64 bytes; one fuel loop over an explicit work stack, label fixups by `bset` |

Decisions: one flat `Buf` per stage (no recursion, no data types in S) so every stage is a fuel loop the proof can unroll; `Own` exists because `Gen` updates buffers in place.
The inference is unverified; only the check (`OwnSpec.chk`) is proved (`OwnStage.own_stage`).

Proofs live in `Proof/`: `Lex`, `Parser`, `Own`, `Gen`+`Machine` (code correctness), `Main` (composition); see `../README.md`.
The self-language text is the concatenation of these files (`Testing/nano/v2self/build_self_S.py`); **any edit changes the certificate and source link** (`Proof/Cert`, `Proof/SrcLink`, regenerate per `../README.md`).
Limits: restricted subset (no `≤ ≠ && ||`, no `Int64` in the lexer); programs with widths ≥ 2^20 are rejected.
