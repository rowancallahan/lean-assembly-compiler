# Nano/V2Self: the self-hosted nano compiler C and its correctness proof

## Where to start
- `REVIEW.lean`: the final theorems, their `#print axioms`, and every definition you have to trust.
  Build it with `lake build Nano.V2Self.REVIEW` (about 1 min warm). The notes for it are
  `Testing/notes/NANO_V2_REVIEW.md`.
- The final theorems, all in the `NanoMain` namespace:

| theorem | file | statement |
|---|---|---|
| `C_correctLO` | `Proof/Main/RvTop.lean` | `CompileCorrect riscv compileC` (generic form: `C_correct_on`, `Main/TopOn.lean`) |
| `C_runsO` | `Proof/Main/RvTop.lean` | `CompileRuns riscv compileC` (OOM exactly below `memoryNeeded`) |
| `self_correct_C`, `self_runs_C` | `Proof/Main/SelfC.lean`, `RunsTopO.lean` | the same, for C compiled by itself |
| `Cert.sem_C` | `Proof/Cert/All.lean` | the meaning of C's own source text is C's Lean function |

## Layout
| folder | contents |
|---|---|
| `Prelude.lean` | buffers and prims of the self-language |
| `C/` | **the compiler**: `Base`, `Lex2` (lexer `s10`), `Par1` (parser `y16`), `Own` (ownership check `o41`), `Gen` (code generator `g41`). The driver is `mC x = g41 x (o41 (y16 (s10 x)))` (`Proof/Main/Sem.lean`) |
| `Proof/Lex/` | lexer spec `LexSpec.Lexes` (`Lex2Spec`), its soundness (`Lex2Sound`), token well-formedness |
| `Proof/Parser/` | reference grammar `ParSpec` (`refParse`, `ParsesProgram`), the abstract parser `ParRun*`, `ParInv*` (Par1 ↔ ParRun; `ParInv.parserSound`) |
| `Proof/Own/` | ownership spec `OwnSpec`, `OwnP0`–`OwnP30`, `OwnStage.own_stage` |
| `Proof/Gen/` | Gen's code and width relations on success (`GenRef`, `GenTop`, `GenWidth`, `GenAll`) |
| `Proof/Machine/` | the abstract machine J, Gen's templates, the node / def / program theorems, the Sail lift (`SimW`), start code, capacity / OOM exits, the host lift, the exact work bound (`RunsDef`: `Msp`) |
| `Proof/Bridge/` | `Sem` ⇐ E's machine semantics (`MainBridge*`), the converse (`MainConv*`), the shift invariant (`MainShift*`: `shiftInv`) |
| `Proof/Main/` | `Sem` (the semantics, stage props), `Compile` (`compileC`, `spaceC`), `TopOn` (generic top theorems over a `JTarget`), `RvTop` (RISC-V instances), `SelfC` / `RunsTopO` (self-compilation) |
| `Proof/Cert/` | **GENERATED** meaning certificate (`sem_C`). Do not edit by hand |
| `Proof/SrcLink/` | `SrcLink.lean` plus **GENERATED** chunks: C's text lexes and parses to `Cert.PC.all` (`SrcGen.link_pc`) |
| `Proof/Tests/` | non-vacuity tests and audit witnesses (`OwnNV`, `MainWitness`, `MainCert`, `AuditWitness`, `AuditSpace`) |
| `Legacy/` | the old compiler chain (pre-Par1/Gen). Not part of the proof; kept for the scripts in `Testing/nano/v2self` |

Namespaces do not follow the folders (for example `NanoMain`, `ParSpec`, `Templates`, `Cert`, `SrcGen`).

## Rebuilding and regenerating
- Everything: `lake build $(find Nano/V2Self -name '*.lean' | sed 's|/|.|g; s|\.lean$||')` (about 12 min cold, 4 cores).
- Self-language source of C: `python3 Testing/nano/v2self/build_self_S.py` writes `Testing/nano/v2self/self_S.lean`,
  a plain concatenation of `C/{Base,Lex2,Par1,Own,Gen}.lean` plus the driver. The bootstrap fixpoint script
  (`Testing/nano/v2self/boot/fixpoint.sh`) also writes `self_S_input.txt` (C's text).
- Fixpoint (a test, not a proof): `Testing/nano/v2self/boot/fixpoint.sh`. It runs B1 = Lean-compiled `self_S` to get
  B2 = B1(text), then B3 = B2(text) on QEMU, and compares B3 with B2. The current values are in
  `Testing/nano/v2self/B2.sha256`.
- Certificate, after any change to C's source text:
  `lake env lean --run Testing/nano/v2self/cert/dump_pc.lean Testing/nano/v2self/self_S_input.txt > pcdump`, then
  `python3 Testing/nano/v2self/cert/gen_cert.py pcdump` (writes `Proof/Cert/`).
- Source link, after any change to C's source text: `lake env lean --run Testing/nano/v2self/srclink/gen.lean SRC
  OUTDIR GROUPTOKS` (writes `Proof/SrcLink/` chunks; see the file header).
- Axioms of the REVIEW theorems against the pinned list: `Testing/scripts/review_axioms.sh`.
- Dead code: `Testing/scripts/deadcode.sh` (report: `Testing/notes/NANO_V2_DEADCODE.md`).
- Rules: no `sorry`; no new axioms; no `native_decide`, `bv_decide` or `extern`; each module ≤ 5 min and ≤ 8 GB
  (12 GB tolerated by the owner); `Spec/` is the owner's.

## Notes
The index of `Testing/notes/NANO_V2_*.md` is `Testing/notes/NANO_V2_STATUS.md`.
