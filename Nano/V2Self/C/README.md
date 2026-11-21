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
