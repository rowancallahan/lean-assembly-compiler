# Nano/Base/V2: the "small backend" (namespace `Nano.V2B`)

A typed stack-machine code generator for the nano v2 language, with a Lean proof that the RISC-V words it emits
refine the language semantics on the Sail model. It is the base layer that `Nano/V2Self` reuses: `Proof/Machine/{SimW,Bridge,RvEnc}.lean`
import `Sim`/`Enc`/`Gen`, and `Testing/nano/v2f/run.lean`, `Testing/nano/v2self/selfcompile.lean` run `Gen`. Design notes: `Testing/notes/NANO_V2_BACKEND.md`.

## Files (import order)
| file | contents |
|---|---|
| `Lang.lean` | typed AST (`Ty`, `Ex`, `Tl`, `Prog`) and its Lean meaning (`den`, `run`, `Prog.eval`); words, owned buffers, nested products, fuel loops |
| `Gen.lean` | AST → structured stack code `SC` (`cE`, `cT`, `prologue`, `epilogue`) → flat `I` words (`SC.flat`, `I.enc`); register/calling convention is in the header |
| `Sem.lean` | semantics of `SC` on an abstract word machine (`St`, `Cfg`, `I.run`, `runL`, `SC.Ex`); an out-of-block access is stuck |
| `Expr.lean` | proof layer 2: the stack invariant `Stk` and the uniform contract of `cE`/`cT` (`li_ok`, `pushC_ok`, `Keep`, `Post`) |
| `Flat.lean` | proof layer 3: `SC.flat` on a pc-level machine (`pstep`, `PStar`, `flat_ok`) |
| `Enc.lean` | proof layer 4a: for `I.wf` instructions `I.enc` is the word the Sail step lemmas are stated for (`encSt_eq`, `encBt8_eq`, `encJt_eq`) |
| `Sim.lean` | proof layer 4b: one `pstep` = one retired Sail instruction under `Rel` (`sim_step`, `sim_star`) |

## Decisions
- Structured `SC` first, flattening second: control flow is proved once on `SC.Ex`, byte offsets only in `Flat`/`Sim`.
- Abstract machine gets stuck on any bad access, so "the code runs" already proves every access valid (what `Sim` needs).
- Every push checks `t6 ≥ t5`, every `mk` checks the heap top: out-of-memory is a status code, never undefined behaviour.

## Check
`lake build Nano.Base.V2.Sim` (needs the Sail RV model at `../deps/sail-riscv-lean`, see `Testing/notes/MODEL_PROVENANCE.md`);
axioms of the final theorems: `Testing/scripts/review_axioms.sh`.

## Limits
Only the RISC-V back end; the instruction set is what `Gen` emits (no compressed forms). Cleanups here must keep names used by `Nano/Run`.
