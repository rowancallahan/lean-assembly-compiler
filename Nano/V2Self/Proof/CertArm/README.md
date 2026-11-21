# Proof/CertArm — meaning certificate of the ARM translator `rv2arm` (GENERATED)

Everything here except this file is written by `Testing/nano/v2self/cert/gen_cert.py` from
`Testing/nano/v2self/arm/rv2arm.lean`. Do not edit by hand; regenerate.

| file | contents |
|---|---|
| `Src.lean` | `rv2arm` source as Lean defs (namespace `RA`, comments stripped) |
| `PC.lean` | reference parse of `self_S_input.txt`: `b<i>`/`d<i>` (`Nd`/`DefA`), list `PC.all` |
| `OutSpec.lean` | word-level (`UInt64`) shadows `q`, `e0`, … of the output-building defs, with `<f>_map` (low bytes = the `RA` def) |
| `Specs.lean` | `Spec<i>`: per-def specification (`Ref (F args) (enc (RA.f args))`), `Cert.call_<i>` call rules, `specs inp` |
| `Defs0..3.lean` | `ok_<i>`: def `i` meets `Spec<i>`, given the specs of the defs it calls (`Good`) |
| `All.lean` | `all_ok` (every def meets its spec), `sem_rv2arm` (`Sem κC PC.all inp` refines `RA` on the whole program) |

Where it sits: the ARM instance of the same certificate method as `Proof/Cert` (RISC-V compiler C), reusing
`Cert.Tac`/`Cert.Asm`. `Machine/ArmRA.lean` imports `Src` to prove `rv2arm` correct on Gen's words (`armOK` blocks).

Decision: certify the *source text* of `rv2arm` by evaluating its parsed program, so the translator that is run is the
one proved, with no hand-written model; chunked into `Defs0..3` to keep each file's elaboration small.

Check: `lake build Nano.V2Self.Proof.CertArm.All`. Assumption: `inp.length < 2^64`. Limit: covers `rv2arm` as written; any
edit to its source needs regeneration.
