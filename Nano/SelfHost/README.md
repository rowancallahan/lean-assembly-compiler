# Nano/SelfHost: C's own source text is compiled correctly by C

## Contents
| folder | what |
|---|---|
| `Cert/` | **GENERATED** (`Testing/nano/v2self/cert/gen_cert.py`): meaning certificate `Cert.sem_C`: the meaning of C's source text is C's Lean function. Do not edit |
| `CertArm/` | **GENERATED** the same for the `rv2arm` translator (`CertArm.sem_rv2arm`) |
| `SrcLink/` | `Chain`, `Chk*` (**GENERATED** by `Testing/nano/v2self/srclink/gen.lean`): C's text lexes and parses to `Cert.PC.all` (`SrcGen.link_pc`) |
| `Bridge/` | `MainBridge*` (nano semantics ⇐ machine semantics), `MainConv*`/`MainConvF*/X*` (converse), `MainShift*` (`shiftInv`), `MainOk`, `MainTy`, `SemX` |

## Role
Turns "C is correct for every source" into "C compiled by itself is correct": the text of C is certified (Cert), shown to be what the parser reads (SrcLink), and its semantics bridged to the machine (Bridge). Used by `Nano/Main/SelfC`, `SelfLink`, `RunsTopO`.

## Decisions
Certificates are generated and checked by the kernel rather than proved by hand (C's text has hundreds of defs). Regenerate after any change to C's source: see `Testing/nano/v2self/` scripts and `Nano/Main/README.md`.

## Check
`lake build Nano.SelfHost.Cert.All Nano.SelfHost.SrcLink.Top`.

## Limits
Generated files are large (Cert ≈ 50 modules, SrcLink ≈ 65); they must be regenerated, never patched.
