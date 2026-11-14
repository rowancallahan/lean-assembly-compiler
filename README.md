# lean-assembly-compiler

A compiler from small pure Lean programs (bytes in, bytes out) to RISC-V and AArch64 machine code, with
kernel-checked proofs in Lean 4 that the machine code computes the Lean function on the Sail-generated
CPU models. No `sorry`, no extra axioms beyond the models' own, no `native_decide`/`bv_decide`.

| Folder | Contents |
|---|---|
| `Spec/` | what is proved: byte encodings, source languages and their meaning, the machine-level `Implements` statement (`Spec/Riscv.lean`) |
| `Compiler/` | machine-independent middle layer (interface + Hoare logic) and the front end (`Pipe`, `reify%`, `compile%`) |
| `Riscv/` | RISC-V back end: step lemmas (`Steps/`), direct proofs (`Direct/`), interface instance (`Back/`), `Examples/`, `Legacy/` |
| `Arm/` | ARM v9.4-A Sail model (`model/`), its generator (`gen/`), proofs (`proofs/`), `shrink/`, the AArch64 code generator |
| `Testing/` | QEMU / Sail-emulator harnesses (`asm/`), box setup, check scripts, `notes/` |

Build and check (Lean 4.29.0, RISC-V model at `../deps/sail-riscv-lean`; ~1 h from clean):

```
lake build                     # Spec, Compiler, Riscv, Arm.CompilerArm
Testing/scripts/check.sh       # build + #print axioms of the main theorems + forbidden-tactic grep
Arm/proofs/check.sh            # ARM proofs (Lean 4.34.1, needs the built model in /home/user/armv9-lean)
```

Proved on RISC-V: expressions (`compile_ok`), loops (`compileS_ok`, `gcd_ok`), byte arrays and memory
(`compileStore_ok`, `compileAF_ok`), sorting equal to `List.mergeSort` (`sortCode_implements`,
`msortCode_implements`), and the list front end (`compileP_ok`, `compile%`), also through the middle layer
(`compAF_ok`). On ARM: expressions at the decode+execute layer; the full step is in progress.

For agents: `Testing/notes/AGENT_OVERVIEW.md` (rules, where things live), `Testing/notes/SESSION_SUMMARY.md`
(log), `Testing/notes/DETAILS.md` (full proved / tested / not-proved list), `Testing/notes/ROADMAP.md`.
