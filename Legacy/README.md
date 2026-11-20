# Legacy (reference only, NOT built)

Earlier compilers and chains, moved here on 2026-11-20 so that the self-hosted compiler (`Nano/V2Self`) is the
repository's compiler. The layout mirrors the old top level (`Legacy/Compiler`, `Legacy/Riscv` incl. `Frontx`,
`Legacy/Nano`, `Legacy/Nano/V2Self/Legacy`). Module names gained the `Legacy.` prefix; imports were rewritten
mechanically. Lake library `Legacy` is not a default target and nothing live imports it: these files are not built
or checked, and some do not build (for example `Legacy/Riscv/Legacy`, which contains `sorry`). Their results are
in the history before the move (main @ f06eecb4) and in `Testing/notes`.
