# S3 -> Implements1With adapter (Riscv/Back/S3Impl1.lean)

Decisions (recorded as made):

1. Result length in a1: the IR stub after `main` returns now runs `mov RLen R0` (RLen = r12 = a1, R0 = rk 0 = t0,
   where `ret` loads `main`'s first result) before `ret`: `stub3 = [leaveC 0, leave, mov RLen R0, ret]`
   (Compiler/Ir/Emit.lean). The S3 main wrapper `mainTC` returns `[.r 8]`, the output index register of
   `outLoop`, i.e. the number of bytes written.
2. `Ctx.Fin` (Compiler/Ir/EmitStep.lean) success disjunct strengthened with `T.keepC C.s0 s'`,
   `T.fr s' = T.fr C.s0` and `∀ v, r.vs[0]? = some (.w v) → T.get s' RLen = v`; `done_ok` proves them
   (leave restores the frame register gp from the stub's cell). On RISC-V keepC + gp give `abiSavedKept`.
3. Memory frame (4) needs NO simulation change: `emit_ok` holds for any `Ctx`, so the adapter instantiates the
   context with `outL := y.length` (the actual result length) instead of the output block's length; `Unch` is then
   exactly "unchanged outside [output.base, y.length) and the work block".
4. `Cfg` after the run is `T.ok` in `Fin`.
