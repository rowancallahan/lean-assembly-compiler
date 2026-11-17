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
5. `S3.words P` is defined from `Ir.compileW (lowerP P)` (empty list when rejected); `compile_words` /
   `code_eq` (`c.code = wordBytes (words P)`) / `code_length` (`c.code.length = 4 * (words P).length`).
6. `S3.spaceOf c n` = max of `memoryNeeded c x` over the explicit enumeration `allBytes n` of all byte lists of
   length `n` (`memoryNeeded_le_spaceOf`); `implements1_spaceOf` needs no space hypothesis.

Results (Riscv/Back/S3Impl1.lean): `Proven.S3.implements1`, `Proven.S3.implements1_spaceOf`; axioms identical to
`Proven.S3.compile_correct` (checked with `#print axioms`). Nothing left open.

Emitted code changes: the IR stub's tail gains one `mv a1, t0` before `ret` (every IR-compiled program: S3,
Nano, IR examples); the S3 `main` wrapper returns `[.r 8]` (one extra load in its `ret`).
Nano's `main` still returns `[]`, so `a1` holds an unspecified value there (nothing claims otherwise).

Build status: `lake build Spec Compiler Riscv` and `lake build Riscv.Back.S3Impl1` succeed.
Outside that set: `Riscv.Frontx.S3Examples` / `S3RecExamples` fail with "maximum recursion depth" in the generated
certificates' `simp`; NOT caused by this work: reproduced with S3Mirror alone, and it passes when the three
`s3_norm` lemmas added by the base commit 1b68500 (`u8_mk_sw`, `u8_ofBitVec_sw`, `u64_toUInt8_ofNat`,
Compiler/S3/Cert.lean) are removed with `attribute [-s3_norm]`. `Nano.ExpandMSelf` was killed (exit 137, memory)
while another build ran on the machine; not verified here.
