# Nano V2Self audit build (HEAD 9b4306aa)

Sequential `lake build <module>` over 401 modules under Nano/V2Self. Most modules were already up to date, so times are incremental, not cold-build numbers. Peak RSS is the lake process including its Lean child.

- Modules: 401; failed: 3 (MainCertC3, MainCertC4, MainCertC5, all compile errors, not OOM)
- Max wall: Driver 60.5 s; max peak RSS: MainWitness 2.6 GB. No module over 5 min or 8 GB.

## Failures
- MainCertC3:
  - error: Nano/V2Self/Proof/MainCertC3.lean:78:15: Tactic `rfl` failed: The left-hand side
  - error: Lean exited with code 1
- MainCertC4:
  - error: Nano/V2Self/Proof/MainCertC4.lean:45:13: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
  - error: Nano/V2Self/Proof/MainCertC4.lean:53:13: Tactic `rfl` failed: The left-hand side
- MainCertC5:
  - error: Nano/V2Self/Proof/MainCertC5.lean:44:13: Tactic `rfl` failed: The left-hand side
  - error: Nano/V2Self/Proof/MainCertC5.lean:99:13: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

## Banned/axiom grep (Nano/V2Self, file:line)
Nano/V2Self/REVIEW.lean:2:Build: `lake build Nano.V2Self.REVIEW`.  The #print axioms output is the authoritative axiom list. -/
Nano/V2Self/REVIEW.lean:17:#print axioms NanoMain.C_correctLO
Nano/V2Self/REVIEW.lean:21:#print axioms Cert.sem_C
Nano/V2Self/REVIEW.lean:32:#print axioms NanoMain.self_correct_C
Nano/V2Self/Proof/ParCapBnd.lean:122:#print axioms NanoMain.C_correctLO

## Axioms
'NanoMain.C_correctLO' depends on axioms: [cancel_reservation,
 get_16_random_bits,
 load_reservation,
 match_reservation,
 plat_term_write,
 propext,
 riscv_f16Add,
 riscv_f16Div,
 riscv_f16Eq,
 riscv_f16Le,
 riscv_f16Le_quiet,
 riscv_f16Lt,
 riscv_f16Lt_quiet,
 riscv_f16Mul,
 riscv_f16MulAdd,
 riscv_f16Sqrt,
 riscv_f16Sub,
 riscv_f16ToF32,
 riscv_f16ToF64,
 riscv_f16ToI32,
 riscv_f16ToI64,
 riscv_f16ToUi32,
 riscv_f16ToUi64,
 riscv_f16roundToInt,
 riscv_f32Add,
 riscv_f32Div,
 riscv_f32Eq,
 riscv_f32Le,
 riscv_f32Le_quiet,
 riscv_f32Lt,
 riscv_f32Lt_quiet,
 riscv_f32Mul,
 riscv_f32MulAdd,
 riscv_f32Sqrt,
 riscv_f32Sub,
 riscv_f32ToBF16,
 riscv_f32ToF16,
 riscv_f32ToF64,
 riscv_f32ToI32,
 riscv_f32ToI64,
 riscv_f32ToUi32,
 riscv_f32ToUi64,
 riscv_f32roundToInt,
 riscv_f64Add,
 riscv_f64Div,
 riscv_f64Eq,
 riscv_f64Le,
 riscv_f64Le_quiet,
 riscv_f64Lt,
 riscv_f64Lt_quiet,
 riscv_f64Mul,
 riscv_f64MulAdd,
 riscv_f64Sqrt,
 riscv_f64Sub,
 riscv_f64ToF16,
 riscv_f64ToF32,
 riscv_f64ToI32,
 riscv_f64ToI64,
 riscv_f64ToUi32,
 riscv_f64ToUi64,
 riscv_f64roundToInt,
 riscv_i32ToF16,
 riscv_i32ToF32,
 riscv_i32ToF64,
 riscv_i64ToF16,
 riscv_i64ToF32,
 riscv_i64ToF64,
 riscv_ui32ToF16,
 riscv_ui32ToF32,
 riscv_ui32ToF64,
 riscv_ui64ToF16,
 riscv_ui64ToF32,
 riscv_ui64ToF64,
 sys_enable_experimental_extensions,
 valid_reservation,
 Classical.choice,
 Quot.sound]
'NanoMain.self_correct_C' depends on axioms: [cancel_reservation,
 get_16_random_bits,
 load_reservation,
 match_reservation,
 plat_term_write,
 propext,
 riscv_f16Add,
 riscv_f16Div,
 riscv_f16Eq,
 riscv_f16Le,
 riscv_f16Le_quiet,
 riscv_f16Lt,
 riscv_f16Lt_quiet,
 riscv_f16Mul,
 riscv_f16MulAdd,
 riscv_f16Sqrt,
 riscv_f16Sub,
 riscv_f16ToF32,
 riscv_f16ToF64,
 riscv_f16ToI32,
 riscv_f16ToI64,
 riscv_f16ToUi32,
 riscv_f16ToUi64,
 riscv_f16roundToInt,
 riscv_f32Add,
 riscv_f32Div,
 riscv_f32Eq,
 riscv_f32Le,
 riscv_f32Le_quiet,
 riscv_f32Lt,
 riscv_f32Lt_quiet,
 riscv_f32Mul,
 riscv_f32MulAdd,
 riscv_f32Sqrt,
 riscv_f32Sub,
 riscv_f32ToBF16,
 riscv_f32ToF16,
 riscv_f32ToF64,
 riscv_f32ToI32,
 riscv_f32ToI64,
 riscv_f32ToUi32,
 riscv_f32ToUi64,
 riscv_f32roundToInt,
 riscv_f64Add,
 riscv_f64Div,
 riscv_f64Eq,
 riscv_f64Le,
 riscv_f64Le_quiet,
 riscv_f64Lt,
 riscv_f64Lt_quiet,
 riscv_f64Mul,
 riscv_f64MulAdd,
 riscv_f64Sqrt,
 riscv_f64Sub,
 riscv_f64ToF16,
 riscv_f64ToF32,
 riscv_f64ToI32,
 riscv_f64ToI64,
 riscv_f64ToUi32,
 riscv_f64ToUi64,
 riscv_f64roundToInt,
 riscv_i32ToF16,
 riscv_i32ToF32,
 riscv_i32ToF64,
 riscv_i64ToF16,
 riscv_i64ToF32,
 riscv_i64ToF64,
 riscv_ui32ToF16,
 riscv_ui32ToF32,
 riscv_ui32ToF64,
 riscv_ui64ToF16,
 riscv_ui64ToF32,
 riscv_ui64ToF64,
 sys_enable_experimental_extensions,
 valid_reservation,
 Classical.choice,
 Quot.sound]
'Cert.sem_C' depends on axioms: [propext, Quot.sound]
'SrcGen.link_pc' depends on axioms: [propext, Quot.sound]
'ParInv.parserSound' depends on axioms: [propext, Classical.choice, Quot.sound]

## SelfC's own Lean process (addendum)

`lean Nano/V2Self/Proof/SelfC.lean` with `LEAN_PATH` from `lake env` (dependencies already built), measured with wait4 on the lean process itself: exit 0, wall 1.2 s, user 0.9 s, peak RSS 1.9 GB, no output (no errors or warnings). SelfC.lean is 51 lines of statements; its dependencies carry the proof work.

Correction: the earlier 13.3 GB peak for the SelfC step was the lake process during a build that also rebuilt dependencies, not SelfC's own elaboration. Cert.Fun alone peaked at 12.2 GB during its own rebuild.
