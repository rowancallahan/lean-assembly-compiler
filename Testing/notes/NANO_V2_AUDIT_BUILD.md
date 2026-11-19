# Nano V2Self audit build (H1, at HEAD 9b4306aa; committed by the lead from H1's report)

Sequential `lake build <module>` over 401 modules under Nano/V2Self. Most modules were already up to date, so times are
incremental, not cold-build numbers. Peak RSS is the lake process including its Lean child.

- Modules: 401; failed: 3 (MainCertC3, MainCertC4, MainCertC5: compile errors, not OOM). These were F's abandoned
  duplicate certificate; deleted since (O, 5024388).
- Max wall: Driver 60.5 s; max peak RSS: MainWitness 2.6 GB. No module over 5 min or 8 GB.

## Banned/axiom grep (Nano/V2Self)
No uses of native_decide, bv_decide, ofReduceBool, implemented_by, @[extern], sorry, admit or axiom; the only hits are
`#print axioms` lines and doc comments (REVIEW.lean:2/17/21/32, ParCapBnd.lean:122).

## Axioms (at 9b4306aa)
- `NanoMain.C_correctLO`, `NanoMain.self_correct_C`: the Sail RISC-V extern set (cancel/load/match/valid_reservation,
  get_16_random_bits, plat_term_write, sys_enable_experimental_extensions, the riscv_f16/f32/f64/i/ui conversion and
  arithmetic externs) + propext, Classical.choice, Quot.sound. No sorryAx.
- `Cert.sem_C`, `SrcGen.link_pc`: propext, Quot.sound.
- `ParInv.parserSound`: propext, Classical.choice, Quot.sound.

## SelfC's own Lean process
`lean Nano/V2Self/Proof/SelfC.lean` with deps built: wall 1.2 s, peak RSS 1.9 GB. The earlier 13.3 GB figure was the
lake process rebuilding dependencies; Cert.Fun alone peaked at 12.2 GB (since removed from the import path and deleted).
