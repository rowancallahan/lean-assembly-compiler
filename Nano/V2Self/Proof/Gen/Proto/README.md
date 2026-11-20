# Proof/Gen/Proto: throwaway prototype for cleanup step 9 (design input, not live)

* `Emit.lean`: GenRef's work-item invariant with the Gen source (`Src`: g36/g37) and the emitters (`Em`) as parameters.
  Main: `Em`, `Em.OK`, `Src`, `Src.OK`, `Reach`, `CG`/`CGs`, `v_const`, `seq`, `v_call`; RISC-V instance `rvEm`, `rvSrc`,
  `rvSrc_ok`, `reach_rv`, `cg_rv`, `v_const_rv`.
* `Lay.lean`: target encoder `Tgt` and layout `pos` (J index to cell index) for "emitted cells = encoding of the J
  templates", including non-uniform layouts. Main: `encL`, `GLay`, `lay_at`, `Exact`, `em_const`, `rv_exact`.

Sits beside `Proof/Gen/GenRef.lean` (imports it and `Proof/Machine/NdCG.lean`); nothing imports this folder.
Covers CONST and CALL only; no fixups (IF/LOOP/exits). Assumptions of the generic theorems: `S.OK E`, `E.OK`, `T.OK`,
`Exact E T`, `GLay T pos C`; all proved for RISC-V. Design, alternatives, blockers and estimate:
`Testing/notes/GEN_EMIT_PROTO.md`. Build: `lake build Nano.V2Self.Proof.Gen.Proto.Lay`.
