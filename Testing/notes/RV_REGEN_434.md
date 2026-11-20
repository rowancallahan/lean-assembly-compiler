# RISC-V model REGENERATED with Sail 97aa617dc (not the trusted model): Lean 4.34.1

Branch `rv-regen-434` (based on `lean-4.34`). This is an experiment. The trusted model (`51c635c`, Lean 4.29)
is unchanged on `main` and `nano-v2-src`. Provenance, exact commands and versions: `Riscv/gen/PROVENANCE.md`.
Data files: `Testing/notes/rvregen434/`. Tools: `Riscv/gen/regen434/`.

## 1. Generation
- Sail `97aa617dc` (sail2 HEAD; the newest tag `0.20.3` predates the 4.34 port) was built with opam/OCaml 5.2.1.
  Nothing was blocked, except that `codeload.github.com` returns 403. Only the C-emulator dependencies are fetched
  from there, and they are switched off with upstream's `DOWNLOAD_*=OFF` options.
- sail-riscv `b7d1357` is the same input as the trusted model. It generated without problems (408 s).
- **Provenance of the trusted model confirmed:** Sail `8eb1fb6b` with sail-riscv `b7d1357` reproduces `51c635c`
  byte-for-byte (all 160 `LeanRV64D/*.lean`, the root file, `lakefile.toml`, `lean-toolchain`). So every difference
  below comes from Sail `8eb1fb6b..97aa617dc` and lean-sail `v5 → v10`. The RISC-V specification text is the same.
- Source diff vs `51c635c`: `rvregen434/model.diff.gz` (full, applies with `git apply`) and `model.diffstat`
  (164 files, +14511/-31093). `ZicsrInsts.lean` alone is -24000 lines: `read_CSR`/`write_CSR`
  are now if-chains instead of one huge `match` (see §3).

## 2. Build on Lean 4.34.1 (serial, one `lake build <module>` at a time)
All 160 modules build with 0 errors and no `sorry`. That includes `DeviceTree`, which failed on `51c635c` and on the
hand-edited model (`prefix` keyword; fixed by Sail `c44944f1`). Total 598 s. Heavy modules (time / peak RSS):
`InstsEnd` 201 s / 2.9 GB, `PlatformConfig` 77 s / 2.2 GB, `Defs` 54 s / 2.4 GB, `HexBits` and `HexBitsSigned` 9 s / 1.7 GB,
`ZicsrInsts` 7 s (61 s on the hand-edited model). Everything else is under 5 s. Peak RSS is 2.9 GB, which includes about
1.6 GB of mapped imports. Per-module data: `rvregen434/build_model_434.tsv`.

## 3. Definition-level comparison
Two methods.
- **Raw** (`Dump.lean`, unchanged from `rv434-experiment`): name, module, kind, universes, `Expr.hash` of type and value.
  The probe line is identical on all three dumps. It is compared on the 123 modules of the 4.29 dump.
- **Normalized** (`NDump.lean`, new): mdata stripped, binder names erased, the `let` nonDep flag erased, `assert`
  renamed to `sail_assert`, and every reference to an auxiliary constant (`match_N`, `_sparseCasesOn_N`, `_f`, `_unary`,
  `_mutual`, `proof_N`, `eq_N`, private or hygienic names) replaced by the normalized hash of its body, recursively.
  So aux renumbering does not count as a change, but a change *inside* an aux constant does.
  This needs both models in one toolchain, so the hand-edited model was rebuilt on 4.34.1 for it.

### (a) vs the original 4.29 model (raw; `rvregen434/cmpA.*`)
16,227 constants vs 16,055 (same modules): 15,197 identical, 842 changed (829 value, 13 type+value; 833 defs, 9 thms),
188 only in the original, 16 only in the regenerated model.
- 169 of the 188 removed are `T.toCtorIdx`: Lean 4.34 no longer generates them (toolchain, as on `rv434-experiment`).
  18 are aux renumberings (`match_N`, `_sparseCasesOn_N`, `_hyg` names). The last one is `LeanRV64D.assert`, now `LeanRV64D.sail_assert`.
- Of the 826 changed non-aux constants, 212 differ after normalization (see (b)). The other 614 differ only by
  the `assert` rename, `cleanup.letToHave false` (lets stay `let`; they were `have`), mdata or binder names, aux renumbering,
  or the toolchain-side changes listed in `RV_MODEL_434.md` (derived `BEq`/`Repr`, xor instance, `Int.Internal.Linear`).

### (b) vs `rv434-experiment` (hand-edited 51c635c on 4.34.1)
Raw: 836 changed, 17 only hand-edited, 12 only regenerated. **Normalized: 12,394 constants; 12,172 equal,
222 values differ, 0 types differ, 0 removed, 11 new.** Normalized lists: `rvregen434/ncmp.{changed,onlyA,onlyB}.txt`.
11 constants have equal raw hashes but differ normalized: they reference a `_mutual`/`_unary`/`_f` aux constant whose body
changed under the same name, which the raw method cannot see.

**11 new constants** (Sail `c9bee615`, type-abbreviation extensions, and the effect-printing helpers):
`is_fp_bits`, `is_mem_width`, `is_sew_bitsize`, `is_sv_mode`, `nfields_range`, `nfields_range_pow2`,
`valid_misaligned_order` (`Defs`: `abbrev` predicates for Sail integer-set types, e.g. `is_fp_bits k := k ∈ [16,32,64,128]`),
and `prerr_effect`, `prerr_bits_effect`, `prerr_endline_effect`, `prerr_int_effect` (`SpecializationV1`).
`sail_assert` replaces `assert` (same body shape: `PreSail.sail_assert p s`).

**222 changed values, by cause** (per-constant classes: `rvregen434/final_classes.tsv`; normalized token diff per function:
`rvregen434/fdiff.txt`):

| class | # | cause (Sail commit) | effect |
|---|---|---|---|
| short-circuit | 160 (+13 also unit-stmt) | `e55d89e7` "support short-circuiting && \|\| with effects" | `pure ((← a) && (← b))` becomes `a <&&> (do b)` (also `<\|\|>`). **Semantic:** b's effects (register reads, exceptions, asserts) now run only when a does not decide the result, which is Sail's semantics. Before, both sides were always run. Results agree when b's effects are pure reads that cannot fail. Covers most `execute_*` (vector/FP: the `illegal` checks), `encdec_*`, `check_CSR`, `currentlyEnabled`, `haveDoubleFPU`/`haveHalfFPU`/…, `legalize_*`, `is_*_accessible`, `config_is_valid`, `amo_encoding_valid`, `vmem_*`, `wF`/`wV`/`wX`, … |
| unit-stmt ascription | 35 (+13) | `47530a5e` (legacy-do typing workaround) and `1bd6e8fd` (assignment lifting) | statements become `let _ ← ((do S) : M Unit)`. Same computation; the term has an extra bind with a discarded unit binder. Covers `fetch`, `fetch_bytes`, `checked_mem_read/write`, `pt_walk`, `translateAddr`, `trap_handler`, `exception_handler`, `tick_clock`, `run_hart_active`, `reset_sys`, `mem_write_ea`, `htif_*`, `clint_*`, `execute_MRET/SRET/FENCE/AMO/ZICBO*/SSRDP/VLRE/VSRE`, … |
| match → if-chain | 4 | `0f510569` (rewrite `if exp == lit` when BEq is not supported) and `2f5dcd13` (no mixing of vector and bitvector-literal patterns) | `read_CSR`, `write_CSR` (68.5k → 4.5k / 6.5k tokens), `fence_bits_forwards{,_matches}`: `match b with \| 0x301 => …` becomes `if b == 0x301#12 then … else …`. Same function for literal patterns. Very different terms, and the aux `match_N` constants are gone. |
| mutual partner | 4 | none (text unchanged) | `check_stateen_bit`, `get_hstateen`, `get_xLPE`, `is_zfinx_enabled_by_stateen` are in a `_mutual` block with changed members |
| `do` after `let x ←` | 3 | `322a415d` "always print do in effectful let-binding" | `execute_VAESKF1_VI`, `execute_VAESKF2_VI`, `get_sstateen`: `let w ← do …` opens a nested do-block, which elaborates differently. Expected to be equal by the monad laws (not checked). |
| FakeReal | 2 | lean-sail / Sail library | `round_down`: `x.toUInt64.toNat` → `x.floor.toInt64.toInt` (the old version was wrong for negative and fractional inputs). `round_up`: `round_down (x+0.5)` → `x.ceil…`. **Semantic** (only reaches float-to-int "real" helpers). |
| `main` | 1 | `3626605b` (main file imports everything) | the generated `main` entry |

Not checked in the kernel: no `rfl`/bisimulation proof that old and new compute the same function. The short-circuit and
FakeReal classes are not equal in general. They are behaviour fixes in Sail's Lean output.

## 4. Repo modules against the regenerated model (Lean 4.34.1)
See §5 (filled in when the build finishes).
- `Riscv/Back/BootReset.lean`: `resetSysWith` is a hand copy of `reset_sys` with the reservation hook as a parameter. **Hand copy
  re-synced with the model REGENERATED with Sail 97aa617dc**: the `Ext_Zicfilp` branch is now `let _ ← ((do if … ) : SailM Unit)`
  as in the model. With the old copy `reset_eq : reset () = resetWith (cancel_reservation ()) := rfl` did not terminate (>150 s);
  with the re-synced copy it checks in 1 s. Only the statement shape changed, not the proof.
- `Riscv/Back/BootV.lean` `wr_misa`, `acc_misa`, `se_misa` (`by rfl` through the new `if b == 0x301#12` chains of `write_CSR` /
  `is_CSR_accessible`): pass unchanged when checked against the model alone (4 s each).

## 5. Conformance / fuzz tests
The repo's Sail tests (`Testing/asm/*_test.py`, `cosim.py`, FUZZ6–10) run the Sail **C emulator** binary
(`deps/sailsim/.../sail_riscv_sim`). They do not execute the Lean model, so they cannot detect a difference between
Lean models. Running them would not test this change. The checks that do exercise the Lean model are the
kernel-checked step lemmas in `Riscv/Steps` and `Nano/V2Self/Proof/Machine` (§4).
