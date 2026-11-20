# Generated-code speed: where the instructions go, and what each fix costs in proofs

Analysis only (2026-11-20, base 947ebf5). No compiler, proof, Spec or model file was changed.
Counts are exact executed RISC-V instructions (`bench/nanorun_prof.c` per-word profile). The savings are **computed from the
profile** by matching Gen's emitted templates in the code (`bench/profile_mix.py CODE.bin PROF.bin [noconst]`); no changed
compiler was built or run, so each saving is a model of the new sequence, not a measurement of it.

## Result in one paragraph

Two cheap wins exist, and neither is on the ROADMAP list. (1) 49.6% of the self-compile runs inside constant defs, because
`Par1.lean` defines `d3 := d1 + d2 … d11 := d9 + d10` and every `d11` reference re-runs an 11-call chain; writing those five
defs as literals removes 41.6% with no compiler change. (2) `li` of a value ≥ 2048 is a fixed 17-word chain; skipping leading
zero bytes (same instructions, no `lui`) removes 10.9% today, 2.8% after (1). Every item on the ROADMAP list is PERVASIVE in
the proofs, for three structural reasons given below. No superlinear pattern was found in the emitted code.

## Dynamic mix

Self-compile = B2 compiling `self_S_input.txt`, 1,454,349,112 instructions. hex / sum = the BENCH examples on 100 KiB.
"self, folded" = the self-compile profile with every constant def replaced by `li; push` at its call site (746.3 M).

| pattern (share of executed instructions) | self | self, folded | hex | sum |
|---|---:|---:|---:|---:|
| push (`addi; bgeu; sd`, 3 executed per push) | 19.8% | 32.7% | 26.2% | 27.3% |
| prologue + epilogue + `jal ra` | 34.1% | 8.3% | 16.5% | 0.0% |
| 17-word `li` | 13.8% | 1.5% | 0.0% | 0.0% |
| BIN (pop two, op, store) | 9.2% | 10.5% | 14.6% | 22.7% |
| BGET (10 per access, bounds check included) | 6.1% | 11.9% | 0.0% | 0.0% |
| IF compare (pop two, branch) + `jal else` | 4.6% | 8.9% | 4.2% | 0.0% |
| LOCAL load / pop into slot | 6.7% | 13.1% | 11.2% | 20.5% |

By opcode (self): addi 33.7%, ld 19.8%, sd 16.7%, bgeu 13.4%, slli 7.3%, jal 3.1%, add 2.3%, jalr 2.0%, rest 1.7%.
Calls: 29.0 M in the self-compile, of which 25.5 M are calls of constant defs (21.9 M of those from other constant defs).
A constant def costs 21 instructions per call (37 if its value is ≥ 2048); `d11` costs about 250.
Example inner loop (`sum`, 44 instructions per byte; about 8 would do): 4 checked pushes, 2 BIN, RD, 2 pops into slots, 5 for fuel.

## Ranked table

"self" = share of the 1,454 M self-compile; "folded" = share of the 746 M profile after constant defs are gone (the better
predictor for ordinary programs); hex / sum = share of that program's run. Lines are rough estimates.

| # | candidate | self | folded | hex | sum | proof files touched | class | est. lines | recommendation |
|---:|---|---:|---:|---:|---:|---|---|---:|---|
| S | flatten `d3,d5,d7,d9,d11` (and `g_901/902/908`) to literals in the compiler's own source | 41.6% | – | 0 | 0 | none by hand: `ParInv.d11v : d11 = 184384 := rfl` and the other value lemmas stay true; regenerate Cert, SrcLink, B2 | LOCAL (source only) | ~10 source, 0 proof | **do first** |
| L | byte-skipping `li` (addi/slli only: 3 words below 2^16, 5 below 2^24) | 10.9% (2.8% after S) | 0.9% | 0 | 0 | `Expr` (`liT`, `li_loop`, `li_run`), `SafeRun` (`li_sr`), `ExprExact` (`g23_big`, `g23_exact`, `const_exact`), `TmGood` (`liT_good`), `MachExact` (`liT_le`) | LOCAL | 150–250 | **do second**; no push is removed, so the room semantics is untouched |
| 4a | inline literal constant defs at the call (ROADMAP 4) | 17.0% (4.2% after S) | – | 0 | 0 | Gen state gets a table; `GenRef`/`GenTop` (`Inv`, `DefC`), `NdSem.tm`/`sv`, `SemX.svF`, `MainConv*`, 3 node theorems | PERVASIVE | 600–1000 | defer; S gets most of it |
| 1 | one overflow check per function (ROADMAP 1) | 10.5% (6.5% with the re-check needed after each call) | 11.7% (10.7%) | 10.7% | 9.1% | every node contract (`EVHw`, `EVHwS`, `CapW`), `sv`/`svF`, `RoomRun`, `SafeRun`, `CapRun`, `Heap*`, `MainConv*` | PERVASIVE | 1500–2000 + a new invariant | defer |
| 2 | small-immediate right operand of BIN / compare (ROADMAP 2) | 6.1% | 11.8% | 15.5% | 13.6% | new visit mode in Gen, new `CG` constructor, `v_bin`, `v_if`/`t_if` doubled, `svF` + `MainConv*`; and/or/xor also need a new `J` constructor and an rv2arm change | PERVASIVE | 600–900 (+400 for compares) | defer |
| 2' | LOCAL as right operand loaded straight into t1 | 1.8% | 3.5% | 0 | 0 | as 2 | PERVASIVE | as 2 | defer, do with 2 |
| 3 | direct conditional branch (ROADMAP 3) | 0.8% | 1.6% | 0.8% | 2.3% | branch offsets are constants in `GoodW`, `GoodX`, `SafeX`, `encJ`, `sim_beq8`…; the IF layout `+5/+6` is in every node theorem | PERVASIVE (mechanical) | 500–800 | drop: smallest gain on the list |
| 5 | top of stack in a register (ROADMAP 5) | 3.7–6.4% | 4.2–8.6% | 5.8–7.8% | 9.1% | everything in `Machine/` | PERVASIVE | not estimated | defer; alone it is worth less than 1 or 2 |
| 6 | ARM: variable-length blocks (ROADMAP 6) | not measured (no ARM tools here) | | | | `St.wk` is a field of the J state: 28 Machine files, plus `Target`, `ArmTarget`, `ArmRA*` | PERVASIVE | 1100–2100 | defer |
| 6' | ARM: branch over the padding instead of executing it (same 4-word blocks) | not measured; 4 → 2 executed for 1-word blocks | | | | `ArmTarget.run_pads`, `ArmEnc.pad4`, `ArmRA` `e*_eq`, translator, regenerate CertArm | LOCAL | 150–300 | candidate, but measure on hardware first (a taken branch is not free) |
| P | skip the frame check when the def has no locals (`addi t6,t6,0; bgeu`) | 3.8% (0.5% after S) | 0.5% | 1.9% | 0 | prologue length 12 appears in 24 statements | PERVASIVE for the gain | – | drop |

Items 1 and 2 overlap (2 after 1 is 4.8% / 9.4%). After S + L the self-compile is about 810 M (56%). With 1, 2, 2', 3 on
top it would be about 600 M (41%); the examples would gain about 25–30%.

## Why the listed items are not LOCAL

1. **Out-of-memory is modelled exactly.** The run semantics checks room at every leaf (`SemX.leafF`:
   `if H.top + 8 ≤ sp then ok else room`, and `defSF`, `bnewS`), `CapNode` proves that a room failure reaches the OOM stub,
   and `memoryNeeded` (`thr`, `Msp`) is the least work size of that semantics. Any change that removes or moves a push
   (items 1, 2, 2', 4a, 5) changes `sv`/`svF` and with it the `MainConv*` converse proofs.
2. **Item 1 also needs a new invariant.** BNEW raises t5 inside a function, and a callee's BNEW raises it under the caller.
   A check done at function entry is stale after either. The code needs a re-check after each call (2 instructions, already
   in the 6.5% / 10.7% figures) and after BNEW, and the contracts need a budget term.
3. **Branch offsets are fixed constants** in the Sail layer (`GoodW`: beq/bltu only +2, bgeu only +2/+3/+4; one `sim_*`
   lemma per offset). Item 3 needs general offsets there and in the ARM range lemmas.
4. **The ARM translator accepts only addi/slli/srli** among I-type instructions and has no `lui`. andi/ori/xori or `lui`
   means a new `J` constructor (about 150–250 lines over 15 files) plus an rv2arm change and a regenerated CertArm.

What is LOCAL: each template has one `xT : List J`, one `x_run`, one `x_oom` and one `x_exact` lemma (push: `Call.push_run`,
`Expr.push_oom`, `SafeRun.push_sr`, `RoomRun.push_oom_srun`). A change inside one template that keeps its pushes, its length
interface and its instruction set is cheap. Item L is the only measured hot spot of that kind.

## Other slow patterns looked at

- Call sequence: 17 instructions of overhead per call (jal 1, prologue 9, epilogue 7). After S it is 8.3% of the self-compile.
  Cheaper forms change the prologue length (see P).
- Fuel: 5 instructions per loop iteration (`ld; beq; jal; addi; sd`), 0.75% of the self-compile, 11% of `sum`. Item 3 removes one.
- CONTINUE pushes the whole new state and pops it into the slots: 6 per state word after the value is computed. A LET of a
  just-pushed value does the same (`sd; ld`): 0.5% self, 10.4% of `maxbyte`. Removing either changes the pushes, so reason 1 applies.
- BGET: 10 per access with the bounds check; the semantics needs the check. At most 1–2 could go.
- Result copy in the epilogue: 2 per result word; small.
- Superlinear patterns in the emitted code: none found. The K^2 compile cost in BENCH.md is the same constant-def chain:
  the hot "return stubs" there are `d1…d11`, called per def and per lookup. S should remove most of it (not re-measured).

## Recommendation

1. **S**: literals for `d3, d5, d7, d9, d11` in `C/Par1.lean` (and optionally `g_901/902/908` in `C/Gen.lean`). About 41.6%
   of the self-compile, no hand proof expected to change. Check: the fixpoint, the regenerated Cert/SrcLink, `ParInv` builds.
2. **L**: byte-skipping `li` in `g23`. 10.9% today, 2.8% of the original count after S; helps any program with constants
   ≥ 2048, nothing on the BENCH examples. About 150–250 proof lines in 5 files.
3. Nothing else on the list meets "LOCAL and ≥ 10%". When the deferred speed phase starts, do items 1 and 2 together in one
   pass over the room semantics (they share the `svF`/`MainConv*` cost): about 20% of the folded profile and 20–25% of the examples.

## Reproduce

```
cc -O2 Testing/nano/v2self/bench/nanorun_prof.c -o nanorun_prof
NANORUN_PROF=self.prof ./nanorun_prof Testing/nano/v2self/B2.bin Testing/nano/v2self/self_S_input.txt out.bin
python3 Testing/nano/v2self/bench/profile_mix.py Testing/nano/v2self/B2.bin self.prof            # mix + savings
python3 Testing/nano/v2self/bench/profile_mix.py Testing/nano/v2self/B2.bin self.prof noconst    # after folding constant defs
```
`profile_mix.py` asserts that every function entry and every pop-two site matches a known Gen template, so it fails on a
code generator it does not know. The proof-cost column comes from reading the proof files, not from trying the changes.
