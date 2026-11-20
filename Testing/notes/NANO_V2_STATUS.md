# NANO v2 notes: index and status (2026-11-19)

Start with `Nano/V2Self/README.md` (layout, final theorems, how to rebuild) and `Nano/V2Self/REVIEW.lean`.

## Current: read these
| note | what |
|---|---|
| NANO_V2_REVIEW.md | owner review: the final theorems, what to trust, caveats, axioms |
| MODEL_PROVENANCE.md | the machine models (Sail RISC-V, Sail ARM, DeepMind arm64): commits, generators, patches, toolchains, which theorems use which |
| BRANCHES.md | branches, Lean versions, what is proven and trusted where |
| NANO_V2_AUDIT.md | soundness / loophole audit (G). Finding A is fixed; finding B (acceptance not kernel-proved) is open |
| NANO_V2_MAIN.md | the end-to-end statement and the stage structure (D) |
| NANO_V2_SPRINT.md | open sprint units (pruning O-P1..P5, others) |
| NANO_V2_DEADCODE.md | dead-code report (`Testing/scripts/deadcode.sh`) |
| NANO_V2_REORG.md | the reorganization: DONE (2a02149, cleanup 5024388 / 4d17b0a); the mapping table uses the OLD names |
| NANO_V2_ARM.md | design of an AArch64 back end for C (planned) |

## Per-component design and history (still accurate for their component, but not updated after the reorg's renames)
| note | component |
|---|---|
| NANO_V2_CG.md | C's code generator Gen and its proof |
| NANO_V2_OWN.md | the ownership stage o41, plus the parser WIDTH CAP section |
| NANO_V2_PARINV_DESIGN.md | design of the parser proof (ParInv) |
| NANO_V2_IR.md | the frozen intermediate formats (AST words, IR v2.1) |
| NANO_V2_SPEC.md | milestone 1 frozen interfaces |
| NANO_V2_SRC.md | the compiler's stages in the restricted (nano v2) style |
| NANO_V2_CHECKPOINT.md | the compiler as nano-subset source (pre-self-hosting review) |

## Historical: superseded, kept for the record
| note | why historical |
|---|---|
| NANO_V2.md | the original v2 plan (branch `nano-v2`) |
| NANO_V2_ASTRA.md | architecture advice and the decision (2026-11-17) |
| NANO_V2_BACKEND.md | the earlier small backend (`Nano/V2/*`, not V2Self) |
| NANO_V2_ROUND5.md, NANO_V2_ROUND6.md | relayed proof skeletons (rounds 5 and 6) |
