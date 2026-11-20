# Testing

Scripts and records, not proofs.

* `scripts/`: `release_check.sh` (all gates), `review_axioms.sh` (+ `review_axioms.txt`, the pinned axioms),
  `spec_check.sh`, `model_hash.sh`, `sorry_scan.sh`, `deadcode.sh`, `bigbox/` (big-machine verification kit).
  Scripts about the earlier compilers (`check.sh`, `statement_check.sh`, `axioms_*.lean`) refer to modules now in
  `Legacy/`.
* `nano/v2self/`: the self-compile fixpoint (`boot/`), examples, the ARM cross check (`arm/`), certificate and
  source-link generators.
* `riscv/gen/`: provenance and tools of the regenerated RISC-V model.
* `notes/`: design and status notes (historical paths in them predate the 2026-11-20 move).
