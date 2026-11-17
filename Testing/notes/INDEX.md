# Notes index (harvested from branches, harvest2)

One line per note: name (file in this folder), source branch, summary.

- IR_DESIGN.md — ir-design — Design for one shared IR; no compiler code changed.
- IR_S3.md — ir-s3 — S3 calculus (Compiler/S3), proved once through the IR (S3.compile_correct); front end s3_compile; 15 functions verbatim incl. inductive + structure, QEMU + Sail.
- COMPCERT_MINING.md — compcert-mining — Ideas to take from CompCert (ideas only).
- CONLECHE_DEPTH.md — conleche-depth — Call-graph depth probe of the con-leche checker core through the front ends.
- CONLECHE_TARGETS.md — conleche-targets — Con-leche blocking targets classified by first failure (type gate).
- LEANSVG_DEPTH.md — leansvg-depth — Depth probe of lean-svg `render` call graph vs the front ends.
- LEANSVG_TARGETS.md — leansvg-targets — Lean-svg blocking targets derived from the depth probe.
- LEANZIP_DEPTH.md — leanzip-depth — What blocks a verbatim lean-zip `inflate` (and gzip/zlib decode).
- LEANZIP_TARGETS.md — leanzip-targets — What each blocked lean-zip inflate function needs, and what landed since the probe.
- SELFHOST_DEPTH.md — selfhost-depth — Depth probe of the compiler's pure core through the front ends.
- BUILD_PROFILE.md — build-profile — Per-module build timing of Spec/Compiler/Riscv/Frontx and a speed-up plan; no source changed.
- BUILD_CACHE_TEST.md — build-cache-test — Test of restoring the build cache and running `lake build Frontx`.
- MIXHASH.md — mixhash — Facts about Lean core `mixHash` and the con-leche computed hash fields.
- BOOK_SURVEY3.md — booksurvey3 — Survey of the pure functions in "Functional Programming in Lean" against main.
- TINYSELF2.md — tinyself2 — Growing the self-hoster with the inductive path.
- FUZZ6.md — fuzz6 — Differential tests of the NOTES §18–21 entries.
- FUZZ7.md — fuzz7 — Differential tests of multiply / divide / remainder / variable shifts (§22).
- FUZZ8.md — fuzz8 — Differential tests of the strings / Name entries (§23).
- FUZZ9.md — fuzz9 — Differential tests of the Expr (§25) and higher-order (§27) entries.
- CONLECHE_S0.md — conleche-s0 — Con-leche batch functions with number % 4 == 0 through frontx_ind.
- CONLECHE_S1.md — conleche-s1 — Con-leche batch functions with number % 4 == 1.
- CONLECHE_S2.md — conleche-s2 — Status note for con-leche batch functions with number % 4 == 2 (root-level file on the branch; not completed).
- CONLECHE_S2_frontx.md — conleche-s2 — Second CONLECHE_S2 note on the same branch (Testing/notes/frontx/CONLECHE_S2.md); number % 4 == 2 batch functions, not completed.
- CONLECHE_S3.md — conleche-s3 — Con-leche functions with number % 4 == 3.
- BOOK_S1.md — book-s1 — First third of the book survey's blocked rows, retried on main.
- BOOK_S2.md — book-s2 — Second third of the book survey's blocked rows, retried.
- BOOK_S3.md — book-s3 — The 13 blocked rows in the last third of the example files.
- ZIPSVG_S1.md — zipsvg-s1 — Retries of lean-zip / lean-svg rows that NOTES §22 may have unblocked (variable `*`, `/`, `%`).
- IR_C_ORACLE.md — ir-c-oracle — Work in progress: untrusted IR-to-C printer and a gcc/QEMU comparison oracle.
