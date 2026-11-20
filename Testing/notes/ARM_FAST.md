# ARM_FAST: making the ARM side fast to build and prove, soundly

Research and proposal only. No source was changed. Measured on this box (4 cores, 15 GB, no swap), Lean 4.34.1,
2026-11-19, model = `Arm/model` as committed (34 modules, 577k lines, 34,905 declarations).
"Measured" below means run here today. "Static" means a token-level reachability analysis of the model source
(every identifier in a declaration body that names another declaration is an edge; this over-approximates).
"Quoted" means taken from an existing README or note and not re-run.

## 0. Recommendation

1. **Cache the built model** in `build-cache` (there is no ARM tarball there today). This removes the model build
   from every box. It is needed whatever else is done, because any theorem about `stepModel` needs the full model.
2. **Generate a core slice of the model as a partition of the same declarations** (`Armv9Core` + rest), and prove
   everything that does not mention the top-level decoder against the core alone. The core builds from source in
   about 4.5 minutes and its oleans are 42 MB compressed. No equivalence theorem is needed (§2).
3. **Put the decoder and the full step in one thin glue layer** (`SymDec` + `Step` + `full_gen`), the only proof
   files that import the full model. Everything above consumes the `full_*` laws through `JTarget.step_ok`.
4. **Take `Words.lean` out of the default build.** It is 63% of today's ARM check time and serves only the old
   216-word expression compiler. The symbolic-field method of `SymDec.lean` replaces it.
5. Do not use DeepMind's semantics as the working model (§5).

Expected result: ARM day-to-day loop = restore 42 MB, or build the core in 4.5 min, then about 80 s of proof
checking for the core layer (measured file times, serial). The glue layer adds an estimated 2 to 3 minutes against
cached full-model oleans.

## 1. Measurements

### 1.1 What the 15 instructions reach (static)

Roots: the 39 `decode_*_aarch64_*` functions for movz/movk, add/sub imm and shifted-reg, subs imm and reg, and/orr/eor,
lslv/lsrv/asrv, madd, csinc/csel, b, bl, b.cond, cbz/cbnz, br/blr/ret, ldr/str (unsigned, pre, post), ldrb/strb,
ldur/stur; plus `__FetchInstr`, `__TopLevel`, `__CycleEnd`.

| set | declarations | lines | reaches `Reduce__1` |
|---|--:|--:|---|
| whole model | 34,905 | 577k | yes |
| the 39 decode functions (with their execute functions) | 1,632 | 26.5k | no |
| step without the decoders (`__FetchInstr`, `__TopLevel`, `__CycleEnd`, stopping at `__DecodeA64/A32/T32/T16`) | 1,998 | 30.1k | no |
| **slice** = both of the above | 2,139 | 33.4k | no |
| `__TopLevel` with the decoders | 15,527 | 522k | yes |
| `__DecodeA64` alone | 12,027 | 380k | yes |

Per A64 decoder group (reachable lines): `DataProcImm` 13k, `DataProcReg` 16k, `LoadStore` 49k, `BranchExcSys` 186k
(MSR/MRS pull in 134k lines of `SysregsAutogen`), `DataProcFPSIMD` 42k, `SVE` 115k, `SME` 77k.
`Reduce__1` is reachable only through `DataProcFPSIMD` and `SVE`. The four groups our words decode through do not
reach it. `Reduce__1` has two call sites in the whole model, both in `Instrs64.lean` (SIMD reduce).

So a pruned top-level decoder is not small unless `BranchExcSys` is also pruned inside. The slice therefore
stops below the group decoders: it contains the per-instruction decode and execute functions, not `__DecodeA64`.

### 1.2 The slice, generated and compiled (measured)

A 60-line prototype script (kept in the session scratchpad, not committed) copies the model and, in every module that
imports `V8Base`, keeps only the reachable declarations, verbatim and in their original order. It removes the
`DecodeEnd` import from `Fetch` and drops the 8 declarations of `Fetch` that call a decoder (`ExecuteA64` …
`__TopLevel`). Extra roots: every model name mentioned in `Arm/proofs/Arm/{Base,Exec,Flags,Hooks,Fetch,Mem,Branch,
BrFull,Ret}.lean` (909 names, mostly bitfield getters in simp sets; they add about 900 lines).

| | full model | slice |
|---|--:|--:|
| `V8Base` | 24,178 decls, 123k lines | 2,145 decls, 27.7k lines |
| `Instrs64` | 1,365 decls, 42k lines | 52 decls, 2.3k lines |
| `Fetch` | 17 decls | 9 decls |
| `SysregsAutogen`, `Instrs32`, `Instrs64Sve`, `Instrs64Sme`, `DecodeEnd` | 422k lines | nothing kept |
| total lines (small modules kept whole, `Defs` 5.5k) | 577k | 40.0k |
| build `V8Base` | **did not complete**: killed for memory at 1076 s (beside another build) and at 1312 s (alone); see §1.5 | **170 s** alone (221 s beside another build) |
| build from source, whole thing | not measured here; `DecodeEnd` alone about 20 min (quoted, `Arm/gen/DIFFS.md`) | **about 4.5 min**: Sail library 10 s, `Defs` 65 s, small modules 15 s, `V8Base` 170 s, `Interrupts`+`Instrs64`+`Fetch` 15 s |
| build output | not measured; estimate 1.1 to 1.2 GB (1.7 kB per line as in the slice, plus `Defs`) | 216 MB (`Defs.olean` is 132 MB of it); **42 MB** as `tar | zstd -3` |
| importing it in a new file | — | about 1 s |

The slice compiles with 0 errors. That shows no kept declaration needs a dropped one, including for elaboration.
The sliced modules contain only `def`s, doc comments and one `termination_by`; all 45 instances of the model are in
`Defs.lean`, which is kept whole.

### 1.3 Existing proofs against the slice (measured)

Five files of `Arm/proofs` were compiled against the slice with one edit: the import line of `Base.lean`
(`Armv9.DecodeEnd` → `Armv9.Instrs64`). None of them mentions the decoder.

| file | theorems | against the slice | against the full model (quoted, `Arm/proofs/README.md`) |
|---|--:|--:|--:|
| `Base` | 28 | 26.8 s | ~31 s |
| `Exec` | 17 | 28.6 s | ~36 s |
| `Flags` | 6 | 1.1 s | ~1 s |
| `Hooks` | 47 | 18.6 s | ~22 s |
| `Fetch` (incl. `fetch_ok`) | 18 | 4.4 s | ~6 s |

All pass unchanged. `#print axioms` of `fetch_ok`, `__FetchInstr`, `__CycleEnd` and the madd/ldur/blr decode functions
on the slice: `propext`, `Classical.choice`, `Quot.sound`.

**Proof checking is not faster on the slice.** Times are within noise of the full-model times. Import cost is small
either way (oleans are memory-mapped). The slice buys build-from-source time, memory and cache size. It does not buy
tactic speed.

### 1.4 Where today's ARM check time goes (quoted, `Arm/apc/README.md`, 2026-11-15)

`Arm/proofs/check.sh`: 1016 s, one process, serial. `Words` 637 s (63%), `Witness` 108 s, `SymDec` 40 s, `Exec` 36 s,
`BrFull` 35 s, `Base` 31 s, the other 12 files 129 s together. `Words` proves 216 concrete words by unfolding the whole
group decoder once per word. `SymDec` does the same job for a symbolic word in about 2.5 s per instruction form
(14 forms, 35 to 40 s).
`check.sh` calls `lean -o` in a loop. It has no parallelism and no staleness check.

### 1.5 Building the full `V8Base` (measured, partial)

`V8Base` needs about 12 GB (quoted). Here it was at 6.7 GB after 4 minutes. A second `lean` process beside it (the
2.4 GB slice build) got one of them killed (exit 137) at 1076 s. So on a 15 GB box the heavy modules (`V8Base`,
`SysregsAutogen`) must build alone, and lake's parallelism does not help the model build.
A second run of `V8Base` alone was also killed for memory (exit 137) after 1312 s; it was at 12.8 GB after 769 s.
**The full `V8Base` could not be built in this session** (16 GB total, about 15.4 GB free before the build). The
model has been built on a box of this size before (quoted), so the margin is a few hundred MB. A from-source full
build is therefore not a dependable step on these boxes, which is the strongest argument for options 1 and 3.

### 1.6 Parallelism available inside `V8Base` (static)

The dependency graph of `V8Base`'s 24,178 declarations has depth 36. Its longest path is 3,470 lines of 123k
(ratio 35). 60.8k lines are never referenced inside `V8Base`. So `V8Base` can be cut into several modules that build
in parallel, each with a fraction of the peak memory. This only speeds up the one build that fills the cache.

## 2. Is the slice sound? (a)

Three ways to justify it, in order of preference.

**A1. Partition, not copy (recommended).** Lean identifies a constant by its name, not by its module. So generate
the model as two layers: core modules holding the reachable declarations, and the original modules holding the rest
and importing the core. Namespaces stay `Armv9.Functions`. Then:
* the full model **is** core ∪ rest: the same names, the same definitions;
* a proof compiled against the core imports only core oleans, and the full build uses those same olean files;
* so a theorem proved on the core is a theorem about the full model's own constants. There is nothing to prove equal.

What is trusted in addition: the partition script moves text verbatim. The dependency direction is right by
construction (the core is closed under references; the rest keeps its original order and may import all of the
core), and a wrong cut fails to compile. The one way it could change a definition silently is elaboration that
depends on a declaration which is no longer in scope (instances, overloads). Check for that mechanically, once per
regeneration: dump (name, hash of type, hash of value) for every `Armv9.*` constant from the unpartitioned build and
from core ∪ rest, and `diff`. The dump takes 1 s on the slice (12,920 constants). The comparison itself was **not run**: it needs a full `V8Base`
build, which did not complete here (§1.5).
Cost: about 1 to 2 days (script into `Arm/gen/regen.sh`, lakefile, the diff as a check, one full rebuild).

**A2. Separate copy plus one equality theorem per definition.** Needs both copies in one environment under different
names, shared types, and about 2,100 `Slice.f = Full.f` proofs in dependency order. More work, more build time, and
it proves less than A1 gives for free. Not recommended.

**A3. Decode-prune lemmas (`SymDec` style).** `__DecodeA64 pc w s = decode_X fields s'` from `w &&& K = T`. These
are theorems of the full model. They are not an alternative to the slice: they are the link from the top-level
decoder to the per-instruction functions, and every design needs them. 14 exist. About 16 more are needed (the
register-register ALU forms, subs, csinc/csel, madd, lsl/lsr/asr-v, br/blr, ret symbolic, ldur), at about 2.5 s each.

A slice with its own pruned `__DecodeA64` (a different function under a new name) is not recommended. It would be a
second definition of the step, it would need the full model anyway to be related to the real one, and §1.1 shows
the pruned decoder is still large unless it is rewritten by hand.

## 3. Step lemmas that never reference `Reduce__1` (b)

Two layers, with different answers.

* **Per-instruction layer** (decode function + execute, fetch, memory access, hooks, cycle end): yes. The slice does
  not contain `Reduce__1` at all (static and compiled), so no lemma there can depend on it. This layer is where
  nearly all the proof work is.
* **Full-step layer**: no, and it cannot. `stepModel` calls `__TopLevel`, which calls `__DecodeA64`, whose body names
  all ten group decoders. Any statement about `stepModel` has `Reduce__1` among the constants it depends on.

That dependence is harmless as generated today. `Reduce__1` is a `partial def`, which the kernel sees as an opaque
constant with no axiom. `#print axioms __DecodeA64` gives the three standard axioms (quoted, `Arm/gen/DIFFS.md`; not
re-run here, no full build). `sorryAx` would come back only if the model were regenerated without
`--lean-partial-function Reduce__1`. Make that fail loudly: `regen.sh` asserts that `partial def Reduce__1` is in
`V8Base.lean`, and the final axioms file stays the gate.
`partial` costs nothing for us: nothing can be proved about SIMD reduce, which we never execute.

The layering to use (it is what `Step.lean`'s `step_ok` and `BrFull.lean`'s `full_gen` already do):

| layer | imports | contents | changes |
|---|---|---|---|
| K (core) | `Armv9Core` | `Base`, `Flags`, `Exec` forms, `Hooks`, `Fetch`, `memreadG*`/`memsetG*`, `*_exec` | often |
| G (glue) | full model | `dec_*sym` (A3), `step_ok`, `full_gen`, `full_*` = K lemma + `dec_*sym` + `step_ok` | rarely |
| T (target) | G's statements | `armTarget.step_ok` for `JTarget` | per J instruction |

Above T the proof is generic over `JTarget` and model-free. Today `Mem.lean` and `Branch.lean` mix K and G content
(they import `BrFull`/`Machine`), and `SymDec` imports `Machine` → `Full` → `Words`. Those imports need to be cut.

## 4. Build-time tactics (c)

| tactic | finding |
|---|---|
| prebuilt oleans in `build-cache` | No ARM model there today (only `sail-riscv-lean`, `sailsim`, `repo-build`). Add `armv9-core` (42 MB measured, one blob) and `armv9-full` (estimate 250 MB compressed, 3 parts of 90 MB). Name each tarball by toolchain and the git tree hash of `Arm/model`. Build with lake, not `lean -o`: lake compares source hashes, so a stale cache rebuilds instead of being used silently. Include root-level `.lake/packages/Sail` (`BUILD_CACHE_TEST.md` found that the dependency-level copy is ignored). |
| splitting `V8Base` | Possible and mechanical (§1.6), same soundness argument as A1. Only helps the build that fills the cache. Do it only if that build has to run on 15 GB boxes or often (for example during the 4.35 migration). |
| `--tstack` | Already set (`--tstack=400000` in the model lakefile and `check.sh`). It is needed for deep terms. It is not a speed setting. |
| parallelism, model | Blocked by memory on this box (§1.5). A 32 GB box could build `SysregsAutogen` and the `Instrs*` modules together after `V8Base`. |
| parallelism, proofs | `check.sh` is serial. As a lake library the proof files build in parallel. Without `Words`, `Compiler`, `Full`, `Machine` and `Witness` the remaining files sum to about 240 s serial. |
| `Words.lean` | Remove from the default target (keep as a legacy target for `compile_ok` and `apc_eq_sail`). Symbolic `dec_*sym` lemmas cover every register and immediate in about 2.5 s per form. |

## 5. DeepMind's arm64 semantics as the working model (d)

Sound: the bridge theorems (`bridge_step`, `sim`, `simM`) are proved with the three standard axioms, and the final
statement stays on Sail's `stepModel`. But it does not save Sail work and it adds work.

* Each bridged instruction needs the Sail full step (`full_*`) as an input. That is the expensive part, and it is the
  same lemma the direct route needs. The bridge then adds a DeepMind step and an agreement proof on top.
* Not bridged today: `ldr`/`str`/`stur` (8 bytes), `ldur`, `cbnz`, `madd`, `br`/`blr`, the SP forms.
* Build cost (quoted): `arm64` 162 s on first build, Apc 414 to 434 s (`WideDec` 345 s), bridge 205 to 229 s.
* The memory models differ (permissions, W^X, no alignment rule against Sail's aligned-only 8-byte accesses), so
  every run carries `MemRel`/`CodeOK` side conditions.
* Their toolchain pin is 4.34.0. The planned move to 4.35 would have to carry their package too.
* Its real advantage, a small executable model for program-level proofs, is already provided by J: with `JTarget`
  the program-level proof never sees a machine model.

Keep `Arm/apc` as a cross-check that two independent models agree on the forms already bridged. Do not put it on
the path of the main theorem.

## 6. Other (e)

* **One instantiation file.** With `JTarget`, only layer K, layer G and the file that defines `armTarget` import the
  model. The roughly 400 modules above J never do. This matters more than any model-side speed-up.
* **Build the cache on a bigger box once.** 32 GB lets the heavy modules overlap.
* **`Defs.lean`** (65 s, 132 MB olean, the register type) is needed whole by every option. It is the floor for a
  from-source build of anything.
* **A termination proof for `Reduce__1`** upstream (the Sail constraint on the width is not in the Lean type) would
  remove the opaque constant. Not needed for this back end.

## 7. Ranked options

| # | option | cost | soundness argument | expected build time |
|---|---|---|---|---|
| 1 | Model oleans in `build-cache` (full and core) | one full model build per (model, toolchain), about 30 lines of script | same source files; lake rechecks source hashes | restore in seconds instead of a full build that did not fit in memory here |
| 2 | Layers K/G/T as a lake library; `Words` out of the default target; missing `dec_*sym` forms | about 2 days (import cuts, about 16 new forms; the missing full steps are already costed at about 1,200 lines in `NANO_V2_ARM.md`) | unchanged: same theorems, same model | proofs about 240 s serial instead of 1016 s, less in parallel (estimate) |
| 3 | Core slice by partition (A1) | 1 to 2 days | same constants; verbatim move; hash diff per regeneration | core from source 4.5 min (measured); layer K about 80 s (measured file times) |
| 4 | Split the rest of `V8Base` (and `SysregsAutogen`) for parallel, low-memory builds | 1 day after 3 | as 3 | affects only the cache-filling build; up to about 3× on 4 cores (estimate from §1.6) |
| 5 | DeepMind semantics as working model | at least 6 more bridge forms plus memory relation for 8-byte accesses | sound (proved bridge) | slower: adds about 10 min of builds and does not remove any Sail lemma |
| — | Separate slice with equality theorems (A2); slice with its own pruned decoder | high | weaker or redundant | — |

## 8. Not verified

* Full-model build time and olean size (§1.5): no full build completed here.
* The hash comparison of A1 (slice constants against the unpartitioned build) was not run, for the same reason. Until
  it is, "same definitions" rests on the verbatim text move and on the 116 existing theorems checking unchanged. The 250 MB cache estimate is extrapolated from the slice.
* `#print axioms __DecodeA64` on the full model was not re-run here.
* The reachability analysis is token-based. It can only over-approximate, and the compile of the slice confirms it is
  closed. It was not checked that the slice is minimal.
* `Mem.lean`, `Branch.lean`, `BrFull.lean` and `Ret.lean` were not compiled against the slice (their imports go
  through the decoder layer today). Their model references are in the slice's roots.
* Peak memory of the sliced `V8Base` build was not recorded (2.4 GB after 60 of 170 s).
* Parallel wall times in §4 and §7 are estimates.
