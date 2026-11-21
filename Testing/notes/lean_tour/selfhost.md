# Lean 4 self-hosting and trust (read at tag v4.34.1, commit 5045d00) vs nano

All paths are in github.com/leanprover/lean4 at v4.34.1. Counts measured on that checkout.

## 1. How Lean builds itself (plain language)

Lean's compiler/elaborator is written in Lean. To build it you need a Lean — a chicken-and-egg problem.
Lean breaks the cycle by **checking into git the C code that an older Lean generated from its own sources** (`stage0/`, ~2500 `.c` files, 591 MB).
The build is a ladder; each rung is built by the rung below:

```
 stage0/stdlib/*.c  (checked-in generated C, frozen, NOT from the current commit)
        | cc + C++ runtime/kernel in stage0/src
        v
   stage0/bin/lean        "blackbox bootstrap binary"
        | compiles current src/**/*.lean  (ignores its own old stdlib; everything is `prelude`)
        v
   stage1  = new .olean + new generated C -> cc -> stage1/bin/lean     (what `make` gives you)
        | compiles src/**/*.lean again
        v
   stage2  (only to test compiler/format changes on the compiler itself)
        | again
        v
   stage3;  CI does `diff stage2/bin/lean stage3/bin/lean`  == fixpoint check (CMakeLists.txt:238)
```
Moving `stage0/` forward = **update-stage0**: copy stage1's generated `.c` files over `stage0/`, commit
("chore: update stage0"). Needed when the library starts using a new language feature the old stage0 can't compile.
The kernel (C++), runtime (`lean.h`), and the `lean` driver are NOT regenerated: they are ordinary C++ built from `src/` at every stage.
Nothing proves stage0.c corresponds to the Lean source: it is trusted by convention and reviewed by CI.

## 2. File map

| What | Where | Role |
|---|---|---|
| Doc of the whole scheme | `doc/dev/bootstrap.md:1-66` (stages), `:68-107` (update-stage0), `:109+` (complications) | authoritative explanation |
| Stage driver | `CMakeLists.txt:145-205` | ExternalProject `stage0` (src dir = `stage0/`), `stage1` (PREV_STAGE=stage0), `stage2`, `stage3` |
| Fixpoint check | `CMakeLists.txt:238` `check-stage3` = `diff stage2/bin/lean stage3/bin/lean` | byte-identical binaries |
| update targets | `CMakeLists.txt:207-209`; `src/CMakeLists.txt:1022-1030` | forward to stage1 `update-stage0[-commit]` |
| Update script | `script/lib/update-stage0` (40 lines) | `rm -rf stage0`, copy every tracked non-Lake src file, replace each `.lean` by the `.c` stage1 emitted, `git add` |
| Rebase helper | `script/rebase-stage0.sh` | regenerate stage0 commits after rebase |
| Auto-update CI | `.github/workflows/update-stage0.yml`; trigger = `src/stdlib_flags.h` differs from `stage0/src/stdlib_flags.h` | bot commits new stage0 on master |
| CI stage runs | `.github/workflows/build-template.yml:142,333,337,348` | build stage2, check-stage3, run update-stage0 |
| Stage overrides | `stage0/src/stdlib_flags.h` (options forced only in stage0, e.g. `proofAsSorry`, `prefer_native`) | escape hatches for bootstrap breakage |
| C emitter (written in Lean) | `src/Lean/Compiler/LCNF/EmitC.lean` (Lean IR -> C text) | produces the checked-in `.c` |
| IR pipeline | `src/Lean/Compiler/LCNF/`, `src/Lean/Compiler/IR/` (ToIR.lean, Checker.lean, EmitLLVM.lean) | LCNF -> IR -> C/LLVM; IR has its own `Checker` (type/arity sanity, not semantic) |
| Runtime ABI | `src/include/lean/lean.h` (installed as `runtime/lean.h`) | what generated C calls |
| Kernel (trusted checker) | `src/kernel/` — 8071 lines C++ total; `type_checker.cpp` 1373, `inductive.cpp` 1417, `environment.cpp` 315, `quot.cpp` 123 | `environment::add` (`environment.cpp:271`) dispatches; `lean_add_decl` export `:287`, `lean_add_decl_without_checking` `:297` |
| Kernel entry from Lean | `src/Lean/Environment.lean:296` `@[extern "lean_add_decl"]` | Lean code calls C++ kernel through extern |
| Native-reduction hook | `type_checker.cpp:604-640` (`reduce_native`, `Lean.reduceBool`/`reduceNat`), used `:762,:1101` | kernel calls the **interpreter/compiled code** during defeq |
| Axioms for it | `src/Init/Core.lean:2338` `axiom trustCompiler`, `:2361` `reduceBool`, `:2396` `axiom ofReduceBool` | `native_decide` ends up here; `#print axioms` shows it |
| Reference interpreter | `src/library/ir_interpreter.cpp` (1240 lines): interprets Lean IR from the environment; header comment `:3-25`; `run_boxed` `:1157` | used for `#eval`, `reduceBool`, and platforms without JIT; calls native symbols via dlsym when present |
| `implemented_by` | `src/Lean/Compiler/ImplementedByAttr.lean:14-71` | doc states: implementation "is not checked to be equivalent" |
| `extern` | `src/Lean/Compiler/ExternAttr.lean:28-36` | names a C symbol; body (if any) is only the logical model |
| Independent re-checker | `src/LeanChecker.lean` (built as `leanchecker`, `src/CMakeLists.txt:928`, `stdlib.make.in:106,208`) | replays .olean decls through the kernel; not a second kernel implementation |

## 3. Facts that matter for nano

**What Lean trusts (and nano does not):**
- The **~8k-line C++ kernel** is the *only* thing the logic depends on, and it is deliberately small and separate from the compiler.
- Everything else is untrusted-for-soundness: elaborator, tactics, compiler (LCNF/IR/EmitC), all of `stage0/`. A compiler bug can produce a wrong binary but cannot prove `False`.
- The **compiler is not verified at all**. `stage0/*.c` is trusted by provenance (review + CI fixpoint on binary diff). Fixpoint stage2==stage3 shows only self-consistency; a "trusting trust" backdoor present in stage0 would survive it.
- `@[implemented_by f]` and `@[extern "c_sym"]`: compiled behavior can differ arbitrarily from the kernel-visible definition. The kernel never sees the replacement. Lean's own docs say so. Soundness of *proofs* is unaffected; *meaning of the executable* is.
- `native_decide` / `Lean.reduceBool` / `ofReduceBool` (`Core.lean:2396`) pull the **compiler + interpreter + C runtime + hardware** into the trust base of a proof. They are marked by the `trustCompiler` axiom.
- The C compiler, `lean.h`, `libleanrt`, mimalloc/allocator, libc, OS are all trusted. There is no ISA semantics anywhere.

**What nano trusts (and Lean does not):**
- nano's statement is about the *binary*: "machine code run on the Sail/DeepMind ISA model computes the Lean function". No C compiler, runtime or libc in the base; instead: Lean's kernel, the ISA model fidelity, and the specification statement itself (`Encode`, memory/OS-loading assumption).
- nano's self-hosted compiler output is **proved** equal to its source (`Nano/SelfHost/Cert`: "meaning of C's text is C's Lean function"; `SrcLink`: the text parses to that), instead of "checked-in artifact + convention".
- No `extern`, no `implemented_by`, no `native_decide`/`reduceBool` (ROADMAP standing decisions) => no gap between the logical definition and executed code.

**What both share:** the Lean kernel (nano's proofs are checked by it; Lean's kernel is C++ and unverified, ~8k lines + `Nat`/`String` GMP-style fast paths).

**Structural differences:**
| | Lean | nano |
|---|---|---|
| Frozen bootstrap artifact | `stage0/stdlib/*.c`, 591 MB, regenerated by script | `B2.bin` (machine code) checked in |
| Link artifact<->source | none formal; CI rebuilds + `diff stage2 stage3` | theorem: artifact is the compiled source (kernel-checked) |
| Fixpoint | stage2 == stage3 binary diff (needs full rebuild, hours) | fixpoint is a *consequence* of the proof, plus `selfhost_gate.sh` |
| Source language | full Lean (the compiler uses everything incl. macros, `partial`, `unsafe`) | small bootstrap subset; Lean-compatibility invariant |
| Update step | `update-stage0` copies new C; reviewers trust bot | regenerate certs (generated Lean), kernel rechecks; a bad update fails to build |
| Escape hatches | `stdlib_flags.h` option overrides, `prefer_native`, `proofAsSorry` in stage0 | none allowed (no sorry/axiom) |
| Reference interpreter | `ir_interpreter.cpp` over IR (unverified, 1240 lines C++) | the Lean semantics of the subset itself is the spec; the Sail model plays the "runs it" role |

Caveat: Lean's stage0 also embeds an older compiler *front end* (elaborator). nano has no elaborator: it reads a subset's syntax and a kernel-checked equation per function (ROADMAP "Front end"), so it avoids that whole trusted-by-convention surface.
Not verified by me: the original (pre-self-host) C++ compiler is gone from this tree (`src/library/compiler` absent); the root of the stage0 history is in git history, not checked here (shallow clone).

## 4. Reuse assessment for nano

**(a) Blueprint — worth adopting (cheap, conceptual)**
1. *Staged naming and the "stage0 is a blackbox, never rebuilt from current source" rule.* nano already has this in effect with `B2.bin`; state it in `Nano/SelfHost/README.md`: B2 = stage0, built-by-B2 = stage1, built-by-stage1 = stage2, require stage1 == stage2 byte-for-byte. Check that `selfhost_gate.sh` does stage2 (not only stage1), because Lean's own doc says stage1 alone can hide format/ABI breakage (`bootstrap.md:35-50`): "stage1 compiler can't load what it just produced". Concrete gap to look for: a change to the output encoding that B2 handles but B2-built-C cannot.
2. *Update procedure as one script with a mechanical guard*: Lean's trigger is "`stage0/src/stdlib_flags.h` out of sync" and a CI bot commits the update; PRs that touch `stage0/` need a label and separate commits (`bootstrap.md:99-107`). nano equivalent: B2.bin + regenerated Cert/SrcLink must change in dedicated commits, never mixed with source changes; keep a single `update_b2.sh` (nothing in Lean checks this beyond convention; nano's kernel-check is stronger).
3. *Bootstrap-only option overrides in one file* (`stdlib_flags.h`): if nano ever needs temporary relaxations (e.g. weaker lints for generated code), isolate them like this and have CI fail if left on in a release. nano's no-sorry/no-axiom rule says: currently not needed.

**(b) Oracle — useful for testing**
- Lean's `lean` binary (`stage1`) as differential oracle already matches the Compatibility invariant: run the same subset program through `lean --run`/`#eval` and compare bytes. `ir_interpreter.cpp` is an alternative oracle for "what does compiled Lean do", but it's the same as using real Lean; no extra value except it runs without a C toolchain.
- Lean's EmitC output (`stage0/stdlib/**.c`) of real library functions (e.g. `Nat`, `List`, `String` ops, 2519 files) is a corpus for *what the production compiler does for a Lean function*, usable to compare calling conventions/representations. It is NOT a semantic oracle for nano (nano's representation is its own, ROADMAP "String representation").
- `leanchecker`/`Lean.Environment.replay` style re-checking: oracle for "do nano's generated Cert/SrcLink modules still typecheck from a fresh process", independent of the build's `lake`. Cheap to add as a CI step if not already present.

**(c) Copy — mostly no**
- Do not copy `stage0/`-style generated *source* (C): it re-introduces a C compiler + `lean.h` into the trust base, which nano's design removes. Do not copy the CMake ExternalProject ladder (nano is not CMake/C++).
- Do not adopt `reduceBool`/`native_decide`: it is the exact trust leak (compiler in the loop) that nano's proofs avoid.
- The kernel stays as is: nano reuses Lean's, with the same unverified C++; nothing to copy from `src/kernel` except knowing its size (8k lines) for the "trusted base" paragraph of nano's README (nano's trust = kernel + ISA model + spec, comparable in size to Lean's own kernel + C toolchain + libc + runtime).

**Honest bottom line:** Lean's bootstrap is an engineering process (checked-in artifact + CI fixpoint) with no proof linking artifact to source; nano's is a proof. The transferable parts are process hygiene (stage naming, require stage2 fixpoint, dedicated update commits, one update script, CI label/guard), not technology. Nothing in Lean's bootstrap should be copied as code.
