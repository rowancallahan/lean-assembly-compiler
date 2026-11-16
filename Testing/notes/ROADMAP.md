# Target functions

Goal of each row: `ImplementsMapped code f` for the named Lean function `f`, RISC-V first, then ARM.
"Needs" = what the compiler lacks today (see `Testing/notes/ARRAYS.md` for the current language).

## Fits the current language (or nearly)
| Target | Lean reference | Needs |
|---|---|---|
| sort (done, insertion) | `List.mergeSort` | — |
| take / map / sum (done) | `List.take`, `List.map`, `List.foldl` | — |
| reverse, filter, count, min/max | `List.reverse`, `List.filter`, `List.count`, `List.min?` | output encoding for `Option` |
| binary search | `Array.binSearch` | encoding of the result |
| UTF-8 validation | `ByteArray.validateUTF8` | larger loop bodies |
| merge sort (in progress) | `List.mergeSort` | spill slots |

## Word arrays and scale
| Target | Lean reference | Needs |
|---|---|---|
| CRC-32 | own definition (~10 lines) | 32-bit masking, table |
| SHA-256 (long-term showcase) | own definition, published vectors | word arrays, rotates, constant table, padding |

## On the path to a proof checker (con-leche)
| Target | Lean reference | Needs |
|---|---|---|
| recursive function: evaluate an expression tree given as bytes (prefix encoding) | structural recursion on an inductive `Tree` | function calls, a stack, recursion depth bound from the input |
| linked list: build from input bytes, then reverse / append / length by pointer chasing | `List.reverse`, `List.append` on the decoded list | bump allocator over the block model, pointer cells, representation invariant (list ↔ cells) |
| hash map: insert n key/value pairs, then look up | `Std.HashMap` (or association-list `List.lookup` as the reference) | word arrays, hashing, open addressing, table invariant |
| tagged data + dispatch: tiny bytecode interpreter | own definition | tags, jump on tag, stack in memory |
| big-number add / multiply | `Nat.add`, `Nat.mul` on limb lists | carries, multiply (shift-add or M extension) |
| parse bytes into a tree, check, print | own definition | all of the above |

## Showcase only (not on the path)
knapsack, edit distance, Floyd–Warshall, Dijkstra, max-flow.

## Order
merge sort → word arrays (CRC-32) → calls + stack (tree evaluator) → allocator (linked list) →
hash map → tagged dispatch (interpreter) → big numbers → SHA-256 → read con-leche / con-ron and fill gaps.

# Standing decisions (from the owner)

- Scope: a SUB-compiler for pure functions, bytes in → bytes out (`Spec/Encode.lean`). No IO, no OS interaction.
  The OS (or a boot stub) only loads blocks and reads the result; "a correctly functioning OS hosts the process" is a stated assumption.
- The compiler is one pure Lean function. Any number of internal passes/optimisations is fine if proved:
  no `sorry`, no `axiom`, no `extern`, no `native_decide`/`bv_decide`.
- Front end: translate Lean definitions ourselves with a kernel-checked equation per function; do not use Lean's compiler IR.
- Structure: front (Lean → program) / middle (program → abstract ops + all Hoare logic, machine-independent) / back (per target, thin).
  Design on RISC-V; ARM follows in the background.
- Two backends with separate proofs, each equal to the Lean function; no combined ARM = RISC-V theorem needed.
- Arithmetic: integers and modular arithmetic only. NO floats, nothing over the rationals/reals.
  Candidate clients: Mathlib-defined number theory computed modularly (after big numbers); SHA-256; CRC-32.
- Speed matters: generated code should aim to match or beat Lean's native compiler.
- Tier 1 = the explicit compiler: one pure function with several proved optimisation passes inside, invisible in the spec.
  Tier 2 = hand/agent-optimised code for a specific function, proved against the same spec; interchangeable with tier 1.
- Resources in the spec: ONE bound, `space n` = extra bytes of memory the code may use for an input of n bytes
  (a single work block; the compiler carves it into scratch/frame/spill slots as it likes). No separate "stack"/"scratch"
  in the user-facing statement. Registers: a fixed convention (which are preserved), not a counted resource.
- Unbounded `Nat` and termination (owner): three accepted ways, chosen per function, all visible in the statement:
  (1) bounds as explicit ARGUMENTS/hypotheses of the function or theorem (e.g. `(h : n < 2^64)`, a bound parameter);
  (2) bounded types in the signature (`BitVec 64`, `UInt8`, `Fin n`), so no side condition is needed;
  (3) FUEL: the function takes a step budget and returns `none`/a default when it runs out — termination is then
  trivial and the machine code has a proved step bound. Out-of-range results use `Option`/`Except` through `Encode`.
- Every compiled function goes through `Spec/Encode.lean`: the input block holds `enc a`, the output block ends holding
  `enc (f a)`; functions over `Nat`/`List α`/structures are compiled via their byte encodings (that is the normal case,
  not a "restatement").
- Floats and IO: not now. When floats are added, the float library is taken as an AXIOM set: the trusted base is then
  exactly two things, the machine (assembly) semantics and the float library. (The Sail RISC-V model already exposes
  its floating point as 67 uninterpreted `riscv_f*` constants — the natural place to connect.)
- Memory: blocks are lists of cells; layouts of pairwise-disjoint blocks; owner reviews byte layouts in `Encode.lean`.

# Far future (noted, not planned)

- Self-hosting: compile the compiler's core (program bytes → machine code bytes) with itself.
- Multi-core: each core gets its own writable block, shared blocks are read-only, one coordinating core
  only reads the others' "done" state; results are interleaving-independent by the separation theorem.
- con-leche / con-ron compiled to proved ARM and RISC-V code.
- lean-svg's `render : Options → ByteArray → Except String ByteArray` as a large pure client.
- A tiny real-time operating system on RISC-V proved on the same model.

- Signal: (a) a new implementation of the Signal protocol written in Lean, specified by PROPERTIES only (security
  statements; the implementation is free to change), compiled by this compiler; (b) compile DeepMind's existing
  byte-level Lean model of libsignal (AlphaProof Code, github.com/google-deepmind/code-verification, Apache-2.0)
  with this compiler, so their security proofs apply to our binary. Needs constant-time code generation for secrets
  (our theorems say nothing about timing). Ideas to adopt from that paper now: frozen held-out spec + `comparator`
  gate, non-vacuity proofs for configuration predicates, mutation tests of the spec, single integrator commits.
- DeepMind's small hand-written AArch64 user-mode Linux semantics as an additional ARM target (Sail stays the reference);
  experiment pending (their package: Lean 4.34.0, no dependencies, Apache-2.0).
  Owner's plan for Signal (decided): write a FRESH short property spec S (human-readable, target < 1k lines without
  wire formats); write our Lean implementation F; prove (1) F satisfies S and (2) F = M (DeepMind's model) on all inputs.
  Validate S by mutation: mutants of F that break F = M should mostly break S too; a security-relevant mutant that
  breaks F = M but still satisfies S marks a gap in S.

# Strategy (owner, 2026-11-15)

- Features before speed: up to ~10x gcc -O2 is acceptable for now; optimisation passes come later, possibly
  larger ones that work across the stack, once big functions compile and show where time goes.
- Depth first: take the biggest pure functions (con-leche checker entry points, lean-zip inflate, lean-svg render,
  the self-hoster), compile until the first failure, and fix the feature that unblocks the most. Breadth (the book,
  surveys) runs in parallel on Sonnet boxes to set the stage.
- Grow the self-hoster alongside the compiler: each new feature is also used in the tiny self-hosting compiler.
- Pure functions only: state monads inside pure code are in scope; IO is not.
- Long-term goals: con-leche and self-hosting. The book, lean-zip and lean-svg are the way there. ARM is a slow
  side track (bridge to Sail ARM).
- String representation: the owner will review the byte layout (as for Encode.lean).
- Memory at run time (owner, final for now): `compile_correct` keeps its shape; its memory hypothesis becomes
  `enoughMemory : memoryNeeded compiled input <= call.workLength`, where `memoryNeeded` is the maximum work memory
  the run uses, DEFINED from the run (not calculated, not an explicit formula). It replaces `compiled.space n` /
  `cellsSup` in the statement (those become ways to prove the hypothesis). Being a Nat it is always satisfiable
  for a large enough block, so the theorem is not vacuous. One work block per top-level call; callees allocate
  inside it.
  Out of memory (draft definition, owner asked for a stab): `memoryNeeded compiled input` = most work memory the
  run uses with unlimited space (defined, not calculated); `OutOfMemory compiled input W := W < memoryNeeded
  compiled input` (a property of the run, not of a register). Behaviour for any W: halts, nothing outside output +
  work changes; `memoryNeeded <= W` -> right output (`compile_correct`); `OutOfMemory` -> halts with `a1 = 2^64-1`
  (the reported flag; output contents unspecified). The two cases are complementary, so the flag appears exactly
  when the run does not fit, never earlier.
- con-leche hashing (owner): `mixHash` is `@[extern "lean_uint64_mix_hash"] opaque` in Lean core (Init/Prelude.lean),
  i.e. no Lean definition at all; `String.hash` is an extern too. Plan: port the C code exactly into Lean
  (`mixHashLean`, 6 lines of UInt64 mul/xor/shift; `String.hash` = MurmurHash64A from the runtime), substitute it in
  a copy of con-leche, re-check con-leche's proofs (they cannot depend on an opaque value), compile that, and fuzz
  the port heavily against native `mixHash` (`#eval` runs the C) on random inputs and on real con-leche terms.
  Our theorems then say "computes con-leche with mixHash := mixHashLean". If con-leche's output provably does not
  depend on the hash function (only consistency), any Lean hash will do.
- String byte layout (owner, 2026-11-15): a length followed by the raw UTF-8 bytes (replaces the §23 chain of tagged
  byte cells). Both keep every symbol; this one is compact and standard. Length width to fix in the round (8-byte
  little-endian like other scalars unless the owner says otherwise). To be done after the Expr round (same files).
- Pipelining (owner, 2026-11-15): start the next round on top of the previous round's unverified branch instead of
  waiting for its checks; rebase if it fails (some redone work is accepted). Farm independent QEMU/Sail test runs out
  to cloud boxes; keep one final combined `check.sh` before pushing to main/stable. Lean already reuses unchanged
  modules' builds. Build cache (owner): branch `build-cache` holds prebuilt build output (zstd tarballs, README
  there); cloud boxes restore it instead of building. First item: the Sail RISC-V model dependency (25 MB).
  Next: this repo's own `.lake/build` at main after big merges (~750 MB raw). Split slow proof files into
  independent lemma files so lake builds them in parallel (plan: branch build-profile, BUILD_PROFILE.md).
- Time budget (owner, 2026-11-16): at least 70-80% (goal 90%) of wall time should be agent thinking/proof writing;
  builds, tests and CI at most 20-30% amortised over a week (the final full check and full re-elaboration excepted).
  Rules for every agent: iterate on ONE file with `lake env lean <File>.lean` (only what changed), never a full
  `lake build`/`check.sh` per attempt; run the full check once at the end of the round; send QEMU/Sail test runs
  to other boxes when possible; use the build cache. Measured daily from the session logs (tool wall time vs
  model time per round).
- Variable-size blocks (owner, 2026-11-16): arrays/strings of different sizes must not make out of memory inexact
  (fragmentation: enough free memory in total but no contiguous piece). Fix, BENEATH the spec: a software
  virtual-memory layer, fixed-size pages + a page table per block, so any free page serves any block; `memoryNeeded`
  is counted in pages (rounding and page tables included), so "fits" stays exact. Cost ~one extra load per array
  access. Not the hardware MMU.
- Later (owner): callee-saved registers (needed to call our code from C or other code from ours).
- Enough memory never fails (owner, 2026-11-16): already stated: CompileCorrect (memoryNeeded <= workLength ->
  right output, no flag) and CompileRuns (flag <-> workLength < memoryNeeded, so any larger block cannot fail);
  software paging keeps memoryNeeded exact for variable-size blocks. TO ADD (non-vacuity of the new statements,
  like `startCorrect_nonvacuous` for the old ones): for each compiled program and input with memoryNeeded fitting in
  RAM next to the other blocks, `compile = some _` and a start state satisfying StartCorrect exists (built by the
  bare-metal boot proof, Riscv/Back/Boot*.lean) with workLength = memoryNeeded. Owner: only BARE METAL matters
  here (the boot proof already provides the start state); hosted setups may not satisfy it, which is fine.
  Later (owner): a non-vacuity statement for non-bare-metal (hosted) setups too.
  ROUTINE (owner): once the bare-metal corollary exists, every round's new machine theorems come with their
  non-vacuity corollary (generated by the front-end command, like `f.implements1`), checked by check.sh.
- Merge hygiene: a round's new axiom file is named after its branch (Testing/scripts/axioms_<branch>.lean, added to
  check.sh's list), never the next free letter, so parallel rounds do not collide.
- Shared IR (Compiler/Ir, Riscv/Back/Ir*): beneath the spec; its theorems are the AllocSpec statements for
  Ir.compile. Later (owner, not now): optionally expose the top theorem as a composition "IR meaning" ∘ "IR → assembly"
  through an adapter.
- C via Certora/clean (owner idea, 2026-11-16): github.com/Certora/clean = CompCert 3.17 fork exporting a C program's
  Clight syntax to Lean 4.32.1 + a Lean port of Clight semantics (interpreter proved sound, determinism, separation
  logic). C→Clight front end is trusted OCaml; NO compiler and no link to CompCert's correctness proof in Lean
  (Clight→asm stays in Coq); non-commercial licence; experimental. Plan, by value: (1) cheap: print our IR as C and
  use gcc/CompCert/Clean's interpreter as a differential test oracle; (2) Clight as a SOURCE language: Clight → our
  shared IR, proved in Lean against Clean's semantics, then our verified chain to RISC-V/ARM (no Coq trust); (3)
  optional Lean→Clight back end proved against Clean's semantics for interop. Round-trip/translation validation is
  sound given one theorem (meaning of emitted C = the Lean function). Not a rewrite: C becomes one more input of the IR.
- Trust and licence (owner, 2026-11-16): trust ONLY the Sail models (no cross-prover trust in CompCert). CompCert
  and Certora/clean are inspiration (designs, proof strategies); acknowledged in NOTICE.md. Licence (owner, 2026-11-16):
  Apache-2.0 (LICENSE; open, warranty/liability disclaimer, patent grant), replacing the earlier non-commercial intent. If CompCert code or proofs are ever copied, that file falls
  under CompCert's licence and must say so.
- Less stuck time (owner, 2026-11-16). Causes seen today: boxes stalled on setup (denied installs of zstd/QEMU/gcc,
  old main, missing sources) and boxes that stopped to ask and waited idle. Fixes: (1) the cloud environment now has
  a setup script installing zstd, qemu-system-misc, gcc-riscv64-linux-gnu; (2) every box prompt: start from the
  latest origin/main, restore build-cache (gzip or zstd), use repo copies of sources (con-leche: origin/conleche-depth
  F2.lean.txt), NEVER stop to ask: make the reasonable choice, write it in the notes, continue; stop only when done
  or after a stated time cap, pushing every step; (3) Haiku only gets self-contained recipes; (4) the parent batches
  merges (one combined check for several small branches) and reacts to box messages immediately.
- Side project (owner, 2026-11-16): Lean → C "auto compiler" via Clean + CompCert (cross-prover trust accepted for
  this side project only; the main project still trusts only Sail). Clean's C→Lean is OCaml clightgen exporting
  Clight SYNTAX as Lean data, not a Lean function, so an "inverse" proof is not the right spec. The one spec needed:
  `leanToClight_correct : ∀ x, clightRun (leanToClight f) (encode x) = some (encode (f x))` against Clean's Lean
  Clight semantics, the same shape as our compile_correct with Clight in place of Sail. Route: shared IR →
  Clight + simulation proof; then CompCert compiles the C. Needs Lean 4.32.1 (Clean) vs our 4.29: separate repo or
  later upgrade; Clean's non-commercial licence applies to the side project only.
- PRIORITY (owner, 2026-11-16): self-hosting + con-leche first; pick whatever is fastest to a STABLE, ORGANISED
  version of those two. lean-zip / lean-svg / book only where they share features (arrays, structures). Every Opus
  round takes its targets from the latest depth probes (CONLECHE_DEPTH2.md, SELFHOST_DEPTH2.md when they land),
  biggest blocker first. Organisation: one route (the shared IR) for every front end, notes indexed in
  Testing/notes/INDEX.md, small pieces merged as they finish.
  lean-zip and lean-svg (and the book) are deliberately easier intermediate targets: when a con-leche / self-hosting
  round is stuck, switch to them to build the missing feature on a simpler case, then return.
- Order and self-hosting track (owner, 2026-11-16): (1) con-leche (the consistent Lean checker) first; (2) then
  self-host a COMPLETE compiler: milestone = the compiled compiler compiles itself AND compiles con-leche (no toy);
  (3) lean-zip, then lean-svg, as easier side targets; the book, lean-zip and lean-svg are the measuring sticks.
  Friendly-style track for self-hosting: a rewrite of the compiler's own core in compiler-friendly style, grown from
  the current code, ONLY where the front end cannot yet take the real style; every rewritten function carries a Lean
  equation proving it equal to the original (so the self-hosted binary implements the real compiler, not a toy);
  the friendly part shrinks as the front end learns the complex style (the long-term goal).

## Next Opus rounds (owner, 2026-11-16)

1. Compile-time constants: a 0-ary definition whose value the kernel computes within a fixed heartbeat budget and output-size cap
   (literal data such as `Name`/`String`/`Nat` constants) is emitted as data, proved by `decide +kernel`/`rfl`. Anything over budget
   compiles as an ordinary 0-argument function (honest run-time cost). Never fold calls with arguments.
2. IR stage S3: move every front end (list, ind, wa, hof, monad, paged) onto the shared IR so features compose in one function
   (e.g. inductives + monad + structure). Without this, features land separately and the con-leche percentages barely move.
Measured yield (BLOCKER_YIELD.md, merged): con-leche greedy starts with 0-ary constants (+106 functions); the self-hoster with
   translator-shape bugs (+83: `PANIC at Expr.appArg!`, `instantiateForall, too many parameters`, kernel `Sim argument has type Type 1`)
   and polymorphic type variables (+105: the compiler's IR types are generic in the register type ρ; monomorphise at the use site).
   So round 1 = constants + monomorphisation of type variables + those translator crashes; round 2 = IR S3.
Ranking of later features from the Haiku yield analysis (`Testing/notes/BLOCKER_YIELD.md`, branch blocker-yield).

## Trust statement (owner, 2026-11-16, FINAL)

Trusted: (1) the pinned Sail models with their axiom set (`Testing/scripts/expected-axioms.txt`) and the standard Lean
axioms (propext, Classical.choice, Quot.sound); (2) the hardware behaves as the Sail model; (3) ONE root proof checker =
the intersection of con-leche, the Lean kernel, nanoda and other independent checkers (paranoid lake check: a proof is
trusted only if all of them accept it). Caveats kept in view: the checkers share the export format and the type theory
(the exporter is the one shared piece of code); the paranoid check must run on the exact shipped theorems and their
dependency closure; theorem STATEMENTS (`Spec/`) are reviewed by the owner, not by the checkers.

### Earlier proposal (superseded by the above)

- Proposed wording: trusted = the pinned Sail models + ONE root proof checker and its logic (today the Lean kernel; later
  con-leche's own binary only after a root checker has checked its proof once; independent checkers such as other Lean
  kernels can be added as diverse roots) + "the hardware behaves as the Sail model". Self-checking is evidence, not a root.
- A COMPLETE self-hosted compiler needs the front ends (today Lean metaprograms with tactics) rewritten as a pure function
  from exported kernel terms to code + a certificate checked by the compiled con-leche. Not counted in SELFHOST_DEPTH*;
  needs its own design round before the self-hosting milestone can be met.

### Elaborator and exporter (owner, 2026-11-16)

- The elaborator is trusted by definition: it is the specification of what a written statement means (checked later by
  reviewing `Spec/` statements printed with `pp.all`). The Lean kernel is assumed correct for now.
- The exporter (lean4export) is the remaining unverified link for the checkers that read the export. Later item: a
  round-trip theorem `parse (export decls) = decls` with con-leche's own parser (both pure Lean functions), then compile
  exporter + parser with our compiler. Chain: elaborator (spec) → exporter (proved) → compiled con-leche (proved) → accept.
