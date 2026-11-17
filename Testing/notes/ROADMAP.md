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

## Trusted base: the six items (owner, 2026-11-16, FINAL)

Math: (1) Lean's logic and axioms (what the kernel accepts: type theory + propext, Classical.choice, Quot.sound);
(2) the elaborator, as the definition of what written syntax means; (3) our specification (`Spec/`: what "correct" is).
Machine: (4) the Sail models describe the ISA correctly (with their axiom set); (5) the physical CPU implements the ISA.
Bootstrap: (6) the first checker used is correct for our use, made robust by intersecting several independent checkers
(Lean kernel, con-leche, nanoda, …). Everything else (exporter, our compiler, con-leche's binary, optimisation passes) is
proved, not trusted.

Tentative (7): the elaborator is correct (it defines what syntax means, and is a likely source of bugs).

### Front-end input: exported kernel terms, compiler correct by construction (owner, 2026-11-16; S3 design direction)

- Input = UTF-8 export of KERNEL terms (lean4export-style), not Lean source text (source text needs an elaborator, i.e.
  the white whale below). The compiler is one pure Lean function `exported terms → Option code` with ONE general
  correctness theorem (proof checking of internals stays beneath the spec). Unsupported input (IO, `partial`, extern,
  unsupported types) returns `none`: rejection, never a wrong compile.
- Per program only the bridge "this exported term denotes the Lean function `f`" remains, a kernel `rfl`/`decide`
  (a metaprogram may generate it). Fits `Program P` / `Computes` in the current spec with `P` = exported declarations.
- Do it inside IR S3: rewrite the front ends as pure `kernel terms → IR` functions instead of tactic metaprograms. This is
  also what makes the complete compiler self-hostable.

### Long term ("white whale"): a small elaborator for pure functions (owner, 2026-11-16; NOT started)

- Size of the real one (Lean 4.29 sources): `Lean/Elab` ≈ 69k lines, `Lean/Meta` (unifier, whnf, instances, match
  compilation, simp) ≈ 83k, `Lean/Parser` ≈ 7k; ≈ 400 `partial`/`unsafe` definitions and ~30 `@[extern]` in those folders.
  No correctness theorems about Lean 4's elaborator are known to us.
- Idea: a small elaborator, written in pure Lean (no `partial`, no `unsafe`, no extern, no IO), for the subset we use:
  `def`/`structure`/`inductive`, explicit or simple implicit arguments, pattern matching, structural and well-founded
  recursion, a fixed set of instances/notations (`+`, `==`, `do` for concrete monads). Rough size 5–15k lines; the hard
  parts are unification, implicit arguments, match compilation and recursion compilation.
- Validation without trusting either elaborator alone: for every definition, elaborate it with both and let the kernel
  prove `tiny_f = real_f` (by `rfl`/`funext`); fuzz with generated programs and our corpora (book, con-leche, the
  compiler itself). Agreement means both would have to be wrong in the same way. Once it is pure Lean, our compiler
  compiles it with a machine theorem.

### Details of the root checker

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

### Nano: a tiny fully self-hosting toolchain (owner, 2026-11-16)

PRIORITY (owner, 2026-11-16 21:50): full self-hosting of nano comes FIRST. It is the through line (spec = own small
elaborator; back end proved with the big compiler's pieces; self-hosting checked by an exact fixed point) that later
structures the big compiler; its syntax is opened up later by putting the full Lean elaborator in front. Boxes: nano-e2e
(Sonnet: elaborator, byte-level rewrites, self-hosted binary), nano-proof (Opus: generator proofs), nano-v2 (Opus:
self-compiling language, B2 = B3).
UPDATE (owner, 2026-11-16 22:00): focus = a MINIMUM VIABLE nano, PROVED correct end to end and self-hosted, plus signed
Int64 + and − (same machine code as UInt64; only the meaning and the agreement checks change). No language growth beyond
that; v2 (self-compiling, B2 = B3) deferred until the MVP chain is closed. Box nano-mvp (Opus) replaces nano-v2.
SUBSET RULE (owner): nano is an EXACT subset of Lean. If `nanoElab` accepts a text, Lean's elaborator accepts the same
text with the same meaning; nano may reject anything. Checked by per-program agreement proofs, random fuzz, and an
adversarial boundary fuzz (accept/reject compared on both sides: precedence of application vs binary minus such as
`f -1`, numeral wrap, unary minus, shadowing of Lean globals, keywords as names, comments, whitespace). Any "nano
accepts, Lean rejects" or "meanings differ" is a bug, fixed by rejecting.
SPEC OWNERSHIP (owner): `nanoElab`, `Prog.eval` and the documented grammar are a DRAFT spec; the owner writes/confirms
the final version later. Boxes keep them minimal, record evidence (agreement proofs, fuzz results, edge cases) for that
review, and spend their effort on the proved back end and self-hosting, not on polishing the spec.

- v1 (Sonnet box, branch nano-e2e): `nanoCompile = nanoGen ∘ nanoElab` (UTF-8 text → AST → RISC-V) written in Lean,
  compiled by our compiler (binary proved to compute `nanoCompile`); elaborator checked against Lean's real elaborator
  (per-program `rfl`/`decide` + fuzz); generated code tested on QEMU/Sail (proof = stretch).
- v2 (queued, fresh Sonnet box after v1): grow nano just enough to write its OWN compiler (if/comparisons, recursion or
  loops, byte input/output); write the nano compiler in nano (S); B1 = our compiler's binary of the Lean version
  (proved); B1 compiles S → B2, B2 compiles S → B3, require B2 = B3 (fixed point); S agrees with the Lean `nanoCompile`.
  Nano owns its whole pipeline (its elaborator is its own spec, cross-checked against Lean's), so no Lean elaborator in
  the loop. Full proof additionally needs `nanoGen` correctness (generated code = `Prog.eval`).
- (owner) `nanoElab` + `Prog.eval` ARE the spec of nano: never proved, only expanded (cross-checked against Lean's
  elaborator). Everything after elaboration is proved: `CompileCorrect riscv nanoCompile`, reusing any big-compiler piece.

### After nano self-hosting closes: grow the self-hosted compiler (owner, 2026-11-17)

- Main line = grow the SELF-HOSTED nano compiler feature by feature (self-hosting stays an invariant: every added feature
  is proved end to end and compiled by itself), rather than finishing the big compiler first.
- Converge on one middle: nano's elaborator emits the S3 typed calculus (Compiler/S3, proved once through the IR to
  RISC-V); nano's stack back end is replaced by that shared, proved S3/IR back end. Big-compiler features arrive through
  the calculus instead of being re-implemented. Self-hosting = compiling that pipeline with itself.
- Front ends compose as functions into the same calculus; pick per program:
  `backend ∘ nanoElab` (small, self-hosted, our spec) or `backend ∘ fromKernelTerms ∘ leanElab` (full Lean, trusted
  elaborator + exporter). As nanoElab grows, fewer programs need the Lean front end; later the small pure elaborator
  (checked against Lean's by kernel equality per definition) replaces it.
- Speed work on the front ends is safe by construction: they are certifying (each output carries a kernel-checked
  theorem), so a wrong speed-up fails the check instead of producing wrong code.
- Increments (owner): grow in SMALL steps, each one checked before the next: one feature or one back-end piece at a
  time (e.g. first move only nano's expression lowering onto S3 while the stack back end stays; then one datatype; then
  calls), and after every step the self-hosting theorem, check.sh and the full-chain test must pass again.
- ORDER (owner, 2026-11-17 04:45): (1) close nano self-hosting by whichever route lands first (frontx per-stage
  certificates or S3); (2) BEFORE expanding nano, make the self-hosted binary B "correct by design": every stage
  compiled through the S3 calculus (compiler proved once), leaving only a Lean-level equation per stage
  (`eval P = stage`), no generated machine-level step proofs; (3) then grow nano in small checked increments on S3.
- INTERPOLATE (owner): move nano onto S3 through a chain of intermediate calculi, each differing from the previous by ONE
  construct (e.g. nano Prog → explicit lets → normal-form expressions → S3 words only → S3 with calls → S3 datatypes),
  each link a small proved translation (simulation / meaning-preservation) checked before the next; the self-hosting
  theorem, check.sh and the full-chain test pass after every link.
- What "correct by design" means here: (a) back end proved once (`nano_stack_correct`, later S3's theorem); (b) each
  byte-level stage of B proved equal to its spec function (`lexB_eq`, `stage2_lexB`, …); (c) B's machine code computes
  those stages (today certifying per stage; after the S3 move, by design). `nanoElab` itself is the spec (defines
  meaning), cross-checked against Lean's elaborator, not proved.

### Spec strengthening: output length and exact output block (owner-approved, 2026-11-17)

1. APPROVED: the code returns the output length in a register (e.g. a1); the spec states the output occupies exactly
   `[outputAddress, outputAddress + a1)` and decodes to the result, so readers never depend on the type's encoding.
2. DEFERRED (owner): zeroing the rest of the output block; outputs are self-delimiting meanwhile. Only on request.
3. Domain of the self-hosted nano binary: either stated explicitly in `Nano.selfHosted` or out-of-domain inputs set
   the OOM flag; must be explicit either way.
Plan (small checked steps, AFTER nano self-hosting closes; length register only): tiniest first step = nano
(output always 8 bytes: `li a1, 8` + one proof step), then the IR back end (a1 = end − start; S3 and the inductive
path inherit it), then the rest. add `CompileCorrectL` / `CompileRunsL` next to the current
statements in Compiler/AllocSpec.lean (nothing breaks); prove them back end by back end (IR first, then inductive path,
paged, S3, nano); when all hold, make them the main statements and retire the old ones. Each back end's exit code sets
the length register (and, for item 2, zeroes the rest).
- SPEC REVIEW ITEM (found 2026-11-17 by the nano-e2e box, NANO.md "RESOURCE LIMITS"): Lean's real elaborator REJECTS
  very deep inputs (≥ 512 nested `let`s, ≥ 256 nested calls, operator chains of ≥ ~3000 operands: "maximum recursion
  depth"), while `nanoElab` ACCEPTS them. This breaks the exact-subset rule only at these resource limits. Fix = make
  `nanoElab` reject above fixed bounds (e.g. nesting ≤ 400, chain ≤ 2500); it changes the spec, so the proofs written
  against `nanoElabT` (ElabU, ElabB*, ParseB*) must follow. Owner decides; until then state the bound in the domain of
  `Nano.selfHosted`. Exhaustive check otherwise clean: all bodies of 1–6 tokens over a 15-token alphabet (~13M
  texts): 0 differences against Lean.
  DECISION (owner, 2026-11-17 06:40): REMINDER, do after self-hosting closes — add the depth/length limit to the spec
  (preferably as an explicit parameter of `nanoElab`, e.g. `nanoElab (lim : Limits) src`), then update the proofs. Until
  then `Nano.selfHosted` carries the bound in its stated domain.
- DECISION (owner, 2026-11-17 07:36): S3 is the route for ALL new compile work (correct by construction: no per-stage
  machine proof; per stage only a Lean bridge + kernel evaluation of the compiler). Stages already compiled by frontx
  (asm, lexer halves, mexp) stay until ORDER step (2) moves them to S3; no new frontx/paged effort.
- ONE GO (owner, 2026-11-17 07:40): the final form compiles the WHOLE nano compiler through S3 in a single build from a
  single source revision (one script / one lake target producing B and `Nano.selfHosted` together), so binary and
  theorem always match and no stage comes from an older compile. All earlier per-stage compiles (frontx asm, lexer
  halves, mexp, and whatever closes the milestone first) are REDONE in that one build. Then B is run on its own source
  (fixed point check, nano v2). The mixed-route milestone is only a stepping stone.

### FREEZE BEFORE THE FULL RUN (owner, 2026-11-17 09:07)
Before the one-go full run (compile the whole nano compiler from one revision, then run it on itself), ALL the Lean code
must be present and final on ONE branch:
- every stage's source (lexer, parser 2a/2b, inliner, expander, assembler), its bridge theorem (`= original` for every
  input) and its stage theorem (`Implements1With`, Sail axioms only), plus the composition `Nano.selfHosted`;
- a manifest `Testing/notes/NANO_MANIFEST.md`: per stage, the file, the bridge, the stage theorem, build wall time (≤ 5 min),
  `#print axioms` line;
- `check.sh` passes, with no sorry and no new axioms.
Then tag that revision. The full run (one build, the QEMU/Sail tests, the self-run, the fixed point later) uses only the
tag. No code changes during the run; a fix means a new tag and a new full run.
ONE GATE (owner, 09:08): there is exactly one point, the tag, where everything is proved end to end: `Nano.selfHosted`
is kernel-checked at the tag, every manifest row is done and check.sh passes. Only after that gate does B run on its own
source. Per-part checks before the gate (stage tests on QEMU/Sail) are allowed and encouraged; they never replace the gate.

### GATE REACHED (2026-11-17 12:17): nano v1 rc1 = origin/nano-parse-s3 commit 6a76836
`theorem Nano.selfHosted (K : Nat) : SelfHosted binary (fun _ => space5 K) (Domain K) nanoCompileA` (Nano/SelfHostFinal.lean),
no hypotheses; `binary` = 5 linked stages (lexA, stage2b, inliner: S3; nanoExpM; nanoAsm);
`Domain K src := SizedL K … src ∧ LeanLimits src`. Axioms: Sail set + propext, Classical.choice, Quot.sound (expected-axioms.txt:930).
check.sh ALL CHECKS PASSED (1026 s). Heavy modules: ParseS3BStage ≈ 8 GB, ParseS3BAllocB ≈ 7.6 GB, so build with limited parallelism.
Tag `nano-v1-rc1` → 6a76836 still to be pushed by the owner (the session git proxy refuses tag pushes).
Next: the self-run from 6a76836 (no code changes), then merge the nano branches to main.
nano v1 rc2 (2026-11-17 15:14) = origin/nano-parse-s3 commit 152f05b: same `binary` words as rc1 (evaluated hashes), every module
≤ 155 s cold and ≤ 6.3 GB, check.sh ALL CHECKS PASSED (1177 s). Self-run at rc1 (branch nano-selfrun ca437bf): binary = binaryC proved,
55529 words, linked QEMU 146/146, Sail 8/8; build 1390 s / 11.0 GB. Tags nano-v1-rc1 (6a76836) and nano-v1-rc2 (152f05b): owner to push.

### NANO V1 MERGED (2026-11-17): branch merge-nano → main, stable
merge-nano = origin/main + nano-parse-s3 (c9514b2, rc2 152f05b) + nano-e2e + nano-closeB + nano-selfrun. Conflicts:
check.sh loop / expected-axioms = main's lines then the branches' (nano-closeB appended); NANO_MANIFEST.md keeps both
(selfrun's 11:33 gate status marked superseded). No Nano/ or S3 Lean source changed by the merge except: closeB's
`Nano/InlP3Self.lean` ("compile in progress") overflows the stack in the build, so it is archived in
Testing/nano/archive/ (InlP3 / InlP3Proof stay). check.sh: ALL CHECKS PASSED (cold over the f1cfb76 cache 1115 s up to
the failure, then 1271 s; peak 6.2 GB, 4 jobs); only the pre-existing statement-fingerprint WARNING, not re-frozen.
`Nano.selfHosted`: 77 axioms = expected-axioms.txt:930 (Sail set + propext, Classical.choice, Quot.sound).
IR-STRONG RECONCILED (2026-11-17): branch merge-ir-strong = main + ir-strong (+ s3-rec's later examples). One IR stub:
nano's `[leaveC; leave; mov a1 r0; ret]`; the OOM exit keeps the shared `encK .exit` (gp not restored), so nano's
`binary` words are unchanged (same 55529-word hash) and `CompileRunsL` proofs for the IR are dropped (GAP, next tag).
`CompileCorrectL` / `CompileCorrectRV` / `implements_of_compileL` / `S3.implements` and `S3.implements1` all proved.
check.sh ALL CHECKS PASSED (2385 s). Details: Testing/notes/IR_STRONG.md "Reconciliation with nano v1".

### RELEASE MARKERS (owner, 2026-11-17 17:10): no tags
Releases are marked by a commit on main whose message says it is the final addition (e.g. "nano v1 FINAL: …"), not by
git tags. nano v1 FINAL = this commit: main contains nano-parse-s3 rc2 (152f05b, same binary as rc1 6a76836),
`Nano.selfHosted` proved (Sail axioms + propext/Classical.choice/Quot.sound), check.sh passed (merge-nano), self-run QEMU
146/146 and Sail 8/8 on the proved binary. The nano-v1-rc1/rc2 tags are not needed.

### DIRECTION (owner, 2026-11-17 17:40): compiler #2 (nano) compiles ITSELF; compiler #1 is the store
- GOAL: nano v2 = the nano compiler written in nano, compiled by its own proven binary: B1 (built by compiler #1 / S3)
  → B2 = B1(own source) → B3 = B2(own source), B2 = B3 byte for byte, with the proof `Nano.selfHosted`-style for each.
- HOW: grow the nano subset by interpolation (one construct per proved link; nano stays an EXACT subset of Lean), until
  the nano compiler can be written in nano. Candidate order: comparisons + `if`; bounded recursion / loops; byte input
  read + output write; UInt8 / match on small numbers; small data (tuples/structures, maybe lists).
- Compiler #1 (Lean → RISC-V: frontx, S3, IR; con-leche track) is now a general STORE of proven function translations.
  Once compiler #2 self-hosts, its features move onto compiler #2 incrementally ("start small and grow the
  self-hosting one" rather than self-hosting #1 with all features at once).
- Terminology: v1 `Nano.selfHosted` = proven bare-metal nano compiler built by compiler #1; "compiles itself" = v2.

### NANO_V2_SPEC (owner, 2026-11-17 19:25): work may proceed on it without a separate confirmation (the content is Astra-advised, not owner-chosen)
The frozen spec on branch nano-v2 (v1 constructs unchanged + exactly the Astra-decided additions; v1 stage formats;
Int64 dropped for milestone 1) is accepted as the working freeze. Like v1's `nanoElab`/`Prog.eval`, the meaning stays a
draft the owner may review later; changes after the freeze still go through the owner.
