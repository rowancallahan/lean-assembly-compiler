# Target functions

Goal of each row: `ImplementsMapped code f` for the named Lean function `f`, RISC-V first, then ARM.
"Needs" = what the compiler lacks today (see `Testing/notes/ARRAYS.md` for the current language).

## Invariants (owner, 2026-11-21) — every change must keep both
1. Strict Lean compatibility: nano's language is a subset of Lean's. Every program nano accepts, Lean accepts with the
   same results (fuzz: nano-accepts ⇒ Lean-accepts and agrees; any violation is a FAIL).
2. Strict self-hosting: the compiler (all stages, every target incl. native ARM) is written in nano's bootstrap
   subset and compiles itself; Testing/scripts/selfhost_gate.sh must pass on every merge.
   Self-hosting is the PRIMARY goal (owner, 2026-11-21): the aim is a Lean proof about the compiler itself. New
   features (con-leche's inductives, casesOn, recursion, classes, big Nat, Expr input) are implemented in
   bootstrap-subset nano. The bootstrap subset grows only slowly and in proven steps: each step regenerates the
   self-hosted binaries, re-proves the fixpoints and passes the gate.
3. No @[implemented_by] / @[extern] (or other attributes/keywords that let run-time code differ from the logical
   definition: export, csimp, unsafe, opaque): attributes are a whitelist of meaning-preserving ones only. (Owner: implemented_by may be supported LATER —
   then nano compiles the implementation, as Lean's runtime does; banned for now.)

## LONG-TERM GOAL (owner, 2026-11-21): close the loop with con-leche
Compile con-leche (the CONsistent LEan CHEcker, proven: accepts ⇒ the declarations have a ZFC+inaccessibles model)
with self-hosted nano to proved ARM and RISC-V code. Then: con-leche's consistency proof + nano's compiler theorem ⇒
the BINARY only accepts consistent developments, with no trust in Lean's compiler or runtime. Next, use that binary to
re-check nano's own proofs and con-leche's proofs, so Lean's C++ kernel is no longer the only checker. Remaining trust:
the ISA models (Sail / DeepMind) + hardware, ZFC + inaccessibles, the mixHashLean port (see con-leche hashing below),
and the first kernel check of the bootstrap. Steps:
- after the release, re-check the release theorems with con-leche;
- an Expr spot check: nano emits Expr, compared with Lean's elaborated Expr; then an evaluator proof tied to
  con-leche's model;
- syntax growth driven by con-leche's blocker list (CONLECHE_DEPTH2 / BLOCKER_YIELD), now via the self-hosted front
  end (the earlier Legacy/Frontx con-leche route is shelved with the Lean-hosted mode).

## STRUCTURE DECISION (owner, 2026-11-23): back end carries meaning, front end is checked
- BACK END (Expr → machine code) carries ALL the meaning. The main theorem: for every Expr e in the slice, the
  machine code writes the bytes of con-leche's Denotes(e). Sem and Ev are internal lemmas, not part of the statement.
- FRONT END (text → Expr) claims no meaning. Its output is checked per program against Lean's elaborated Expr
  (kernel-checked for the compiler itself). Nano's parser keeps its own semantics as a helpful side definition and
  is still proved against Lean's parser as far as possible (leaves, LEAN-EQUIV, harvest), but the main theorem does
  not depend on it.
- SELF-HOSTING: the compiler's text → its Expr (= Lean's, kernel-checked) → its machine code computes Denotes of
  that Expr. So when the Expr matches, the compiler provably compiles itself correctly (binary identity: fixpoint,
  later kernel evaluation).
Work, estimated: per-machine corollaries (hours, in progress); the Expr entry point (decoder in nano + proof, about
the size of u10: days); Ev = Denotes using con-leche's lemmas (several days; spike first on UInt64.add / ite /
List.cons); the Denotes copy + Expr-identity check (days; Lean 4.35 vs 4.34.1 toolchain gap); restating the top
theorems around Expr (days).

## OWNER NOTES (2026-11-23): Expr is the semantic interface
- Expr is how meaning is defined from now on, because that is what Lean does. We copy Lean's approach.
- REUSE CON-LECHE MAXIMALLY (its term type, Denotes, lemmas). Show our meaning is literally theirs.
- Ev is internal. It may be rewritten (and renamed, e.g. ExprRun) freely, as long as self-hosting is kept.
- The most important check: nano's elaboration of ITSELF equals Lean's (C_lean_all). Per-program checks for other
  programs are optional extra assurance.
- Back-end-only self-hosting is possible: the compiler compiles the Expr of its own source, exported from Lean's
  elaborator, so no nano front end is needed for the proof. The nano front end stays useful for running
  standalone (no Lean needed) and is still proved against Lean as far as possible, but it is not on the critical
  path of the main theorem.

## SIMPLIFICATIONS (owner, 2026-11-23)
- Reuse con-leche maximally: emit con-leche's own term type (a subset of it) as nano's Expr, so no translation step.
- Ev is internal, so rewrite it to mirror Denotes rule by rule (same environment / bvar / app / lam / let structure;
  constants through the same table). The Ev = Denotes bridge is then an induction whose cases are con-leche's own
  lemmas (WellDenotedV_inst, beta, app, literals) plus the value-to-set encoding.
- LATER: reduce the IRs to Expr → one pre-assembly layer (J) → thin per-target encoders (RISC-V, ARM, x86).

## THE HOLY GRAIL (owner, 2026-11-23): meaning = con-leche's Denotes, computed by self-hosted, proven code
1. Meaning: con-leche's `Denotes` (ConLeche/Denotes.lean), copied verbatim or imported once nano moves to its
   Lean version (4.35). Check the copy's elaborated Expr is identical to con-leche's (C_lean-style tooling).
   Denotes is a definition, not a program, so it stays in Lean, not in nano.
2. Proof: machine code → Sem (have) → Ev of the Expr (eval_emit; for ANY Expr via the entry point) → Denotes of
   the Expr (new: Ev agrees with Denotes on the slice). Needs the slice-to-con-leche-term map, the set encoding of
   UInt64/Bool/Nat/lists/pairs, the ~50 constants via their definitional equations in con-leche's model, and an
   induction over the slice. The boundary: the output bytes = the byte list that Denotes assigns to f(input).
3. Self-hosting: the compiler is an Expr in the slice, so (2) applies to itself; the binary identity comes from the
   fixpoint, later from kernel evaluation.
This replaces the "standard meaning" route. Keep the per-program certificates Ev(e) = f as a cross-check.
Trust at the end: one initial kernel check (bootstrap), then re-checks with nano-compiled con-leche; the ISA models
(Sail RV, Sail ARM, DeepMind ARM) + hardware; propext/Choice/Quot.sound + ZFC with inaccessibles; the Spec I/O boundary.

## MAIN THEOREM PLAN (owner, 2026-11-23): Expr is the central IR
Theorem A, the main theorem: for every Expr e in nano's slice and every input, the compiled machine code (RISC-V
Sail, ARM DeepMind, ARM Sail) writes the encoding of Lean's value of e to the output location.
Ingredients:
- have: ExprSpec (the slice and Ev); the compiler theorems (machine code = Sem) on all three machines;
  eval_emit (Ev(emit p) = Sem p); C_lean_all / C_expr (the compiler's Expr = Lean's, and Ev of it = mC).
- new 1: the Expr ENTRY POINT. A decoder from serialized Expr to nano's AST, written in nano (self-hosted), with
  Sem(decode e) = Ev e for EVERY e in the slice. Composed with the compiler theorems, this gives Theorem A with
  "Ev" in place of "Lean's value".
- new 2: Ev = Lean's value. Per program, an auto-generated certificate Ev(e) = f, proved symbolically (by
  unfolding, not by enumerating inputs; cost scales with program size). In general: a standard meaning, then
  con-leche's model.
- self-application: the compiler is total (fuel, no partial), so it is an Expr in the slice and A applies to
  itself. The binary = compiled code comes from the fixpoint now, and from kernel evaluation later.
Theorem B (front end) stays a per-program check: nano accepts + Expr matches ⇒ by A, output = Lean's value.
Programs with partial defs (e.g. parts of con-leche) must be rewritten in total, fuel style with a proved equation
(the "friendly track") before they are Exprs in the slice.

## TRUST CHAIN FOR SELF-HOSTING (owner, 2026-11-21) — what is proved, what is trusted, what is next
Status (keep_round1_expr; EXPR.md is the detailed report):
- E (Expr emitter) is written in bootstrap nano and compiled by B2. Its output = emitSpec byte for byte.
- Check: C's emitted Expr = Lean's elaborated Expr, 234/236 defs. o32/o38 are representation only
  (k ∈ {0,1}, used only in `k == 1`). Nat step 1 (numOkP, Lean's numeral default) targets 236/236.
  Big-number Nat is deferred.
- Proved: eval_emit (Ev of emitted Expr = nano's Sem, all programs); C_expr (mC = Ev of C's Expr);
  self_expr_C (C's RISC-V code writes that value). The fixpoint B2 = B3 is checked.
- LONG-TERM (owner, 2026-11-22): Ev in general. (a) Define the standard meaning of the emitted Expr slice and prove
  Ev = that meaning for every Expr. (b) Then prove Ev = con-leche's model meaning for every Expr in the slice.
  Composed with the compiler theorems on RISC-V (Sail) and ARM (DeepMind + Sail), this gives: for every program
  whose Expr matches Lean's, the machine code computes con-leche's meaning of Lean's Expr. Applied to C compiled
  by itself, the B2 identity comes from the fixpoint / kernel evaluation. TODO soon: the ARM analogue of
  self_expr_C, which only composes C_expr with C_correct_native_release.
- NEXT (owner, 2026-11-22): prove the SELF-HOSTED emitter E itself. Restate the chain over E's own definitions
  (a SrcLink-style cert for E), or prove E = emitSpec. Until then, E is checked byte-equal to emitSpec.
- In progress: make "emitted Expr = Lean's Expr" kernel-checked (generated literal + decide/rfl), not a script check.
Trusted: Lean kernel + propext/Choice/Quot.sound; the ISA models (Sail RV, Sail ARM, DeepMind ARM) and
hardware = model; Spec/ (loader, encodings); the Expr generator reading the environment; Ev's faithfulness
to Lean for programs other than C; Lean's toolchain once, for B1.
Next, to remove trust (owner wants all three on the roadmap):
1. Kernel proof that B2 = mC(C's source), which removes the B1/toolchain trust (see "remove trust in the bootstrap toolchain").
2. A general proof of Ev against a formal model of Lean's Expr semantics (e.g. con-leche's set-theoretic model).
3. Re-check all nano proofs with con-leche (an independent verified kernel).

## LONG-TERM (owner, 2026-11-21): kernel as trusted execution for the bootstrap binary
Theorem `mC source = B2bytes`, proved by kernel evaluation, split into stages with intermediate literals
(lex → tokens → AST → … → bytes). It is checked by Lean's kernel (removes the Lean-toolchain/B1 trust) and
re-checked by con-leche (an independent verified kernel). This is diverse double compiling with a proven route.
Step 1: kernel-evaluate the lexer stage on C's source and time it in both kernels, then extrapolate.
Feasibility is unmeasured.

## LONG-TERM (owner, 2026-11-21): Expr side output + Expr entry point (all self-hosted)
1. Side output: nano also emits, for each def, the Expr it means, together with the computed value.
2. Spot check: nano's Expr = Lean's elaborated Expr (up to generated names/helpers). Theorem: if they match, nano's
   output = Lean's output. Proof: evaluator for nano's Expr fragment, eval(emit a) = nano semantics of a, and the
   existing compiler theorem. When they don't match, nothing is claimed (elaboration differs), so only fuzz applies.
3. Expr entry point: a second front door that takes elaborated Expr (e.g. exported from Lean). It is written in
   nano and self-hosted, an optional input, not the shelved Lean-hosted compile mode. Users who don't trust nano's
   parser/elaborator can use Lean's elaborator and rely only on the back-end theorem (Expr fragment ⊆ Lean,
   same Expr ⇒ same output).
4. Self-consistency check: the compiler compiled by Lean's toolchain (B1) vs. compiled by itself (B2 = B3), plus
   comparing nano's Expr of its own source with Lean's Expr of it (extends SrcLink). If equal, nano's parser /
   elaborator don't change the meaning of nano's own code.
Reuse the earlier Expr-level work in Legacy/Riscv/Frontx (kernel-checked equation per function) where it fits.

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
- STATUS (branch nano-v2, 2026-11-17): plan + increment 1 (comparisons + `if`) in Testing/notes/NANO_V2.md:
  `Nano.V2.nano_stack_correct` proved (Sail axioms only), oracle fuzz 0 differences, QEMU+Sail 1344 pairs; v1 untouched.
  Found: v1 `nanoElab` accepts an empty binder group `( : UInt64)` (Lean rejects) — NANO_V2.md C1.

### NANO_V2_SPEC (owner, 2026-11-17 19:25): work may proceed on it without a separate confirmation (the content is Astra-advised, not owner-chosen)
The frozen spec on branch nano-v2 (v1 constructs unchanged + exactly the Astra-decided additions; v1 stage formats;
Int64 dropped for milestone 1) is accepted as the working freeze. Like v1's `nanoElab`/`Prog.eval`, the meaning stays a
draft the owner may review later; changes after the freeze still go through the owner.
- Owner (19:35): the elaborator spec is deliberately LOOSE for now; it is a working draft, to be tightened by the owner later. Do not treat its details as final.

### NANO v2 FINAL RUN: two independent paths (owner, 2026-11-17 19:45)
- Path L (trusts Lean's compiler, acceptable since the elaborator is trusted anyway): build the nano compiler's Lean
  source `s` as a native executable with the plain Lean toolchain (`lake`), run it on the UTF-8 bytes of `s` → Bᴸ.
- Path N (our binary only): run B₁ (then B₂) on QEMU/Sail on the same bytes → B₂ (→ B₃).
- Required check: B₂ = B₃ byte for byte. (Owner 19:55: comparing against the Lean-toolchain path is NOT required. Bᴸ
  here means the OUTPUT of the Lean-compiled compiler run on s — not Lean's own native executable, which naturally differs.) The proof route (ImplementsBytes B₂ Cκ without compiler 1 in its dependency
  closure) is the separate, stronger claim; keep the two clearly labelled so they are not confused.

### NANO v2 CHECKPOINT BEFORE THE SELF-HOSTING DECISION (owner, 2026-11-17 20:00)
- Bootstrap binary: may simply be the Lean-toolchain-compiled nano compiler (we trust Lean's definitions/elaborator, so
  Lean's compiler is acceptable for the bootstrap); the S3/B₁ route is an alternative, not required.
- REQUIRED CHECKPOINT: at one point, the ENTIRE nano compiler exists as Lean source written in the nano subset
  (one clearly named folder/file set, e.g. Nano/V2Self/), accepted by Lean, with its status documented (what nano itself
  accepts of it yet). The owner reviews this before deciding how to self-host (bootstrap from Lean's compiler, from B₁,
  or from the elaborator alone; which cross-comparisons to do).
- Until then: interim self-host / self-compile checks are fine (e.g. compiled stages on their own text, partial fixed
  points), but no final self-hosting route is locked in.
- Astra round 6 (E/F/G proofs) did not arrive (Astra out of tokens); work from NANO_V2_SKELETONS.lean.

### PAUSED (owner, 2026-11-17 21:00). All boxes archived; recurring checks disabled.
Branch heads (each has a HANDOFF section):
- nano-v2 f3fe8b9: language + back end (increments 1–4 + products/loops/buffers front end, codegen proofs except
  buffers; HANDOFF "pause 20:50" in Testing/notes/NANO_V2.md).
- nano-v2-src 33b1ab5: OWNER REVIEW CHECKPOINT. Nano/V2Self/ = whole nano compiler as nano-subset source, ALL accepted
  by nano's own front end incl. the nano driver `m`; Testing/notes/NANO_V2_CHECKPOINT.md (HANDOFF inside).
- nano-v2-boot 2e49781: bootstrap B₁ via S3 (4 stages + parser bridge p2bVS_eq; parser S3 compile unverified);
  HANDOFF in Testing/notes/NANO_V2_BOOT.md. Optional until the owner chooses the self-hosting route.
- Templates on main: Testing/notes/NANO_V2_SKELETONS.lean (round 5) and NANO_V2_SKELETONS6.lean (round 6), verified 4.29.
- s3-rec 6e9e02a (con-leche WIP, paused earlier).
RESUME: owner reviews Nano/V2Self/ and decides the self-hosting route. Then restart one Opus language+back-end box
(buffer proof via round-6 F, Sail loop layer via E, result/status + ImplementsBytes), Sonnet boxes as needed, a Haiku
runner; re-enable triggers trig_01Lbdjhesnym2ZPegRnLPVmf (team check) and trig_01XTKyxsqmfYZouFjjRfeHdt (3-hourly).
- Note for resume: the parser S3 probe (nano-v2-boot bf6ba78, ProbeParse) ran ~16 min without finishing before the pause; likely over the 5-min rule, needs an s3.depth-4 probe / split first.

## 2026-11-18 01:50 UTC — NANO v2 SELF-COMPILE FIXED POINT (tested, NOT yet proved)
- Branch nano-v2-src @ 09e97b6. Self-source S = `Testing/nano/v2self/self_S.lean` (186 defs: Base + Lex2 + Par1 + Gen + driver m),
  generated from the C files by `build_self_S.py`; input text `self_S_input.txt`.
- B₁ = Lean-toolchain-compiled S (TRUSTED: Lean compiler; Array-backed bootstrap prelude, checked equal to the List
  prelude on 20 sources). B₂ := B₁(S) = 248,632 bytes, sha256 2ceffa2c…2ebce. B₃ := B₂(S) on QEMU (64 MiB, 1.6 s) == B₂.
- Reproduced independently by the main session from a clean worktree: `Testing/nano/v2self/boot/fixpoint.sh OUT` (37 s), same sha256.
- Architecture: Astra rounds 7–13 advice (notes NANO_V2_ASTRA7..13). Not yet: Sail run of B₂/B₃ on the full source,
  determinism under different work-memory fill, proofs (Astra 11 plan: soundness on success + acceptance witnesses).

## LATER (owner, 2026-11-19): unbounded loops in nano
Nano programs always halt (only fuel loops on an explicit Nat). For long-running programs (servers, event loops) consider an
UNBOUNDED loop construct later. Correctness would be stated per step / over the output stream (a simulation or trace
property), not as a final-result theorem. Separate from the spec-side fuel: the meaning interpreter and refParse use
arbitrarily large fuel only so they are total Lean functions; "enough fuel" is a named hypothesis of the final theorem.

## OWNER GOAL (2026-11-19): nano v2 correctness statement
Main theorem: for every source in the nano subset and ALL input bytes, the code C compiles implements `Sem` of that source
(Implements1-style, machine-state spec the owner reviewed), with named premises (fuel for refParse/Sem, work memory, size).
Per-program bridge: the one-source certificate `Sem (parse src) = the Lean function` (first for small examples and C itself,
later generated automatically) — gives "this code implements this Lean function" for each compiled program.
Long term: grow the subset (parser spec + Sem + proofs, one construct at a time) until it covers most of Lean.

## AFTER THE PROOF (owner, 2026-11-19): organize the nano v2 proofs
Once C_correctL has no premises and the certificate closes, reorganize Nano/V2Self/Proof/ before merging:
- merge duplicated or split files (e.g. ParInvExpr/ParInvExpr2, the ParRunWF* family, ParInvVal/ParInvValRep, the cert work in
  MainCertC* vs Proof/Cert/*), and give directories a clear layout: Parser/, Own/, Gen/, Machine/, Bridge/, Cert/, Main/;
- delete dead lemmas and scratch modules; keep each module ≤ 5 min / 8 GB;
- one top-level file that states the final theorem and lists every remaining hypothesis, for the owner's review;
- check axioms on the top theorem and the fixpoint after the reshuffle (moves only, no proof changes in the same commit).

## LATER (owner, 2026-11-19): remove trust in the bootstrap toolchain
For now ACCEPTED: B₁ is compiled by the Lean toolchain (trusted), and the fixed point B₃ == B₂ is evidence that B₂ = mC(T)
(T = C's source). With the main theorem + certificate (Sem(parse T) = mC) this gives "B₂ implements mC" modulo that trust.
Future: prove B₂ = mC(T) in the Lean kernel (stage-by-stage, chunked kernel evaluation with intermediate literals), which removes
the Lean-compiler trust and leaves only the kernel, the Sail model and Spec/. Feasibility unmeasured; do it after the
certificate's text link (refParse(lex T) = PC.all), which is the first half of the same job.

## NEXT (owner, 2026-11-19): ARM back end for compiler #2 (C)
Goal: `CompileCorrect arm compileC_arm` and `CompileRuns arm compileC_arm` against the ARM Sail model, same statement shape as RISC-V
(Spec/Alloc.lean, `armMapping` in Spec/Machines.lean). Reuse: C's front end, ownership and certificate unchanged; a new
code generator to AArch64 from the same reference code (CG / J machine templates), proofs mirroring the RISC-V Machine/
layer, built on the existing Arm/proofs full-step lemmas (b, bl, cbz/cbnz, b.cond, movz/movk, add/sub imm, mov, ldr/str/ldrb/strb/stur,
register ALU ops). Later: write the ARM generator in the nano subset so C self-hosts on ARM (native on Apple Silicon).
Owner decisions (2026-11-19): an `arm : Machine` instance in Spec/ next to `riscv` is approved; code below 2^29 for now
(expand later); an ARM RAM window is assumed (chosen from what Arm/proofs supports, MMU off at EL3).
Order (owner, 2026-11-19): (1) organization pass + survey of moving everything to the newest Lean
(Testing/notes/LEAN_435.md); (2) migrate the repo, both Sail models, Arm/proofs and Arm/apc to ONE Lean version: FIRST 4.34.1 (owner, 2026-11-19: the ARM
model and Arm/proofs already work there; most breakage is 4.29->4.34), prove ARM there, THEN step everything to 4.35.0 (owner;
4.36 rejected: it caps field-carrying constructors at 244, and the RISC-V Sail model's `instruction` has 353); (3) then the
ARM proof and the larger code work.

## STATUS + GOALS (owner, 2026-11-20)
- Unproven ARM back end WORKS (Testing/nano/v2self/arm/ on nano-v2-src): nano translator rv2arm.lean; ARM-B2 self-compiles to
  B2.bin byte for byte under qemu-aarch64. Prove it next ("get it working, then prove, rewrite slightly where unprovable").
- Rule: every new piece of code carries proof notes next to it (PROOF_NOTES.md / header comments: intended semantics,
  invariants, register/memory conventions, which lemma will cover it).
- Limits for now (owner OK): output <= 512 KB (nano buffer capacity 2^19), input < 1 MB (2^20). Enough for answers.
- LATER: raise the buffer capacity, compiled-code size and input size (a compiler + spec change, then rebuild and
  re-check proofs). Needed for the goal below.
- GOAL: compile con-leche (leanprover/con-leche, the Lean kernel checker; ~22k lines in the checker core's import closure,
  see Testing/notes/CONLECHE_*.md). Needs (a) a much larger nano subset: user inductives incl. Expr (>2 recursive fields),
  structures, Name/String/Char, Array, HashMap, Except/state monads, partial; (b) the larger capacities above.
- INTERIM (owner, 2026-11-20): while the full Sail ARM model does not build on 15 GB boxes, prove the ARM blocks against
  DeepMind's arm64 Lean model (Arm/apc), with lemmas stated in the same shape as the Sail full_* lemmas.
  LATER: the DeepMind <-> Sail equivalence (per instruction form we use) on a big-memory machine (e.g. a large cloud box),
  so the final theorem is against Sail.
- LEAN VERSIONS (owner, 2026-11-20): never hand-edit the Sail RISC-V model (it is trusted; "very dangerous").
  For now each machine may be proved on its own Lean version ("ok-ish"): RISC-V on 4.29 with the unchanged model,
  ARM on 4.34.1/4.35 with the machine-independent chain. Wanted: RISC-V on 4.34; ideal: both on 4.35. Route for
  RISC-V: regenerate with the official Sail Lean backend (same sail-riscv commit), show the owner the generated diff
  and a definition-level comparison, re-run the RISC-V conformance tests; no hand patches.
- BRANCHES (owner, 2026-11-20): nano-v2-src = Lean 4.29, RISC-V proven, unmodified RISC-V model.
  lean-4.34 = Lean 4.34.1, machine-independent chain + ARM (RISC-V model not built there).
  rv434-experiment = both on 4.34.1 with a HAND-EDITED RISC-V model (clearly marked; never merged without owner review).
  See Testing/notes/BRANCHES.md.
- LATER (fuzz finding, 2026-11-20): each fresh list reserves a fixed 4 MiB (2^19 x 8 B) of work memory that is never
  reused, so ~20 fresh lists exhaust 80 MiB. Correct (OOM is reported, never a wrong answer) but wasteful. Fix together
  with the capacity work: growable lists or reuse.
- ARM MEMORY (owner, 2026-11-20): ARM RAM window = 1 GiB at [2^31, 3*2^30) (E, 9ddb1d4); meets the existing 2^31 bound, so no window proof change; avoids GIC/UART device pages; expand later if
  easy. The shims give 1 GiB of work memory (unproven glue); the ARM theorem will cover runs whose work fits the window.

## MERGED TO MAIN (2026-11-20)
nano-v2-src merged into main: RISC-V proven (Lean 4.29, unmodified Sail RISC-V model; C_correctLO / C_runsO);
ARM proven on DeepMind's arm64 model (Lean 4.34.1; C_correct_armDM / C_runs_armDM, loader premise ArmLoader;
independently rebuilt by two sessions, standard 3 axioms). Working ARM back end + nano translator rv2arm (certified
source meaning, CertArm), shims (1 GiB work), compile.sh / run.sh / try_arm.sh / cross_check.sh. In progress on
nano-v2-src: the same ARM theorem on the official Sail ARM model (C_correct_armSail), then RISC-V model regeneration
with the official Sail tool on 4.34.1.
NEXT (owner, 2026-11-20), in order: (1) expected total program size (code vs source, where the 512 KB / 1 MB limits
bite); (2) speed of compiled programs; (3) grow the parser's accepted syntax until it can express con-leche.
- ORDER + RULES (owner, 2026-11-20): (a) all machines on ONE Lean version (RISC-V regenerated model + ARM on 4.34.1);
  (b) basic speed work, measured by exact executed-instruction counts (Testing/notes/BENCH.md baseline);
  (c) THEN grow the accepted syntax toward con-leche, one construct at a time. Every growth step must keep all proofs
  green (REVIEW axioms as pinned, RISC-V + ARM theorems build) AND must not regress the benchmark baseline
  (self-compile instruction count and the example table); each step gets a CHANGELOG entry.
  Also per step: a short code check: total code size per area (compiler source, proofs, glue) does not grow
  without reason, no dead code (deadcode tool), shared abstractions reused instead of duplicated (e.g. one generic
  machine adapter, one block table). Size table kept in Testing/notes/CODE_SIZE.md.

## Later (owner, 2026-11-20)
- Sail ARM: the theorem temporarily makes no claim about sp (register 31; Sail-local mapping, see Arm/sail/NOTES.md).
  Later: restore sp (prove it unchanged / reset on exit) by exporting SP_EL0/SP_EL3/PSTATE.SP from the full_* lemmas.
- Later: reset the memory chunks (work/scratch regions) on exit, so the caller gets them back in a defined state.

## Order after release-434 (owner, 2026-11-20)
1. Cleanup (low risk) that also prepares optimization: archive dead code, prune dead decls, dedupe the rv2arm table,
   and factor the Gen proofs so the room/OOM check and branch offsets sit behind a few shared lemmas
   (CODEGEN_SPEED.md: that is what makes the speedups PERVASIVE today).
2. Core codegen optimizations, bounded (target ~2x fewer executed instructions on BENCH, then stop): one overflow
   check per function, small-immediate operands, maybe top-of-stack in a register.
3. ARM-specific speed so ARM is not much slower than RISC-V (shorter rv2arm sequences; later a native ARM backend).
4. Before growing: assess four target programs — con-leche (Lean checker), LeanZip, Lean SVG, Lean Align — for what
   each needs from the language/compiler (features, def count, sizes, memory) and what is easy vs hard.
5. Syntax growth toward those four, starting with con-leche (raise the 511-def cap, parser node cap, clear errors),
   proofs green, no speed regression.

## Generated-code speed (analysis only for now)
Goal: no obviously slow patterns in the code the compiler emits.
Evidence (B2.bin disassembly): stack-machine codegen; every push = addi + bgeu + j + sd; `x < 65` ≈ 15 instructions
(good code: 2). B2 has ~10.9k per-push overflow checks and ~14k sd.
Order (each: measure on BENCH.md programs + self-compile, then prove; proofs green, no regression):
1. one stack-overflow check per function (max depth) instead of per push
2. small-immediate operands for ALU ops and compares
3. direct conditional branch when the target is in range (else branch-over-jal)
4. inline constant defs (zero-arg defs returning a literal)
5. top-of-stack in a register (drops push/pop pairs) — biggest win, most proof work
6. ARM: shorter rv2arm sequences for common forms (currently fixed 4-word blocks, ~3.6x)

## Later (owner, 2026-11-20), after con-leche syntax
- Native ARM backend: generate AArch64 directly from the IR (no rv2arm translation) for speed; proved against the
  same A64 machine interface (A64Sem / Sail ARM), RISC-V path unchanged.
- Verified inline assembly ("skip through the compiler"): a Lean value {words, f, proof : code implements f on the
  Sail model (Spec Implements-style contract + the compiler's register/stack/heap/OOM convention)}; the compiler
  copies the words verbatim, the source semantics sees only f, the correctness proof gets one new case. No unproved
  blocks accepted. ARM: free if the block uses only rv2arm-supported forms, else an ARM block + its own proof.
- x86-64 backend (owner, 2026-11-20; later): preferred model = Sail x86 (REMS sail-x86-from-acl2, translated from
  ACL2 x86isa) via the existing Sail→Lean pipeline; alternatives ACL2 x86isa directly, K x86-64 semantics (no Lean
  backend). No vendor-official model exists: record in MODEL_PROVENANCE.md exactly where the model comes from, which
  commit, how it is generated (commands, toolchain, patches), and that it is community/translated. Re-adapt when the
  model updates. Approach as for ARM: an X86Sem-style interface over the few dozen instruction forms the compiler
  emits, a RISC-V→x86 translator first, native generation later.
- Spec strengthening, read confinement (owner, 2026-11-20; later, needs owner-approved Spec change + re-freeze):
  add to CompileCorrect/CompileRuns that the compiled code never READS memory outside its code, input, output and
  work blocks (today only writes are confined: memory outside the output prefix + work block is proved unchanged).
  Out-of-memory remains the only failure mode. Process isolation is out of scope (bare-machine model; the OS is a
  separate layer).

## ARM in the spec (owner-approved 2026-11-20; after the reorg-nano merge)
- Define the ARM machine(s) in `Spec/` (as `riscv` is), so `C_correct_armSail` is stated against a reviewed `Spec/`
  machine, not one defined in `Arm/sail`. Owner reviews the new `Spec/` text; re-freeze FROZEN.sha256 only after approval.
- DeepMind's `ArmLoader` precondition (code executable, data blocks readable+writable) is met by any normal loader /
  shim mapping; state that in the shim notes. Memory wiping on exit is the separate "reset memory chunks" item.
- Later: native ARM backend (no RISC-V translation); notes in TRUST.md say how the current ARM theorems are built.

## Per-target layout (owner, 2026-11-20; after cleanup step 8)
Top level becomes symmetric per target: `Spec/` (RISC-V + ARM machines), `Nano/` (compiler + target-independent proofs),
`Riscv/` (model regen, step lemmas = today's Nano/Base/Riscv, RISC-V target proofs), `Arm/` (models, step lemmas, ARM
target, later the native ARM backend), `Legacy/`, `Testing/`. Done after cleanup step 8 separates the RISC-V-specific
parts from Nano/Run, so the move is complete in one go. Same checks as reorg-nano.
- Spec/ scope (owner): Spec/ = what "correct" means (machines, CompileCorrect/Runs, Encode, memory rules). Generated Sail
  models stay external deps; each target folder holds its regen scripts + provenance, step lemmas, codegen/target proofs.
  Later Spec/ reorg: move the trusted SOURCE-language definitions (lexer spec, grammar/pOf, semantics; today in
  Nano/V2Self, listed in REVIEW.lean) into Spec/, so everything to trust is in one place.
- Per-target model files (owner): each target folder holds `gen/` with the full regeneration recipe (pinned generator +
  model commits, patches, regen script; for DeepMind a fetch script at the pinned commit) and `MODEL.sha256`
  (`Testing/scripts/model_hash.sh` value + file count) next to it; release_check's `hashes` gate reads those files.
  Today: RISC-V regen in Testing/riscv/gen (moves to Riscv/gen), Sail ARM in Arm/gen, hashes only in the central
  Testing/notes/MODEL_PROVENANCE.md, DeepMind has a pinned commit + hash but no fetch script (to add).
- Rename Nano/V2Self by compiler stage, code + proof together (owner; same pass as the per-target move): Nano/Lexer
  (C/Lex2 + Proof/Lex), Nano/Parser (C/Par1 + Proof/Parser), Nano/Ownership (C/Own + Proof/Own), Nano/Codegen (C/Gen +
  Proof/Gen), Nano/Run (Proof/Machine, target-generic; RISC-V parts to Riscv/), Nano/SelfHost (Cert, CertArm, SrcLink,
  Bridge), Nano/Main (top theorems + REVIEW.lean), Nano/Tests, Nano/Base. Module paths change; def/theorem names do not.
  Trusted parser/grammar definition later in Spec/Source/ (Spec/ reorg); its proof stays in Nano/Parser.
- README.md in every stage/target folder (owner): what is in the folder (one line per file or subfolder), what this
  part does and where it sits in the whole (which stage feeds it, which uses it), design decisions made here and why
  (with alternatives rejected), what the stage does, its input/output, the main definitions and
  theorems (file:name), what it assumes from the stages before it and guarantees to the next, how to build/check it,
  and known limits. Written for a human reader and for an agent starting cold. Kept short; updated in the same PR as
  any change that makes it wrong.
- Native ARM backend target order (owner, 2026-11-20): prove it on DeepMind ARM first (faster to build and check), fuzz
  it heavily under QEMU, and treat that as enough for now; the Sail ARM proof follows later via the same A64Sem
  interface. Note: the two ARM models are NOT proved equal to each other; the compiler is proved correct on each
  separately through A64Sem.

## Syntax decisions (owner, 2026-11-21)
- Extend the trusted lexer definition for comments/attributes: approved.
- `match` via a desugar stage in the trusted parse definition (pOf): approved; broader parser changes allowed if heavily
  fuzz-tested (differential vs desugared/stripped programs, Lean #eval cross-check, reject fuzz).
- Extra work memory (+8 MiB for match): accepted.
- Open: namespace flattening; out-of-range index semantics (silent default / trap / proven-in-bounds).
- Order: syntax growth now, in parallel with the native ARM proof (front end vs codegen/run files); core optimizations
  after the native ARM proof lands, applied to both RISC-V and native ARM generators.

## Self-hosting is a hard gate on every merge (owner, 2026-11-21)
Every PR that touches the compiler (any stage, either generator) must, before merge:
1. regenerate the self-hosting proofs (Nano/SelfHost: Cert, CertArm, SrcLink, Bridge) for the new compiler source, and
   build them with REVIEW + review_axioms unchanged ("OK: 8 theorems");
2. reach the fixpoint on RISC-V: B1 → B2 = checked-in B2.bin, B3 = B2 (sha256 in the PR);
3. reach the fixpoint for native ARM: GA_arm compiles its own source to itself, and the 3-host cross matrix
   (RISC-V / rv2arm / native) is identical (Testing/nano/v2self/native_arm/cross_native.sh);
4. release_check.sh gates fix1/fix23 pass.
The compiler's OWN source stays in the bootstrap subset (the language as of release-native-arm), even as the
compiler accepts more (owner, 2026-11-21: avoids confusion). New syntax is for user programs only; a check script fails
if Nano/{Lexer,Parser,Ownership,Codegen,Main} compiler source uses anything outside the subset. Exception (owner,
2026-11-21): comments are allowed in the compiler source once the comments feature is merged (they change no code). Syntax and optimization PRs merge one at a time; the second one re-regenerates SelfHost and re-checks.

## Native ARM route and IR plan (owner, 2026-11-21)
- Release (combined-2 / #17): native ARM via option E — the compiler runs Gen, takes its J program, and a thin J → ARM
  atom translator (fusing J steps into rich A64 instructions, variable length) emits the code. The translator is written
  in nano's bootstrap subset as part of the compiler, so the native compiler self-hosts; proven on DeepMind ARM
  (generic over A64SemN, so Sail needs only its instruction facts). GenArm.lean stays as a test oracle.
- Next after the release: make J an explicit, target-neutral IR that the generator emits (instead of RISC-V words),
  with RISC-V, ARM (and later x86) as thin proven encoders; grow J with target-friendly ops so encoders can use each
  ISA's features; do optimizations on J (proven once). Hyper-optimized per-ISA back ends can come later on top.
- Syntax: nano's accepted language is a SUBSET of Lean's (owner, 2026-11-21): every program nano accepts, Lean
  accepts with the same results; fuzz FAILs on any nano-accepts/Lean-rejects case. Concretely: misplaced docstrings/attributes are rejected too, via a
  decl-modifier check in the trusted desugar spec; reject fuzz checks Lean-rejects ⇒ nano-rejects.
- Lean parser as the model (owner, 2026-11-21): nano's syntax rules follow Lean 4's own parser (src/Lean/Parser) rule by
  rule, with file:line citations in Testing/notes/LEAN_RULES.md; elaborator-dependent meaning (literal defaulting,
  name resolution) is handled by rejecting ambiguous programs + differential fuzz against real Lean. TARGET (owner): nano's parser
  becomes a transcription of Lean 4's own parser for nano's subset (same rule structure, names and order, each rule
  citing its Lean source), written in nano once nano has monads/structures/typeclasses; real Lean is the test oracle
  (no formal equivalence: Lean's parser is partial/meta code and not provable as is). Until then new syntax follows
  Lean's parser rule by rule.
- Why nano exists next to Lean (note for readers): Lean 4 self-hosts but its code generator (Lean → IR → C → clang)
  is unverified; nano proves source-to-machine-code correctness against Sail/DeepMind ISA models with no C compiler in
  the trust base, and proves its own binary is its compiled source.
- DECIDED (owner, 2026-11-21): stay fully self-hosting, nano style; grow nano itself; no second Lean-hosted mode
  for now (option (2) below is shelved). Was open: reaching big Lean programs. (1) grow nano itself (strict, self-hosting); (2) add a
  second mode next to nano: Lean elaborates, nano's proven back end compiles the kernel-checked definition and emits a
  per-program proof that the machine code computes that definition (trusts Lean's kernel only, not its compiler/IR/C;
  not self-hosting; like Legacy/'s compile%). Rejected for now: compiling Lean's IR/LCNF (would trust Lean's unverified
  optimizer). Lean source tour in Testing/notes/lean_tour/ informs this.
- Lean as blueprint (owner, 2026-11-21): use Lean's compiler as a design source and test oracle only; nano stays a
  subset of Lean's parser. Track Lean's IR design (LCNF passes, λRC IR, RC/borrow inference, reset/reuse in-place
  updates, unboxing; Testing/notes/lean_tour/{lcnf,ir}.md) as the reference when J becomes an explicit IR and when
  optimizing; compare our IR choices against it. Note: Lean emits C (then clang), its whole compile path (LCNF → IR →
  C → clang → runtime, plus implemented_by/extern) is unverified; nano proves source → machine code.
- Proven equivalence with Lean where possible (owner, 2026-11-21): Lean parser/lexer pieces that are total (not
  partial; e.g. char classes, numeral decoding, escapes, keyword lists) get theorems that nano's trusted definitions
  equal Lean's own functions (or are a subset with equal values); nano's trusted defs may be rewritten to mirror them.
  Partial/stateful parser code: differential fuzz only; elaborator-dependent meaning: conservative rejection + fuzz.
  Work: Nano/LeanEquiv/, Testing/notes/LEAN_EQUIV.md.
