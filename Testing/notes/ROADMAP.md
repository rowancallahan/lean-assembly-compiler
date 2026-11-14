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
