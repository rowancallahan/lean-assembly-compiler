# Target functions

Goal of each row: `ImplementsMapped code f` for the named Lean function `f`, RISC-V first, then ARM.
"Needs" = what the compiler lacks today (see `Proven/ARRAYS.md` for the current language).

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

- Scope: a SUB-compiler for pure functions, bytes in → bytes out (`Proven/Encode.lean`). No IO, no OS interaction.
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
- Memory: blocks are lists of cells; layouts of pairwise-disjoint blocks; owner reviews byte layouts in `Encode.lean`.

# Far future (noted, not planned)

- Self-hosting: compile the compiler's core (program bytes → machine code bytes) with itself.
- Multi-core: each core gets its own writable block, shared blocks are read-only, one coordinating core
  only reads the others' "done" state; results are interleaving-independent by the separation theorem.
- con-leche / con-ron compiled to proved ARM and RISC-V code.
- lean-svg's `render : Options → ByteArray → Except String ByteArray` as a large pure client.
- A tiny real-time operating system on RISC-V proved on the same model.
