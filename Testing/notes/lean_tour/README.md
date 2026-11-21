# Lean's compiler vs nano: what nano can reuse (Lean v4.34.1)

Synthesis of five reader notes in this folder (`elab.md`, `lcnf.md`, `ir.md`, `runtime.md`, `selfhost.md`) and `../LEAN_RULES.md`.
Caveat inherited from the readers: nobody ran a Lean toolchain for the tour notes; worked IR examples are derived by reading. Effort numbers are rough guesses, not measurements. `LEAN_RULES.md` is the exception: it ran real Lean 4.34.1 against `B2.bin`.

## 1. Two pipelines side by side

```
Lean:   source ─parse─▶ syntax ─elaborate─▶ kernel Expr ─▶ LCNF (pure, then impure phase) ─▶ IR (λRC) ─EmitC─▶ C ─clang─▶ binary
                                (types, instances,            (simp, specialize, erase,        (inc/dec, reset/reuse,
                                 coercions, match compile)     join points, boxing, RC)         unbox) + C runtime (lean.h, bignum)

nano:   source ─lex─▶ tokens ─parse─▶ AST ─ownership check (o41)─▶ J (templates) ─▶ RISC-V / ARM words
```

| | Lean | nano |
|---|---|---|
| Front end | Parser produces syntax only. The elaborator (`TermElabM`, instance search, unifier, 100k+ lines) decides meaning: literal types, coercions, match compilation, termination | Lexer + parser; typing is a fixed small rule set. No elaboration stage, so nano's parse *is* its meaning |
| Middle | LCNF: ~40 passes (simp, specialize, erasure, join points, CSE, ...) then the impure phase (boxing, borrow, RC, reset/reuse). In v4.34.1 these are LCNF passes, not `Compiler/IR/*` | One checker (`o41`: linear buffer use, so in-place updates are safe) and then J. No optimisation passes |
| Back end | IR → C text → clang. clang and libc are trusted | J templates → words directly. No C, no libc |
| Memory | Reference counting + free lists; bignum `Nat` | Blocks + bump allocation, no RC; fixed-width words |
| Where proofs exist | Kernel checks theorems. **No proof links the compiler (C++/Lean, `partial`, `unsafe`) to the program's meaning.** The compiler is in the trust base | Lexer soundness, parser vs `ParSpec`, ownership ⇒ `Linear`, codegen vs J templates, J runs ⇒ Sail/ARM runs, `CompileCorrect` / `CompileRuns`, compiler compiled by itself (`self_correct_C`). Trust = kernel + ISA model + spec |
| Self-hosting | stage0 C blob checked in, stage1 = stage0 builds source, stage2 = stage1 builds source; CI checks stage1/stage2 agree. Convention, not proof | Same ladder (`B2.bin`), plus a kernel-checked certificate that C's text means C's Lean function; fixpoint is only a test |

Consequence for reuse: **none of Lean's compiler code can be copied** (all `partial`, `CoreM`/`MetaM`, `HashMap`, `panic!`, not in nano's subset, unprovable as is). What transfers is design (blueprints), Lean itself as a test oracle, and a checklist of semantic edge cases.

## 2. Reuse table, ranked

Value = what it buys most. Reuse kind: B = blueprint (copy the design, re-prove our version), O = oracle (differential testing against real Lean), C = copy code. Nothing is C.
Rank is by value per cost, with correctness issues (invariant 1) first.

| # | Idea | Lean location | Kind | Provable here? | Value | Effort | Lands in |
|---|---|---|---|---|---|---|---|
| 1 | Fix the 14 known mismatches where nano accepts and Lean rejects or disagrees (M1 literal arithmetic typed UInt64 vs Lean's Nat; M2 fuel numeral ≥ 2^64; M13 `implemented_by`; M3 `<--`; layout, reserved words, redundant arms, ...) | `Lean/Elab/Extra.lean` (binop%), `Parser/Basic.lean`; see `LEAN_RULES.md` §0 | O (found) + B (rules) | Yes: each is a reject rule or a lexer/parser predicate, with a soundness lemma | correctness (M1, M2, M13 are miscompiles today) | days for M1/M2/M3/M13; 1–2 weeks for layout and namespaces | Lexer, Parser spec, then Ownership/front end |
| 2 | Whole Lean as differential oracle: fuzz nano programs vs `lean`/`#eval`; run the edge list (`n-m` for n<m, `x/0`, `x%0`, UInt wrap, shifts ≥ width, `Int` rounding, 2^63 box limit) | whole tree; edge list in `elab.md` §4, `runtime.md` §3 | O | n/a (testing); aligns with invariant 1 | correctness | small, ongoing; harness exists in `Testing/nano/v2self/fuzz/lean_rules/` | Tests, every stage |
| 3 | Bootstrap hygiene: require stage2 == stage1 (not just stage1 runs); dedicated commits for `B2.bin`/Cert changes; one update script | `doc/dev/bootstrap.md:35-107` | B | Process only (nano's Cert is stronger than Lean's) | correctness / trust | hours | SelfHost, Main |
| 4 | IR with `let / cases / jp / jmp / ret` + big-step semantics + total well-formedness checker with a progress lemma | `LCNF/Basic.lean:371`, `IR/Checker.lean` | B | Yes, total and first-order | coverage (the base for every later pass) | 1–2 weeks | new middle stage between Parser and J |
| 5 | Front-end rewrites that erase Lean's surface: `Decidable`→`Bool`, `Nat` literal/`n+k` patterns → `zero/succ`, trivial-structure unwrapping, Nat `cases` → `decEq`/`sub` | `LCNF/ToLCNF`, `ToMono`, `Match` | B | Yes: each is a small local equivalence | coverage | days to a week each once IR semantics exist | front end |
| 6 | Match compilation as a total function (vars × alts, Maranget style) with exhaustiveness and redundancy from leaves | `Elab/Match.lean` (1300 lines, tactic-based: no copy) | B | Yes for ADT + Nat/Bool/literal patterns, fuel-bounded | coverage + correctness (fixes M11) | 2–4 weeks | Parser/front end |
| 7 | Structural-recursion check (call argument is a strict pattern-bound subterm); explicit `termination_by`; else fuel (already the owner's pattern). Do not copy `guessLex` | `Elab/PreDefinition/Structural` | B | Yes, measure = ADT size | coverage | 1–2 weeks | front end |
| 8 | `UIntN` / small-`Nat` op semantics as property tests + proofs (mod 2^N, `/0=0`, `%0=a`, shifts mod N; RISC-V `divu` by 0 gives all-ones, so emit a zero check; ARM `udiv` by 0 gives 0) | `lean.h:2038-2200` | B + O | Yes, bit lemmas against Sail | coverage | days per op | J templates, both backends |
| 9 | Constant folding table (~100 identities: neutral, annihilator, 2^k shifts, relations) | `LCNF/ConstantFold.lean` | B + O | Yes, one lemma per rule, easiest proof win | speed | 1–2 weeks | new pass on IR |
| 10 | Simp = inlining + case-of-known-constructor + dead-let removal, with ONE substitution/inlining lemma reused by all later passes | `LCNF/Simp/*` | B | Yes, 1–3 weeks to get the core lemma right | speed (largest after specialisation) | 3–5 weeks | IR pass |
| 11 | Specialisation of fixed arguments (monomorphic loops instead of dictionary/closure calls) | `LCNF/Specialize`, `FixedParams` | B | Yes if the subset has no runtime type classes: inline fixed args + cache | speed (biggest in idiomatic Lean) | 3–6 weeks | IR pass |
| 12 | Join points instead of closures for control flow; jp arity reduction; ReduceArity | `LCNF/JoinPoints`, `ReduceArity` | B | Yes | speed (fewer spills) | 1–2 weeks each | IR pass |
| 13 | Bignum `Nat`: add/sub/compare/schoolbook mul on 32-bit limbs; shift-subtract division instead of Knuth D; keep the "≤ 2^63−1 is always small" normal form | `runtime/mpn.cpp` (356 lines), `lean.h` | B + O | Yes, `toNat` correctness; division is the hard part | coverage (ROADMAP: big numbers) | add/sub 1–2 wks, mul 1 wk, div 2–4 wks | new runtime library written in nano |
| 14 | Packed arrays / `ByteArray` / `String` as UTF-8 with the logical-model spec; reproduce edge table (`get!` OOB, invalid positions, `extract`) as tests | `runtime/object.cpp`, `String` section of `runtime.md` | B + O | Yes: rep invariant buffer = model list; UTF-8 round-trip lemmas | coverage | 2–4 weeks arrays; 1–2 weeks String | runtime library, Ownership |
| 15 | ExplicitRC (inc/dec) on λRC, then borrow inference, then reset/reuse | `LCNF/ExplicitRC`, `Borrow`, `ResetReuse` (impure phase in 4.34.1) | B (idea only) | Possible, research-grade; months. Nano's `Linear` check already covers the in-place-update half | speed / memory recycling | months | only if heap values outlive linear use |
| 16 | Closures / `apply` / `_boxed` wrappers; lambda lifting | `runtime/apply.cpp`, `LCNF/LambdaLifting` | B | Yes, medium | coverage (only if higher-order values enter the subset) | 2–4 weeks | defer |
| 17 | CSE, FloatLetIn, ElimDeadBranches (abstract interpretation), ExtractClosed | `LCNF/CSE` etc. | B | CSE small; ElimDeadBranches heavy; ExtractClosed has no home without static init | speed, low | CSE days; others skip | skip for now |

Rows I'd drop outright: copying `stage0` C, `native_decide`/`reduceBool`, GMP, Lean's C++ interpreter as anything but an oracle.

## 3. Top 5 recommendations, in order

1. **Close the miscompiles (row 1, M1, M2, M13, M3).** Cheapest and the only item where nano currently violates invariant 1. M1 means `if 3 - 4 == 0 then 1 else 2` yields `2` in nano and `1` in Lean. Simplest sound rule from `LEAN_RULES.md`: reject numeral-only arithmetic in conditions, `let` values and scrutinees; reject numerals ≥ 2^64; reject `implemented_by`. Cost: each fix changes lexer/parser specs, which means re-proving those stages and regenerating Cert/SrcLink. Not free, but days, not weeks.
2. **Make the differential fuzzer a standing gate (row 2).** It found the 14 mismatches without touching proofs. Add the runtime edge list from `runtime.md` (truncated sub, `/0`, `%0`, shift ≥ width, 2^63 boundary) before the corresponding features land. Cost: ongoing, low; the limit is that it samples and cannot prove agreement.
3. **Add a λ-style IR with semantics and checker (row 4), then the erasing rewrites (row 5).** This is the prerequisite for every optimisation and for supporting more of Lean. Nano today goes AST → J with no middle language. Cost: 2–4 weeks before any visible speedup; the first payoff is coverage, not speed.
4. **Constant folding, then simp with one inlining lemma (rows 9, 10).** ROADMAP says "features before speed, up to ~10x gcc -O2 is acceptable", so this is not urgent, but folding is the easiest proofs available and the inlining lemma is reused by specialisation (row 11) and join points (row 12). Cost: 1–2 weeks and 3–5 weeks; real speed gains likely only with specialisation, which is only worth it once the subset has higher-order or class-polymorphic code.
5. **Runtime library in nano, in this order: UIntN/small-Nat semantics (row 8), arrays and String (row 14), bignum (row 13).** These are what the ROADMAP's targets (CRC-32, SHA-256, big-number add/mul, UTF-8 validation, con-leche) need. Use `lean.h` and `mpn.cpp` as spec and oracle, not code. Cost: weeks each; bignum division is the largest single proof, so use shift-subtract unless speed demands Knuth D.

Deliberately not recommended now: RC / reset-reuse (row 15) because nano's bump allocator plus the `Linear` check already gives in-place updates for arrays, and a proved RC pass is months of work for a problem nano does not yet have; and anything from the elaborator beyond the fixed rules above, because instance search and `isDefEq` are neither provable nor self-hostable, so nano's safest strategy is a restrictive subset (annotated or `Nat` literals, same-type arithmetic, plain ADTs, structural recursion) plus fuzzing wherever it is more liberal.

## Open items

- Readers did not run Lean for the tour notes; IR/LCNF examples and line numbers are from reading. Verify with `set_option trace.Compiler.result true` before relying on shapes.
- Not read in depth: `mod64` of big values, string growth policy, old-compiler remnants.
- `Int` small range is 32-bit in Lean's runtime; irrelevant until `Int` enters the subset.
