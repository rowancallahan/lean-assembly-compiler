# Nano v2: architecture advice (Astra, relayed by the owner, 2026-11-17 ~17:55) and the decision

DECISION (owner, via Astra): **Option C.** Freeze a target subset. Rewrite the nano compiler in it. Compiler 1
(the existing Lean→S3 front end, compiling the rewritten source as ordinary Lean) produces the bootstrap B₁. Nano's
own SMALL backend is the final destination. Compiling S3's implementation is NOT part of the self-hosting milestone.
Do not build a nano→S3 elaborator for the bootstrap.

First milestone: ONE exact nano-written compiler, for ONE frozen subset, compiling its own source with checked
correctness and B₂ = B₃.

## Fixed-point argument
- s = exact frozen source bytes; C = its pure compilation function (fixed options and serialization);
  B₁ = the compiler-1 build; prove Exec(B₁, x) = C(x).
- B₂ = B₁(s), so C(s) = Ok B₂. Nano front end + codegen correctness on s, plus "Lean meaning of s is C", give B₂ implements C.
- B₃ = B₂(s) = C(s) = B₂.
- Byte equality needs a deterministic byte-producing C: freeze symbol order, padding, entry address, resource settings.
- A rewritten compiler needs a NEW instance of the bootstrap theorem; the existing `Nano.selfHosted` covers v1 only.
- Precedent: CakeML (doi 10.1145/2535838.2535841).

## Minimal construct set (comfortable, not absolute minimum)
- UInt64 (Int64 optional) with explicitly defined comparisons.
- `if`, with both branches of the same type.
- Named, fully applied, first-order calls.
- ONE recognized bounded-recursion pattern. It must be ordinary Lean: a fixed prelude macro, or an exactly specified
  recursive def. Fuel must decrease mathematically, with no wrapping decrement at 0.
- Fixed products/records: construct and project only.
- Byte/word buffers: length, checked read, append; update only where needed. Functional semantics first; mutation only
  with a proved ownership rule.
- Explicit failure: a status field (invalid source, fuel exhausted, capacity exhausted).
- Packing ops: shifts and masks.
- NOT needed: small `match` (use `if` on tags), OS I/O inside the pure compiler (the wrapper is specified separately).
- Suggested state: input, cursor, tokenBuffer, workStack, output, status. Use flat buffers and token tags, not recursive
  ASTs. Do nested parsing with an explicit work stack.
- Fixed capacities with explicit failure are fine, provided they fit self-compilation.
- PITFALL: the existing INLINER eliminates every call, so recursive compiler code must not be recursively inlined.
  Either recognize bounded loops before inlining, or keep direct calls and compile their frames.

## Four workers (FREEZE these first: language, buffer API, stage formats, calling convention, theorem interfaces)
1. Language + front end: grammar, AST, typing, Lean interpretation, elaborator extensions.
2. Small back end: stack instructions, if/loop/call lowering, state layout, buffer primitives; a generic codegen theorem.
3. Input stages: the nano-written lexer + parser, source bytes → an agreed flat intermediate format.
4. Output stages + bootstrap: the nano-written inliner, expander, assembler and driver, the compiler-1 bootstrap, and the
   fixed-point composition.
Rules:
- Shared AST/interface files have ONE owner.
- One module per stage.
- Share a tiny end-to-end example immediately.
- A language addition must name the compiler-source use that needs it.
- Pin one source artifact for the fixed-point run.
- Stages must NOT pick their own subsets.

## "Exact subset of Lean": two obligations
- NanoElab s = Ok p ⇒ s is accepted in a FIXED, CLOSED Lean environment (approved imports, instances, notation).
- Meaning_Nano(p) = Meaning_Lean(s).
Pitfalls:
- literal and arithmetic overloading;
- signed vs unsigned;
- unary minus and precedence;
- Bool vs Prop in `if`;
- shadowing;
- the equations of recursive defs;
- the buffer API (checked/default);
- mutation;
- trailing input.
Practical: a restricted grammar plus a translation to Lean terms, with nano semantics proved equal to those terms. The
textual elaboration correspondence may be TESTED only, and must be stated as tested (owner: acceptable for now).
