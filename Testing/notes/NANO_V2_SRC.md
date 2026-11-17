# NANO_V2_SRC: the nano compiler's stages in the restricted (nano v2) style

Branch `nano-v2-src`. Goal (ROADMAP "DIRECTION"): nano compiles itself. This branch writes the five stages of
`Nano.selfHosted` (lexA, 2b, inliner, expander, assembler) as byte machines in the constructs the grown nano language
(branch `nano-v2`, Testing/notes/NANO_V2.md) is to accept, and proves each equal to the current stage.

## Status

| stage | current definition | v2 source | bridge (no sorry, axioms propext/Classical.choice/Quot.sound) | status |
|---|---|---|---|---|
| assembler | `Nano.asm` (Nano/Asm.lean) | `Nano.V2S.asmV` (Nano/V2S/Asm.lean) | `Nano.V2S.asmV_eq : xs.length < 2^32 → asmV xs = asm xs` | DONE |
| expander | `Nano.mexp` (Nano/Expand.lean) | `Nano.V2S.mexpV` (Nano/V2S/Expand.lean) | `Nano.V2S.mexpV_eq : xs.length < 2^32 → mexpV xs = mexp xs` | DONE |
| inliner | `Nano.U.inlB` (Nano/SerU.lean) | `Nano.V2S.inlV` (Nano/V2S/Inl.lean) | `Nano.V2S.InlP.inlV_eq : xs.length < 2^32 → inlV xs = inlB xs` (Nano/V2S/InlProof.lean) | DONE |
| lexA (lexer + 2a) | `Nano.LS.lexA` (Nano/LexS3.lean) | — | — | design below; feasible in the construct set (two passes) |
| parser 2b | `Nano.PS.stage2b` (Nano/ParseS3B.lean) | — | — | BLOCKED on one extra construct (word memory), see below |

Every bridge holds for every input of length < 2^32 (positions are UInt64 words; the self-hosting domain bounds every
intermediate by 2^20, so the hypothesis is implied there). Build: `lake build Nano.V2S.InlProof Nano.V2S.Expand` (all
three files < 10 s each).

## The constructs actually used (the nano-v2 language must support exactly these)

Prelude (Nano/V2S/Prelude.lean), real Lean definitions:
- `rd (xs : List UInt8) (i : UInt64) : UInt64` — input byte `i`, 0 past the end;
- `len (xs : List UInt8) : UInt64` — input length;
- `put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]` — append one output byte.
The input `xs` is passed unchanged; the output `o` is threaded linearly (never used after being passed on), so it
compiles to a buffer pointer + length register.

Function shapes:
- fuel-recursive: `def f : Nat → List UInt8 → UInt64 → … → R | 0, … => base | n + 1, … => body`; every self call
  passes `n`. `R` is `UInt64` or `List UInt8` (the output). Self calls are tail calls except in `inlBody`, where the
  result of one self call is the output argument of another (`f n xs j (p+2) hi (f n xs t s h o)`).
- non-recursive helpers `def g (a b : UInt64) : UInt64` and `def g (o : List UInt8) (a b : UInt64) : List UInt8`.
- the entry `def stageV (xs : List UInt8) : List UInt8 := …`, which computes initial fuels from `xs.length` (Nat `+`,
  `*`: `xs.length + 1`, `n * n`, literal 256) and calls the loops with `[]` as the initial output.

Expressions (UInt64 only): literals; `+ - *`; `&&& ||| <<< >>>` with literal shift amounts < 64; `let x := e; b`;
`if c then a else b` where `c` is built from `==`, `<`, `≤` on UInt64 and `||` (asm uses `||` in conditions);
calls. No `/`, `%`, no Bool values outside `if` conditions, no structures, lists, Option, pattern matching other than
the fuel `0 / n + 1`.

Used per stage: asm: `&&& ||| <<< >>> == ≤ ||`, `+`; mexp: `== ≤ +`; inliner: `+ - * == < ≤`, the nested self call.

## Design of each stage

- asm: loop over 4-byte records at position `i`; per record four helper functions `ax0..ax3 op a b c` compute the
  output bytes in UInt64 (the low 8 bits are `X0..X3`; lemmas `beq8`, `shr8`, `lt8` move the conditions and shifts
  from UInt8 to UInt64).
- mexp: loop over 2-byte micro-ops; `mexpOp m x o` appends the records (an if-chain of `put`s, generated from the
  arms of `mexp`).
- inliner: no table. The inlined body of def `t` is recomputed from the input whenever `t` is called:
  `startOf` (position after the `t`-th `13` record), `hiAt` (the high-byte register at a position: the last `14`
  record before it), `inlBody f xs j p hi o` walks def `j`'s records from `p`, appending ordinary records, following
  `14`, and for `15 x` with callee `t = hi*256+x < j` calling itself on def `t` (nested), until the `13` record.
  Fuel `(len+1)^2`: fuel is passed by value, so it bounds the longest call chain, at most `len+1` loop steps per
  nesting level and at most `len/2` levels (the work itself can be exponential, as `inlB`'s output). The entry
  counts the `13` records (`cnt13`), emits `wrap k last` (`putPro` for `serPro k`, `putWr` for `sWr`).
  Proof (Nano/V2S/InlProof.lean): list-level meanings `c13`, `so` (offset after the `t`-th `13`), `hiS`, `segG` (one
  def's code); `inlBody_eq : inlBody … = segG …` given the table entries so far (`BP`); `inl_main`: the state of
  `inlGo` at the start of def `t`, by induction on `t` (`inlGo_seg` jumps one def).

## lexA (next): design

`lexA xs = encT (lexTS xs)`: `[]` unless `adjOk xs`, `lexS xs.length xs = some ts` and the type code of `ts` is 1 or 2;
then `code :: encToks ts`. The first output byte depends on all tokens, so two passes, both scalar loops over the input
position with the SAME fuel discipline as `lexS` (one fuel unit per token, the word span bounded by the fuel too, so
the bridge is a step-by-step simulation, no fuel-independence lemma): pass 1 returns 4 on failure or the `uniC` code;
pass 2 appends `encToks ts`. Words are ranges `[p, e)` of the input; `wordTokS` becomes range predicates (first byte,
all digits, the four keywords by length + bytes, identifier check) and `numW` a range loop. Constructs: the same set.

## Parser 2b: the extra construct needed

`stage2b` is the parser machine `runS` on a state with lists: the scope `sc` (name, depth), the def table `ds`
(name, arity, index), the continuation stack `K` (frames with ≤ 3 fields). Names are ranges of the input (compare by
re-reading). With only scalars, input reads and output appends this machine cannot be simulated; a different
memoryless algorithm (recursive descent + rescanning) would need a new proof against `runS` on every input, including
gas exhaustion and every failure path — out of reach. Smallest extra construct: ONE threaded word array
`mem : Array UInt64` (or `List UInt64`) with `mget mem i : UInt64` and `mset mem i v`, linear like the output,
allocated once with a size from the input length (the stacks `sc`, `K` and the table `ds` are regions of it). Sent to
the nano-v2 box (session_01MfKuVaecMPtighd5kbQ58u) at the start of the round.

## Coordination

nano-v2 box: session_01MfKuVaecMPtighd5kbQ58u, branch `nano-v2`. Messages sent: (1) hello + proposed construct set;
(2) the exact style above + the memory request for 2b.
