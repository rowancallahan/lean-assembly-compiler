# NANO V2: a reader's guide to the trusted definitions

For a reader who knows Lean 4 but has not seen this code. It covers only what the final theorem's STATEMENT
depends on, in the order: theorems, meaning of a text, lexer spec, parser spec, semantics. Written by reading the
sources at commit 16f4c52 (branch `nano-v2-src`); nothing was rebuilt for this note. Line numbers are for that commit.
Paths are from the repository root. `[UNSURE]` marks what I did not verify. The companion file with the `#check`
list is `Nano/Main/REVIEW.lean`; its notes are `Testing/notes/NANO_V2_REVIEW.md`.

Reading order for a review: `Spec/Top.lean` (94 lines), `Spec/Alloc.lean` (150), `Proof/Lex/Lex2Spec.lean` (69),
`Proof/Parser/ParSpec.lean` (lines 1–455), `Proof/Main/Sem.lean` (lines 1–136), `Proof/Main/MainTop.lean`
(lines 42–105). About 1000 lines. Everything else is proof.

---------------------------------------------------------------------------------------------------------------------

## 1. The final theorems

### 1.1 `NanoMain.C_correctLO` — `Nano/Main/ParCapBnd.lean:118`

```lean
theorem C_correctLO : CompileCorrect riscv compileC
```

No hypotheses. Unfolded, in words: take any source text `s`, any types `α β`, any `f : α → β`, any byte encodings
`encodeInput : α → List UInt8`, `encodeOutput : β → List UInt8`, any `argument : α`, any Sail RV64 state and any
`call`. IF

1. `compileC s = some compiled` (C's driver emitted non-empty code and the text is ≤ 2^20 bytes; §2.4),
2. `Computes s f encodeInput encodeOutput` (the text's meaning agrees with `f` on EVERY `a : α`; §1.3),
3. `StartCorrect riscv startState call compiled.code (encodeInput argument)` (the calling convention; §1.4),
4. the expected output fits in the output block,
5. `memoryNeeded compiled (encodeInput argument) ≤ call.workLength`,

THEN some state `finishState` is reachable by machine steps with: PC = return address; status register (a0) ≠ −1;
the output block starts with `encodeOutput (f argument)`; a1 = that length; memory unchanged outside the result
prefix of the output block and the work block; callee-saved registers unchanged; machine still configured.

Surprising / worth knowing:
- **You supply hypothesis 2.** The theorem links "meaning of the text" (`srcRun`, §2) to machine code. It does not say
  the text means what real Lean would compute from the same characters. `Sem` (§5) IS the definition of meaning. The
  one place a text is tied to a Lean function is the certificate `Cert.sem_C` for C's own source (§1.6).
- **`Computes` is for every `a : α`**, including ones whose encoding is longer than 2^20 bytes or that hit the buffer
  capacity (§5.4). To exclude them, pick `α` as a subtype, as `SelfIn` does (§1.6).
- **No completeness.** Nothing here says `compileC` succeeds on any text. A compiler that always returned `none` would
  satisfy `CompileCorrect`. Which texts are accepted is decided by C's code (`mC`), not by a spec. In particular a
  text can lex and parse (§3, §4) and still be refused, e.g. by C's ownership check (`LinearK`,
  `Proof/Main/Sem.lean:144`).
- `∃ finishState, Runs …` says the return state is reached. `Runs` is "zero or more steps" of a deterministic
  `step : State → Option State`, so there is exactly one run; it does not say the machine stops there.
- Axioms (from `NANO_V2_REVIEW.md` §4, not re-run by me): `propext`, `Classical.choice`, `Quot.sound`, and the opaque
  declarations of the Sail model (reservations, random bits, terminal write, softfloat). No `sorryAx`.

### 1.2 `CompileCorrect` / `CompileRuns` — `Spec/Alloc.lean:130` / `:112`

Both are `Prop`s about a `machine : Machine` and a `compile : P → Option CompiledA`, for any `P` with a `Program`
instance. Same first four hypotheses as above.
- `CompileCorrect` (line 130): adds hypothesis 5 (enough memory) and concludes the eight facts listed in §1.1.
- `CompileRuns` (line 112): NO memory hypothesis. Concludes: returns to the caller; memory changed only in the
  result prefix of the output block and the work block; status register = `oomFlag` **iff**
  `workLength < memoryNeeded`; kept registers; configured. It says nothing about the output contents.
- Proved for C as `NanoMain.C_runsO : CompileRuns riscv compileC` (`Proof/Main/RunsTopO.lean:13`).

Supporting definitions in `Spec/Alloc.lean`:

| name | line | summary |
|---|---|---|
| `CompiledA` | 47 | code bytes, a cell size, and `events : input → List MemEvent` |
| `MemEvent`, `inUse`, `peak` | 21, 26, 32 | alloc/free events (newest first), cells in use, the maximum |
| `memoryNeeded` | 53 | `cellSize * peak (events input)` |
| `oomFlag` | 57 | `0xFFFFFFFFFFFFFFFF` (−1) |
| `OutOfMemory` | 60 | `workLength < memoryNeeded compiled input` |
| `KeptRegisters` | 108 | every register in `mapping.kept` has its start value |
| `AllocSpec`, `Inside` | 42, 37 | NOT used by either statement |

Surprising:
- The header talks of an "allocator specification" and "memory events of the abstract run". For C this is a
  formality: `compileC` reports the single event `[.alloc (spaceC text inp)]` with `cellSize = 1`, so
  `memoryNeeded = spaceC text inp` (`peak [.alloc n] = n`). See §2.3 for what `spaceC` is.
- Truncated subtraction in `inUse` (`free` more than in use gives 0). Irrelevant for C (no `free` events).
- In `CompileCorrect`, `memoryNeeded` is only a hypothesis: a too-large value weakens the theorem, it cannot make
  it false. In `CompileRuns` its exact value matters (the `iff`).
- The length register holds `length.toUInt64` (mod 2^64; harmless, the block is inside 2 GiB of RAM).

### 1.3 `Program` / `Computes` — `Spec/Top.lean:29` / `:32`

```lean
class Program (P : Type) where run : P → List UInt8 → Option (List UInt8)
def Computes program f encodeInput encodeOutput : Prop :=
  ∀ argument, Program.run program (encodeInput argument) = some (encodeOutput (f argument))
```

A source program is anything with a partial bytes-to-bytes `run`. `Computes` says `run` is defined on, and agrees
with `f` on, every encoded argument. For C, `P = SrcC` and `run = srcRun` (§2). `f`, the encodings and the types are
the caller's choice; with `α = β = List UInt8` and identity encodings it reads "`srcRun s = some ∘ f`".

### 1.4 `StartCorrect` — `Spec/Top.lean:70`

The 19 hypotheses on the start state. In plain terms, with the RISC-V mapping (`Spec/Machines.lean:18`):

- machine `configured` (`Cfg`, `Spec/Riscv.lean`: M-mode, fixed CSR values);
- code bytes are in memory at the PC; PC and return address are multiples of 4; the return address is not inside
  the code;
- input bytes are in memory at `inputAddress`; `call.inputLength = input.length`; **`input.length ≤ 2^20`**;
- registers: `ra` (x1) = return address, `a0` (x10) = input address, `a1` (x11) = input length, `a2` (x12) = work
  address, `sp` (x2) = work address + work length, `a3` (x13) = output address;
- the work address is a multiple of 8;
- the four blocks (input, output, work, code) lie in RAM (`0x80000000 ≤ … ≤ 0x100000000`,
  `Spec/RiscvMachine.lean:36`) and are pairwise `Apart`;
- every byte of the output and work blocks exists (`Present`).

Related: `Machine` (:13), `MachineState` (:7), `Runs` (:23), `Call` (:41), `readMemory` (:50), `Apart` (:57),
`Outside` (:61).

Surprising:
- `a0` is both the input-address register on entry and the status register on exit; `a1` is input length on entry
  and output length on exit.
- The 2^20 input limit is in the calling convention, not in `Computes`.
- `readMemory` adds `offset.toUInt64` with wrap-around; `Apart`/`Outside` use `Nat` arithmetic. The `inRam`
  hypothesis keeps blocks below 2^32, so the two views agree.
- `Compiled` (:37) with `space : Nat → Nat` is an older structure; C uses `CompiledA`.

### 1.5 `riscv` — `Spec/RiscvMachine.lean:36`

The Sail RV64 model wrapped as a `Machine`: `step` = one retired instruction of hart 0 (`riscvStep`, :31), else
`none`. Not reviewed here; see `NANO_V2_REVIEW.md`.

### 1.6 The self-compilation theorems (REVIEW.lean §2, §2b)

- `Cert.sem_C` (`Proof/Cert/All.lean:288`): for inputs shorter than 2^64 bytes,
  `Ref (Sem κC PC.all inp) (Sh.mLean inp)`, where `Ref r v := r = .error .cap ∨ r = .ok v`
  (`Proof/Cert/Rules.lean:12`). So: the AST `PC.all` either hits the capacity or returns what the Lean function
  returns. Note the disjunction: the capacity case is allowed on any input.
- `self_meaning_C` (`Proof/Main/SelfC.lean:20`): for C's own source text `SrcGen.X0`, `srcRun` is `some (mC inp)` or
  (capacity) `none`.
- `SelfIn` (`Proof/Main/SelfLink.lean:28`): inputs shorter than 2^64 bytes on which `Sem κC Cert.PC.all` is not
  `.error .cap`. A subtype defined by the semantics itself; which inputs are in it is not characterised.
- `self_correct_C` (`SelfC.lean:35`): `C_correctLO` specialised to the text `X0` and `f = mC`. It KEEPS the
  hypothesis `compileC ⟨X0⟩ = some compiled` (per REVIEW.lean: true iff `mC X0 ≠ []`, shown only by running the
  binary, not proved), and does not say that any shipped binary equals `compiled.code`.

---------------------------------------------------------------------------------------------------------------------

## 2. The meaning of a source text — `Nano/Main/MainTop.lean`

Pipeline: bytes —`LexSpec.Lexes`→ token words —`ParSpec.refParse`→ `List DefA` —`Sem κC`→ output bytes.

### 2.1 `SrcC` (:43), `pOf` (:48)

```lean
structure SrcC where text : List UInt8
noncomputable def pOf (x : List UInt8) : Option (List DefA) :=
  if h : ∃ p, ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts p then some (Classical.choose h) else none
```

`pOf x` is the program the text denotes, or `none` if the text does not lex or does not parse.

Surprising: it uses `Classical.choose`, which normally means "some unspecified witness". Here the witness is
unique: `lexes_det` (:30) shows the token list is unique, and `ParsesProgram` is `refParse ts = some p` with
`refParse` a function. `pOf_eq` (:51) states the consequence: `Lexes x ts → ParsesProgram ts p → pOf x = some p`.
So `pOf` is a function in disguise; the choice is a way to avoid writing a lexer function for the relation `Lexes`.

### 2.2 `srcRun` (:60) and the `Program SrcC` instance (:63)

```lean
noncomputable def srcRun (s : SrcC) (inp : List UInt8) : Option (List UInt8) :=
  (pOf s.text).bind fun p => (Sem κC p inp).toOption
```

The meaning of a text on an input: `none` if the text is not a program; otherwise run `Sem` with capacity
`κC = 524288` and turn `.error _` into `none`.

Surprising:
- `.error .cap` (a buffer reached 524288 elements) becomes `none`. So a program has NO meaning on such inputs,
  and `Computes` fails if any `encodeInput a` is one of them.
- `.error .stuck` also becomes `none`, but never happens for a parsed program (`parsed_not_stuck`,
  `Proof/Parser/MainTyP.lean:839`).
- `Sem` is a total Lean function (fuel loops only), so nano programs always terminate. There is no divergence
  case to model.

### 2.3 `spaceC` (:92)

```lean
noncomputable def spaceC (x : List UInt8) : List UInt8 → Nat :=
  match pOf x with | some p => fun inp => max 16 (Msp p inp) | none => fun _ => 0
```

The work memory, in bytes, that C's code for text `x` needs on input `inp`. `Msp` (`Proof/Machine/RunsDef.lean:48`)
is `16 + thr p inp` rounded up to a multiple of 8; `thr` (:45) is the least `u ≤ 2^32` such that `GoodU p x u`
(:41): at every 8-aligned work base `hb ≥ 2^31` with `hb + u ≤ 2^32`, the run model `RS p x T hb u` is not
`.error .room`.

Surprising:
- This is NOT a source-level quantity. It is defined through `RS`, a lower-level model of the generated code's
  run [UNSURE: I did not read `RS`]. To know the number for a given program you rely on the bounds
  `Msp_le` (`RunsDef.lean:104`) and `spaceC_le` (`Proof/Machine/RunsThr.lean:88`), or on a computed instance such as
  `AuditSpace.spaceC_ex1_eq`.
- Noncomputable: `lfind` branches on an undecided `Prop` using `open Classical`.
- If no `u ≤ 2^32` is good, `thr = 2^32` and hypothesis 5 of §1.1 cannot be met inside the 2 GiB of RAM; the
  theorem is then vacuous for that program and input.

### 2.4 `compileC` (:103), `mC` (`Proof/Main/Sem.lean:18`)

```lean
def mC (x : List UInt8) : List UInt8 := C.g41 x (C.o41 (C.y16 (C.s10 x)))
noncomputable def compileC (s : SrcC) : Option CompiledA :=
  if mC s.text ≠ [] ∧ s.text.length ≤ 2 ^ 20 then some ⟨mC s.text, 1, fun inp => [.alloc (spaceC s.text inp)]⟩
  else none
```

`mC` is the compiler: lexer `s10`, parser `y16`, ownership check `o41`, code generator `g41` (all in
`Nano/V2Self/C/`). Empty output means "rejected". `compileC` packages it for `CompileCorrect`.

Surprising:
- `mC` is a definition, not part of the trusted base in the usual sense: the theorem is ABOUT it. What you trust is
  that `mC` is the function you actually ran. Its comment says it is copied from a Python build script
  (`Testing/nano/v2self/build_self_S.py`), not generated.
- `compileC` is noncomputable only because of `spaceC`; the code field is the computable `mC s.text`.
- The 2^20-byte limit on the TEXT is here; the 2^20-byte limit on the INPUT is in `StartCorrect`.

---------------------------------------------------------------------------------------------------------------------

## 3. The lexer spec — `Nano/Lexer/Lex2Spec.lean`

### 3.1 Definitions

| name | line | summary |
|---|---|---|
| `isW` | 10 | word byte: `A–Z a–z 0–9 _ '` |
| `isD` | 12 | digit byte |
| `opTable` | 15 | 21 operators as (bytes, tag), longest first |
| `kwTable` | 22 | 19 keywords/prims as (bytes, tag) |
| `numVal` | 44 | decimal value **mod 2^64** |
| `le8` | 46 | 8 little-endian bytes of a number, each as a `UInt64` |
| `step` | 49 | one token: `some (emitted words, rest)` or `none` |
| `Lexes` | 65 | the relation: repeat `step` until the input is empty |

`step` on a non-empty input, first match wins:
1. space (32) or newline (10): emit nothing, drop the byte.
2. the first `opTable` entry that is a prefix of the input: emit its tag, drop its bytes.
3. otherwise take `w` = the longest prefix of word bytes:
   - first byte a digit: if all of `w` is digits, emit `5` then `le8 (numVal w)` (9 words); else fail;
   - first byte another word byte: if `w` is in `kwTable` emit its tag (1 word); else emit an identifier:
     `14`, then `1, b` for each byte `b`, then `0`;
   - anything else: fail.

`Lexes x ts` holds iff applying `step` repeatedly consumes all of `x` and the emitted words concatenate to `ts`. It
is a relation, but deterministic (`lexes_det`, `MainTop.lean:30`). `Lexes [] []` holds.

Token tags (a "token word" is a `UInt64`):

| tag | text | tag | text | tag | text |
|---|---|---|---|---|---|
| 1 | `def` | 16 | `×` (C3 97) | 34 | `else` |
| 2 | `let` | 17 | `→` (E2 86 92) | 35 | `Nat` |
| 3 | `UInt64` | 18 | `\|` | 36 | `Buf` |
| 5 | number (+8 words) | 19 | `=>` | 37 | `List` |
| 6 | `(` | 20 | `<` | 38 | `UInt8` |
| 7 | `)` | 23 | `==` | 39 | `len'` |
| 8 | `:` | 26 | `&&&` | 40 | `rd` |
| 9 | `:=` | 27 | `\|\|\|` | 41 | `len` |
| 10 | `+` | 28 | `<<<` | 42 | `put` |
| 11 | `-` | 29 | `>>>` | 43 | `bnew` |
| 12 | `*` | 30 | `[` | 44 | `bsize` |
| 13 | `;` | 31 | `]` | 45 | `bget` |
| 14 | identifier (`(1,b)* 0`) | 32 | `if` | 46 | `bset` |
| 15 | `,` | 33 | `then` | 47 | `bpush` |

Tags 4, 21, 22, 24, 25 are never emitted by this spec.

Surprising:
- **Numerals wrap**: `18446744073709551617` lexes as the number 1.
- **No comments, no tabs, no carriage returns.** `--` lexes as two `-` tokens (and then fails to parse). Byte 9 or
  13 makes `step` fail, so a file with Windows line endings is not a program.
- `=`, `>`, `.`, `{`, `≤`, `≠`, `^`, `/`, `%`, `!` and every other byte not listed: no `step`, the text has no
  meaning. (`^^^` is not lexable even though `Sem.binop` has an xor case, §5.)
- Keywords match whole words only (`define` is an identifier; `len'` and `len` are different keywords).
- A digit-led word with a letter (`3x`) is rejected rather than split.
- Identifiers may start with `_` or `'` and are byte strings; non-ASCII identifiers are impossible.
- Keywords are reserved by the lexer; whether `put` etc. can be re-bound is settled by the parser (they cannot:
  they are never `Tok.id`).
- Newlines are plain whitespace. Layout carries no meaning anywhere in nano.

### 3.2 Worked example A: `a+1` (bytes `[97, 43, 49]`)

1. `step [97,43,49]`: 97 is not whitespace; no operator is a prefix; `w = [97]` (43 is not a word byte); 97 is not
   a digit; `[97]` is not a keyword → emit `[14, 1, 97, 0]`, rest `[43, 49]`.
2. `step [43,49]`: `+` is in `opTable` → emit `[10]`, rest `[49]`.
3. `step [49]`: `w = [49]`, all digits, `numVal = 1` → emit `[5, 1,0,0,0,0,0,0,0]`, rest `[]`.

Result: `Lexes "a+1" [14,1,97,0, 10, 5,1,0,0,0,0,0,0,0,0]`.

### 3.3 Worked example B: `let x := 300;`

| input piece | rule | emitted |
|---|---|---|
| `let` | keyword | `2` |
| space | whitespace | (nothing) |
| `x` | identifier | `14, 1, 120, 0` |
| space | whitespace | |
| `:=` | operator (`:=` is listed before `:`) | `9` |
| space | whitespace | |
| `300` | number, 300 = 44 + 1·256 | `5, 44, 1, 0, 0, 0, 0, 0, 0` |
| `;` | operator | `13` |

Result: `[2, 14,1,120,0, 9, 5,44,1,0,0,0,0,0,0, 13]`.

Counter-examples: `3x` (digit-led word with a letter), `a = b` (bare `=`), `a\tb` (tab): `step` is `none` at
that point, so no `ts` satisfies `Lexes`.

---------------------------------------------------------------------------------------------------------------------

## 4. The parser spec — `Nano/Parser/ParSpec.lean`

`ParsesProgram ts p` (:455) is just `refParse ts = some p`. `refParse` (:447) is an executable recursive-descent
parser written to be read as the grammar. It also does name resolution, type checking and slot assignment, so its
output is a resolved AST with no names left.

### 4.1 Token decoding

| name | line | summary |
|---|---|---|
| `Tok` | 24 | `k tag` / `num value` / `id bytes` |
| `okTag` | 27 | the tags of the table in §3.1 other than 5 and 14 |
| `detokA`, `detok`, `tokens` | 38, 47, 49 | regroup the word stream into `Tok`s |

`5` + 8 words becomes `num (little-endian value)`; `14 (1,b)* 0` becomes `id [b…]`; any other allowed tag `t`
becomes `k t`. Fuel is `ts.length + 1`, enough because each step consumes at least one word.
Surprising: `bytesVal` does not check that the 8 words are bytes (they are, when they come from `Lexes`).

### 4.2 The AST

`DefA` (:306), one per `def`:

| field | meaning |
|---|---|
| `id` | position in the program, from 0 |
| `npw` | parameter words (the input parameter counts 0, the fuel 1, a pair the sum of its parts) |
| `nslots` | total local slots: parameters first, then one fresh group per `let` |
| `kind` | 0 plain def or constant, 1 fuel loop |
| `nres` | result width in words |
| `body` | resolved expression `Nd` |

`Nd` (:77): every value is a flat list of words; a variable is a slot range.

| node | meaning |
|---|---|
| `const v` | the word `v` |
| `loc slot w` | slots `slot … slot+w-1` |
| `bin op a b` | op 1 `+`, 2 `-`, 3 `*`, 4 `&&&`, 5 `\|\|\|`, 6 `<<<`, 7 `>>>` |
| `ite cmp a b t e` | cmp 1: `a == b`; cmp 2: `a < b` (unsigned) |
| `letE slot w v b` | store `v` (width `w`) at `slot`, then `b` |
| `pair cs` | concatenation of the parts' words |
| `call id args` | earlier def number `id`; the input argument is not in `args` |
| `prim p args` | 1 `len'`, 2 `rd`, 3 `len`, 4 `put`, 5 `bnew`/`[]`, 6 `bsize`, 7 `bget`, 8 `bset`, 9 `bpush` |
| `loop z s` | body of a fuel loop: zero arm, step arm |
| `cont e` | "continue the loop with new state `e`" (a tail self-call) |

Types used during parsing (not kept in the AST): `Sh` (:53) shapes `uw` UInt64, `bf` Buf, `ls` List UInt8-as-value,
`nt` Nat, `p a b` pair; `Ps` (:58) parameter kinds `inp` (width 0), `fuel` (width 1), `sh s`; `Ty` (:62)
expression types `s shape`, `lit` (a numeral), `inp`, `bot` (a `cont`).

### 4.3 The grammar accepted

Program: one or more defs, nothing else, the LAST named `m` with exactly `(x : List UInt8) : List UInt8`
(`isMain` :445; any binder name). Def names are unique. A def can call only EARLIER defs.

Plain def (`pDef` :379, second branch): `def f (a b : T) (c : U) : R := e`. Zero binder groups gives a constant.

Fuel loop (`pDef`, first branch; chosen when the text after the name is `: Nat →`):
```
def g : Nat → T1 → … → Tk → R
  | 0, x1, …, xk => Z
  | n + 1, y1, …, yk => S
```
The patterns must be literally `0` and `<name> + 1`; binder names in one arm are distinct.

Types (`pTy` :296): `UInt64`, `Buf`, `Nat`, `List UInt8`, parentheses, `A × B` (right-nested).
- `Nat` is rejected in every parameter, state and result (`hasN`). It can only be the first arrow of a loop.
- The first `List UInt8` parameter that is alone in its binder group is THE INPUT: width 0, no slot contents. Every
  other `List UInt8` is a one-word byte buffer (`pickPs` :341). In a loop, the first `List UInt8` state is the input.

Expressions (`pExpr` :130, `pBin` :166, `pLoop` :177, `pApp` :198, `pAtom` :245):
- `let x := v; b` and `let (a, b) := v; body` (exactly two names; `b` takes the rest of a longer tuple). The `;`
  is mandatory.
- `if A == B then T else E`, `if A < B then T else E`. `A`, `B` are operator expressions of type UInt64. There is
  no Bool type and no other comparison.
- binary operators, left-associative, precedence `|||` 55 < `&&&` 60 < `+ -` 65 < `*` 70 < `<<< >>>` 75 (Lean's
  values). Operands must be UInt64. The right side of a shift must be a numeral token.
- application by juxtaposition: `f a1 … ak`, a prim, or a tail self-call. Each argument is an ATOM, so compound
  arguments need parentheses. Exactly as many arguments as parameters.
- atoms: numeral; `[]` (empty `List UInt8`); `bnew` (empty `Buf`); a variable; the name of a zero-parameter def; a
  parenthesised expression; a tuple `(e1, …, en)` (right-nested pairs).

Rules a Lean reader would not guess:
- **The input is not a value.** It can only be passed along: as the input argument of `rd`/`len`/`len'`, of a call,
  or of a self-call. `put x 1`, `let y := x; …`, and a main body `x` are rejected (`#guard`s at :521–523).
- **The fuel binder is not a value** either (`pAtom`: `some (_, .fuel) => none`). It may only appear as the first
  argument of the tail self-call.
- **Self-calls** are allowed only in the step arm of a loop, only in tail position, only as `g n e1 … ek` with `n`
  the fuel binder; they become `cont`. Tail position passes into `if` branches, a `let` body and parentheses; it is
  lost in conditions, operands, arguments, `let` values and tuple fields. Plain defs cannot recurse at all.
- A loop whose only state is the input cannot continue (rejected, :526).
- Fuel arguments (`tyMatch .fuel`) are a numeral or a `Nat`-typed atom, in practice `(len' x)`.
- Locals shadow defs; the innermost binding wins. Keywords cannot be bound.
- Both branches of an `if` must have the same shape (`Ty.join` :63); a numeral joins with UInt64.

### 4.4 Slots

Parameters take slots `0 … npw-1` in order. Each `let` takes the next free slot(s) AFTER its value has been parsed
and never reuses one; `nslots` is the final counter. In a loop, slot 0 is the fuel, states follow from slot 1.

### 4.5 The width cap (2^20)

`pDef` rejects a def when `2^20 ≤ nslots` or `2^20 ≤ result width` (:410, :431). Reason (comment at :376): pair
doubling such as `let b := (a, a); let c := (b, b); …` makes widths grow exponentially with text length, and the
serializer writes numbers mod 2^64. The check is made once, at the end of each def, on the final counts.
Surprising: this is a limit of the LANGUAGE (such a text has no meaning), not only of the compiler.

### 4.6 Fuel

`refParse` gives the expression parsers fuel `8 * toks.length + 8` and `pDefs` a def count bound
`toks.length + 1`. The mutual functions decrease fuel by one per call, which is what makes Lean accept them.
The header says the bound "is never reached". [UNSURE: I did not find or look for a theorem stating this.]
If it were reached, the effect would be that a text is rejected by the spec. That cannot make `C_correctLO` false
(it is proved against this spec as written); it would only mean the language is smaller than the grammar suggests.

### 4.7 Worked example 1 (`ex1`, :493; checked there by `#guard`)

```
def a (p q : UInt64) : UInt64 := p + q * 3
def m (x : List UInt8) : List UInt8 := put [] (a (rd x 0) 2)
```
Def `a`: `p` is slot 0, `q` slot 1, no lets.
```
{ id := 0, npw := 2, nslots := 2, kind := 0, nres := 1,
  body := bin 1 (loc 0 1) (bin 3 (loc 1 1) (const 3)) }          -- p + (q * 3)
```
Def `m`: `x` is the input, width 0, so `npw = 0` and there are no slots.
```
{ id := 1, npw := 0, nslots := 0, kind := 0, nres := 1,
  body := prim 4 [prim 5 [], call 0 [prim 2 [const 0], const 2]] }
```
`put` is prim 4 with arguments `[]` (prim 5) and the call. `rd x 0` is `prim 2 [const 0]`: the input argument has
been dropped. The file's `#guard` shows the serialized form
`[2, 20,0,2,2,0,1, 3,1,2,0,1,3,3,2,1,1,1,3, 21, 20,1,0,0,0,1, 9,4,9,5,8,0,2,9,2,1,0,1,2, 21]`
(`20 id npw nslots kind nres … 21` per def; I decoded the two ASTs above from it by hand).

### 4.8 Worked example 2 (`ex3`, :506): a fuel loop

```
def g : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, p => p
  | n + 1, x, p => if p < len x then g n x (p + 1) else p
def m (x : List UInt8) : List UInt8 := put [] (g (len' x) x 0)
```
States: `List UInt8` (the input, width 0) and `UInt64`. Fuel is slot 0, `p` is slot 1, so `npw = 2`.
```
{ id := 0, npw := 2, nslots := 2, kind := 1, nres := 1,
  body := loop (loc 1 1)                                           -- zero arm: p
               (ite 2 (loc 1 1) (prim 3 [])                        -- if p < len x
                    (cont (bin 1 (loc 1 1) (const 1)))             --   then continue with p + 1
                    (loc 1 1)) }                                   --   else p
{ id := 1, npw := 0, nslots := 0, kind := 0, nres := 1,
  body := prim 4 [prim 5 [], call 0 [prim 1 [], const 0]] }        -- put [] (g (len' x) x 0)
```
The self-call `g n x (p + 1)` kept only the non-input state: `cont (p + 1)`. The fuel `n` does not appear; the
loop semantics decrements it (§5.3). The call in `m` has two arguments: the fuel `len' x` and `0`.

Rejected variants (all `#guard`ed in the file): `g n p + 1` (self-call not in tail position, :538),
`p + n` (fuel as data, :545), `p <<< q` (shift by a variable, :553), `if p ≤ 1 …` (:561; fails already in the
lexer), a last def not shaped like `m` (:562–563).

---------------------------------------------------------------------------------------------------------------------

## 5. The semantics — `Nano/Main/Sem.lean`

An interpreter over the resolved AST. Environment = a list of slots.

### 5.1 Values

| name | line | summary |
|---|---|---|
| `W` | 24 | a slot value: `.w word` or `.b (List UInt64)` (a buffer) |
| `Stop` | 29 | `cap`: a buffer is full; `stuck`: ill-formed AST |
| `Out` | 33 | `Except Stop (List W ⊕ List W)`: `inl` a value, `inr` a continue payload |
| `Ctx` | 35 | the input bytes, the capacity κ, the meanings of the earlier defs |
| `κC` | 136 | `524288` (2^19) |

Surprising:
- `Buf` and non-input `List UInt8` are the SAME thing here: a list of 64-bit words. `put` pushes the whole word.
  Only at the very end does `Sem` keep each word's low byte. Real Lean's `put` (`Nano/Main/Prelude.lean`) pushes
  `b.toUInt8` at once. The two agree because nano has no way to read a `List UInt8` buffer back (`bget`/`bsize`
  need a `Buf`, `rd`/`len` need the input).
- Buffers are VALUES (immutable lists). `bset` returns a new list. In-place update in the generated code is the
  compiler's business (the ownership check); it is invisible in the meaning.

### 5.2 Primitives and operators

`binop` (:44): `+ - * &&& ||| <<< >>>` on `UInt64`, Lean's own operations (wrap mod 2^64; shifts as Lean's
`UInt64` shifts). Case 8 is xor, unreachable from the parser.

`prim` (:53):

| id | source | result |
|---|---|---|
| 1 | `len' x` | input length as a word |
| 2 | `rd x i` | input byte `i`, **0 if out of range** |
| 3 | `len x` | input length as a word |
| 4 | `put o v` | `o ++ [v]`, or `cap` if `o.length ≥ κ` |
| 5 | `[]`, `bnew` | empty buffer |
| 6 | `bsize b` | length as a word |
| 7 | `bget b i` | element `i`, **0 if out of range** |
| 8 | `bset b i v` | `b.set i v`, **unchanged if out of range** |
| 9 | `bpush b v` | `b ++ [v]`, or `cap` if `b.length ≥ κ` |

`push` (:49) is the only source of `Stop.cap`. Indices use `i.toNat`, no wrap.

### 5.3 Evaluation

- `ev` (:79) / `evL` (:108): evaluate a node / a list of nodes in an environment. `const` gives one word; `loc`
  reads slots; `bin` and `ite` need single words; `letE` writes the value's words to its slots (`setSlots` :41) and
  evaluates the body; `pair` concatenates; `call i` applies the `i`-th earlier def's meaning to the argument words;
  `cont e` returns `inr`.
- `loopRun` (:70): with fuel `n` taken from slot 0 at entry (`n.toNat`):
  fuel 0 → evaluate the zero arm; fuel `n+1` → write `n` into slot 0, evaluate the step arm; a value ends the loop,
  a `cont st` writes `st` into slots 1… and repeats with fuel `n`.
- `defMean` (:114): a def's meaning as a function on argument words: environment = arguments followed by zeros up
  to `nslots`; checks widths.
- `means` (:121): folds `defMean` over the program, each def seeing only the earlier ones.
- `Sem κ p inp` (:127): take the LAST def, apply it to `[]`, expect exactly one buffer, map its words to low bytes.

Surprising:
- `Stop.stuck` covers every shape error (wrong arity, word where a buffer is expected, a `cont` outside a loop…).
  `parsed_not_stuck` (`Proof/Parser/MainTyP.lean:839`) proves it never occurs for `refParse` output.
- `ev` evaluates both comparison operands, and all arguments, left to right. Since the only effect is `cap`, order
  is observable only in which error is reported, and there is only one reachable error.
- `let` slots are not cleared between loop iterations. Not observable: a `let` is always written before it is read.
- Fuel is a 64-bit word. A numeral fuel was already reduced mod 2^64 by the lexer.
- The machine-level behaviour on `cap` (the comment at :27 says the code reports −2) is NOT part of
  `CompileCorrect`: there `Computes` fails, so the theorem is silent. [UNSURE: it is covered by the lower-level
  `compiler_correct'` / `ImplementsC` statements, which I did not read.]

### 5.4 Limits in one place

| limit | where | effect |
|---|---|---|
| text ≤ 2^20 bytes | `compileC` | else not compiled |
| input ≤ 2^20 bytes | `StartCorrect.inputSmall` | else no guarantee |
| slots, result width < 2^20 per def | `ParSpec.pDef` | else not a program |
| every buffer ≤ 524288 elements, so output ≤ 524288 bytes | `Sem.push`, `κC` | else no meaning on that input |
| numerals mod 2^64 | `LexSpec.numVal` | silent wrap |
| work memory ≥ `spaceC` | `CompileCorrect` hypothesis | else the OOM flag (`CompileRuns`) |

### 5.5 Worked example: `ex3` (§4.8) on input `[7, 8]`

`Sem κC p [7,8]`, with `p = [g, m]`.

1. `means` builds `g`'s meaning, then `m`'s (which can call def 0). `Sem` applies `m`'s meaning to `[]`.
2. `m`: environment `[]`. Evaluate `prim 4 [prim 5 [], call 0 [prim 1 [], const 0]]`:
   - `prim 5 []` → `[.b []]`;
   - `prim 1 []` → `[.w 2]` (the input has 2 bytes); `const 0` → `[.w 0]`;
   - `call 0` applies `g` to `[.w 2, .w 0]`.
3. `g`: `npw = nslots = 2`, environment `[.w 2, .w 0]` (slot 0 fuel, slot 1 `p`). `loop` reads fuel 2:
   - fuel 2: slot 0 := 1 → `[.w 1, .w 0]`. Step arm: `0 < 2`, so `cont [.w 1]`; slot 1 := 1 → `[.w 1, .w 1]`.
   - fuel 1: slot 0 := 0 → `[.w 0, .w 1]`. Step arm: `1 < 2`, so `cont [.w 2]` → `[.w 0, .w 2]`.
   - fuel 0: zero arm `loc 1 1` → `[.w 2]`.
   - width 1 = `nres`: result `[.w 2]`.
4. Back in `m`: `prim 4` on `[.b [], .w 2]` → `push κC [] 2` → `[.b [2]]`.
5. `Sem` sees exactly one buffer and returns `.ok [2]`.

So `srcRun ⟨text⟩ [7,8] = some [2]`: one output byte, the input length.

The same program on a 300-byte input returns `[44]`: the loop reaches 300, `put` stores the word 300, and the
final step keeps the low byte (300 mod 256). On an input longer than 2^20 bytes `Sem` is still defined, but
`StartCorrect` no longer applies.

A second, shorter one: `ex1` (§4.7) on `[5]`: `rd x 0 = 5`, `a 5 2 = 5 + 2 * 3 = 11`, output `[11]`. On the empty
input `rd x 0 = 0`, output `[6]`: reading past the end is not an error.

---------------------------------------------------------------------------------------------------------------------

## 6. Where nano differs from real Lean

The nano sources are also valid Lean (with `Nano/Main/Prelude.lean`), but the theorem's meaning is `Sem`, and
the two are not proved equal in general. Differences I can state from the definitions:

1. **Numerals are 64-bit words.** `let a := 5; …` makes `a` a UInt64 slot (`tyShape .lit = some .uw`). In Lean an
   unannotated `let a := 5` is a `Nat` unless the context forces otherwise [UNSURE about how Lean's elaborator
   resolves each such case], and nano offers no type ascription to say which.
2. **Numerals wrap mod 2^64** at the lexer, including fuel numerals, which are `Nat` in Lean.
3. **`len' x : Nat` is a 64-bit word** used only as fuel. Same value while the input is shorter than 2^64 bytes.
4. **Buffers have capacity 524288**; Lean lists do not. Above it nano has no result (`cap`).
5. **`put` on a `List UInt8`** stores a word and truncates at the end (equivalent, see §5.1).
6. **Syntax is a small subset**: `;` after every `let`, no comments, no tabs, no layout, only `==` and `<`,
   atoms as arguments, no `namespace`, no pattern matching other than the loop form, no recursion other than the
   tail self-call.
7. **Termination**: every nano program terminates by construction; nothing like `partial` exists.

What IS proved about the correspondence: only `Cert.sem_C`, for C's own source, with the capacity escape (§1.6).

## 7. Things I did not check

- `RS` / `GoodU` behind `spaceC` (§2.3).
- That the parser fuel bound is never reached (§4.6).
- `Cfg`, `riscvObserve`, the Sail model (§1.5).
- The axiom list (taken from `NANO_V2_REVIEW.md`; nothing was built for this note).
- That `Spec/Alloc.lean` is covered by `Spec/FROZEN.sha256` (REVIEW.lean line 73 says it was not, as of 3ec5c4e).
