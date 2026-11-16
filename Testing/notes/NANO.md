# NANO: UTF-8 source text -> RISC-V, tiny compiler, partly self-hosted (branch `nano-e2e`)

Files: `Nano/Ast.lean` (AST, `den`, `Prog.eval`), `Nano/Elab.lean` (`nanoElab`), `Nano/Asm.lean` (`asm`), `Nano/Gen.lean`
(`genR`, `nanoGenS`, `nanoCompileS`, `depth`), `Nano/AsmSelf.lean` (`asm` compiled by our front end), `Nano/Agree.lean` (generated),
`Testing/nano/*` (tests), `Testing/scripts/axioms_nano-e2e.lean`. Lake lib `Nano` (globs `Nano.+`). Names after the merge with nano-proof:
`nanoGen`/`nanoCompile` = the proved IR-based generator (`Nano/GenIr.lean`, nano-proof); `nanoGenS`/`nanoCompileS` = the stack generator here.

## Language (the DRAFT spec; the owner writes the final one)
`def f (x y : UInt64) : UInt64 := e` lines, or the same with `Int64` (one type for the whole file). `nanoElab` (text -> `Prog`) and `Prog.eval`
are the draft spec; everything below is what `nanoElab` ACCEPTS (it may reject anything Lean accepts, never the reverse: SUBSET RULE).

```
file   ::= def+                                  last def = entry; no other text
def    ::= 'def' name ('(' name+ ':' ty ')')* ':' ty ':=' expr       zero parameters allowed, no empty binder group
ty     ::= 'UInt64' | 'Int64'                    the same in every type position of the file
expr   ::= 'let' name ':=' expr ';' expr | sum   (a `let` only at the start of an expression, `;` required)
sum    ::= prod (('+' | '-') prod)*              left associative
prod   ::= app ('*' app)*                        left associative, binds tighter
app    ::= '-' num | name atom^k | atom          k = arity of the earlier def `name` (k >= 1); `-num` = (0 - num) (Neg UInt64/Int64)
atom   ::= num | name | '(' expr ')'             name = parameter / let (innermost wins) or an earlier def of arity 0
name   ::= 1-3 lowercase letters, then digits or `_`digit groups (`x`, `sq`, `add3`, `x_1`), not in `reserved` (Elab.lean: Lean keywords and
           Init/exported names of that shape: and at bif bne by do end for fun get id if in ite max min mt mut not or rfl set try xor)
num    ::= [0-9]+                                wraps mod 2^64 (as `OfNat UInt64/Int64`); must not touch a name character or `(`
white  ::= ' ' | '\n' | '\r\n'                   a line starts (column 0) with a space, a newline or `def`
```
Further conditions: calls only to EARLIER defs (no recursion), exact arity, every name bound, def names pairwise distinct, no adjacency
`x(`, `)(`, `)x` (Lean needs whitespace before an application argument), no tab, no lone CR. Semantics: `Prog = Nat x Ex` (entry arity,
body); name resolution inlines the callee (`Ex.call body args`), variables are de Bruijn (newest = 0, parameters pushed in order), `den`
wraps like `UInt64` (Int64 = the same bits). Input = the entry's arguments as 8-byte LE words, output = one 8-byte LE word.

## Subset findings (task 3, `Testing/nano/edge.py`, oracle `Testing/nano/oracle.lean`)
The oracle runs Lean's REAL frontend (`IO.processCommands`, header-less file = `import Init`, errors = reject, entry evaluated by the
interpreter) and `nanoElab` + `Prog.eval` on the same text. `edge.py N seed`: ~350 hand-written edge cases (each as UInt64 and Int64; the table
is `Testing/notes/NANO_SUBSET.md`) + every root name of `Init` (1821) and every identifier-like parser token (168) as def / parameter / let name
+ every 2-letter name and random 1-3-letter names with digit / `_1` suffixes in the same three roles (and used afterwards) + token soups +
mutations of valid programs + layout fuzz (random separators incl. column 0, tabs, CR) + shadowing of earlier defs. Verdicts: both reject /
nano rejects only (allowed) / both accept with equal values / BUG.
History: this box and nano-mvp fixed the same class of bugs independently; the merged `Nano/Elab.lean` is nano-mvp's (name shape +
`reserved`, tabs, lone CR, glued numerals / arguments, empty binder groups, duplicate defs) plus ONE more rule found by `edge.py`:
(*) Lean rejects a body or an argument at COLUMN 0 (`def f (x y : UInt64) : UInt64 :=\na * 3`, `g x\n5`), nano accepted: a line may only
start with a space, a newline or `def` (`lineStart`). With it: 0 BUGs (seeds 5, 6, 11-13, 21, 31, 77; 5500-10300 cases each, 200-440 accepted by both).
Found in the pre-merge `nanoElab` (all fixed by rejecting): keywords and `Init` names as names (`def id`, `ite`, `Nat`, `Type`, `sorry`, `_`,
`fun`, `if`, ...), tabs, lone CR, `g(x)(y)` / `g x(y)` / `(x)y`, duplicate defs, column-0 arguments. My own alternative rule (one letter,
then digits/`_`: no list at all, none of the 1821 + 168 names is in the class) is kept out: nano-mvp's wider class with a `reserved` list is
now the one in `Elab.lean`; it is exact only if `reserved` is complete (checked by the `SHAPE` part of `edge.py` and by
`Testing/nano/reserved.lean`/`boundary.py`; a name outside the sampled space could still be missing: the safe fallback is the one-letter rule).
No "meanings differ" case was found (numerals >= 2^64, `-1`/`- 1`/`x -1` = `x - 1`, `x - y - z`, `x - y * z`, application vs binary
operators, unary minus on UInt64, shadowing of earlier defs by parameters/lets all agree). Accepted by Lean, rejected by nano (allowed, by
design): `-x`, `-(e)`, `--`/`/-` comments, `let` without `;`, `let` mid-expression, `x'`, unicode, empty file (Lean accepts it, nano: no entry),
adjacent binder groups `(x : UInt64)(y : UInt64)`, `0x..`/`1_000`/`1e3`, `.`-names, `|>.`, `$`, `fun`, `if`.

## Pipeline
`nanoCompileS src = (nanoElab src).map nanoGenS`, `nanoGenS p = asm (genR p)`.
1. `nanoElab`: `lex` (fuel = length) -> mutual structural parsers on fuel with the scope and the def table; arity and scope errors give `none`.
2. `genR`: stack machine, calls inlined, every value on the machine stack; output = 4-byte pseudo-instruction records `[op,a,b,c]`.
3. `asm` (`Nano/Asm.lean`): records -> RISC-V words. This is the stage compiled by our compiler.

### Calling convention of the generated code (`StartCorrect`, Spec/Top.lean; `riscvMapping`)
a0 = input address, a1 = input length (unused), a2 = work base (8-aligned), sp = work top, a3 = output address, ra = return.
Input blocks and output block are NOT assumed aligned: arguments are read BYTEWISE (`lbu`, `slli`, `or`), the result is written BYTEWISE
(`srli`, `sb`, 8 bytes). The value stack lives in the work block, not in sp: stack pointer t6 (x31) starts at sp, grows DOWN; every push is
`addi t6,t6,-8; bgeu t6,a2,+12; addi a0,x0,-1; ret; sd t0,0(t6)`: a push beyond the work block sets a0 = 0xFFFFFFFFFFFFFFFF (`oomFlag`)
and returns, nothing else changed (sp, gp, s-registers untouched; only t0 t1 t3 t6 are written, a0 only on overflow, input/output blocks
only at the end). `memoryNeeded` = 8 * `Nano.depth p` (`depE`: peak stack slots including the arguments); work = exactly that fits, one byte
less returns the flag (tested). On success a0 keeps the input address (not the flag). Limits: slot offsets are 8 bits: arity < 127 and
stack slots of an expression < 256 (not checked by `nanoElab`). Entry: `mv t6,sp; mv t3,a0`, arguments pushed in order (`rd8`, `push`,
`addi t3,t3,8`), body, `ld t0,0(t6)`, `wr8`, `ret`.

### Records of `asm` (14 ops; `op & 7` is funct3)
`0 ADDI imm=sext8 c | 1 SLLI | 3 LD imm=8c | 4 LBU imm=c | 5 SRLI | 6 ORI imm=c | 7 BGEU (a=0, rs1=b, rs2=c, offset +12) | 8 ADDI imm=8c |
11 SD imm=8c | 16 SB imm=c | 14 OR | 24 ADD | 32 SUB | 40 MUL | 48 RET (0,1,0)`; fields rd=a rs1=b (rs2=c, imm=c; stores rs2=a). Each of the
four byte macros `X0..X3` has at most 7 clauses (see "Front-end findings").

## What exists, and how it is established
| link | status |
|---|---|
| `asm` (records -> code) as RISC-V code on the Sail model computes `asm` | **proved**: `Nano.Self.nanoAsm.implements1` (`frontx_compile` + `frontx_implements_listC`, 379 words, the 77 Sail model axioms, `axioms_nano-e2e.lean`) |
| that binary vs executed Lean | tested: `Testing/nano/nano_selfhost.py` (70 programs): `frontx_test.py` on QEMU **and** Sail == Lean `asm` (70 cases, lengths up to 1664); plus the binary assembles each program's records == Lean `nanoGenS`, and the result runs on qemu-riscv64 for 6 inputs (420 pairs) == `Prog.eval` |
| `nanoElab` agrees with Lean's elaborator | **proved per program, for all inputs**: `Nano/Agree.lean` (39 programs) and `Nano/AgreeInt.lean` (22), `elabEq` (`decide +kernel`) and `agree`; plus the subset evidence above |
| `nanoGenS` output correct | **tested, not proved** (nano-proof proves the IR generator `nanoGen`): `Testing/asm/nano_s_test.sh`: 40 random/structured programs + 3 sources, `ir_test.py` (the real `StartCorrect` harness: QEMU and Sail, work = `memoryNeeded` and one byte less, aligned and misaligned (`MIS`) input/output, writes only in output + work, a0 kept / -1): 1032 program x input pairs (4 hand-made `Ex` incl. out-of-range variables, `anil`/`acons` as expressions, a non-chain argument list: `genR` is faithful to `den` on ALL `Ex`); `nano_test.py 5` and `NANO_INT=1 nano_test.py 30 3` (user-mode QEMU with an odd args address and unaligned output, plus Sail): 264 + 312 pairs == `Prog.eval` |
| `nanoElab`, `genR` as RISC-V code | **not done**: see "Self-hosting status" |

Run: `lake build Nano`; `python3 Testing/nano/nano_test.py 20`; `bash Testing/asm/nano_s_test.sh`; `python3 Testing/nano/fuzz.py 300 7`;
`python3 Testing/nano/edge.py 1500 11`; `python3 Testing/nano/nano_selfhost.py 31` (afterwards `rm -rf Testing/asm/ctest`); regenerate Agree:
`python3 Testing/nano/gen_agree.py; python3 Testing/nano/gen_agree_int.py`. Deep programs need `ulimit -s unlimited` and `lean --tstack=4000000`.

## Front-end findings
* `asm` macros: a chain of more than 7 `if .. else if` clauses in one macro (`X1` with 8) makes `frontx_compile` fail ("could not prove" an
  `rfl` obligation on the `BExp.denote` of the chain; 5 separate probes, each op added alone to the 9-op version). Cure: make the encoding
  arithmetic (funct3 = `op &&& 7` as one expression, I-type and R-type share the byte formulas, BGEU/RET fit the same shapes): 15 ops in 4
  macros with 7/4/3/6 clauses.
* `frontx_view Nano.lex`: "a recursive call that is not on a view of the list", `Option (List Tok)` results, `spanNum/spanId` pairs. Parser:
  mutual recursion, `Option` of pairs with an inductive payload; `genE/genA`: tree + list (`sc`) + depth, results built by `++` of call
  results. `UInt8 <<<` written as `(x.toUInt64 <<< k).toUInt8`; literals in `|||` annotated `: UInt8`.
* Design consequence: the bit packing of instruction words lives in `asm`; `genR` only chooses registers/slots.

## Self-hosting status (task 2) and what blocks it
**B (the proved binary) covers ONLY the assembler stage `asm`** (records -> words, `Nano.Self.nanoAsm.implements1`, 379 words). `nanoElab` and
`genR` are plain Lean; no byte-level rewrite of them was accepted, so there is no "friendly = original" proof and B does not compute the whole
`nanoCompileS`. Evidence (all reproducible, `Testing/nano/probes/`):
1. `genR` as a byte machine. The stack generator was reshaped for it where it was free to (faithful on all `Ex`, position-independent
   records, `memoryNeeded = 8 * depth`), but the generator is a tree walk with a scope list `sc` (de Bruijn index -> slot) and a depth `d`, and
   its code per node is 5-22 records. A flat token stream with `d` as a scalar would remove the tree walk, but then every token must expand
   to a chunk of up to 20 constant bytes inside one `if`-arm; `probes/token_machine.lean` (5 arms, 20-byte chains, `d` threaded) does not
   finish in 30 minutes (TINYSELF.md item 5: 8 arms of 12 bytes: 44 variables / 36 slots, 388 obligations, abandoned). A phase counter (one
   record per iteration) loops in `frontx_view` (TINYSELF.md item 6). The inductive path (`frontx_ind`) allows one scalar and one tree parameter
   (no `sc` list), results by `++` of call results are rejected (F3), arms <= 4-5 (F1, relaxed in NOTES section 25 for decoding only).
2. `nanoElab`: list views need structurally decreasing views (`lex` token spans continue on `ys`), `Option (List Tok)` / pair results and mutual
   recursion are outside every front end; `frontx_rec` (NOTES section 15) handles `if`-trees with all-or-no recursive calls and scalar results only
   (no list results through calls). A shunting-yard / explicit-stack parser needs word arrays and loops (the `wa` path, NOTES section 20) and a
   def table with code strings; the equivalence proof against the recursive-descent parser (all inputs, not per program) was judged out of reach
   for this round (it is the dominant cost, not the front end).
3. New finding that applies to every self-hosted stage: an `if`-chain macro with more than 7 clauses is rejected (see Front-end findings); the
   assembler had to be re-encoded arithmetically to fit 15 ops.
What would make B the whole compiler: (a) a front-end form for "emit a fixed chunk per input element" (e.g. a table-driven loop over a constant
byte table, `wa`) so that `genR` over a flat token stream compiles; (b) `lexer + parser` written as one loop with an explicit stack in word arrays,
or the recursive-descent parser's CPS/defunctionalised form with a generic equivalence lemma; (c) the serialisation `Prog -> tokens` produced by
the elaborator itself. The calling convention above is the interface for the proof of the stack generator by nano-proof (route (a)):
`StackRec.lean` there was written against the previous sp/a1 convention of `genR` and has to be moved to the registers above.
