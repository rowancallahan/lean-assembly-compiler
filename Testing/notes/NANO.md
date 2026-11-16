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
def    ::= 'def' name ('(' name+ ':' ty ')')* ':' ty ':=' expr       zero parameters allowed
ty     ::= 'UInt64' | 'Int64'                    the same in every type position of the file
expr   ::= 'let' name ':=' expr ';' expr | sum   (a `let` only at the start of an expression, `;` required)
sum    ::= prod (('+' | '-') prod)*              left associative
prod   ::= app ('*' app)*                        left associative, binds tighter
app    ::= '-' num | name atom^k | atom          k = arity of the earlier def `name` (k >= 1); `-num` = (0 - num) (Neg UInt64/Int64)
atom   ::= num | name | '(' expr ')'             name = parameter / let (innermost wins) or an earlier def of arity 0
name   ::= [a-z] [0-9_]*                         one lowercase letter, then digits / underscores
num    ::= [0-9]+                                wraps mod 2^64 (as `OfNat UInt64/Int64`)
white  ::= ' ' | '\n'                            a line starts (column 0) with a space, a newline or `def`
```
Further conditions: calls only to EARLIER defs (no recursion), exact arity, every name bound, def names pairwise distinct, no whitespace
needed but NO ADJACENCY `x(`, `)(`, `)x` (Lean needs whitespace before an application argument). Semantics: `Prog = Nat x Ex` (entry arity,
body); name resolution inlines the callee (`Ex.call body args`), variables are de Bruijn (newest = 0, parameters pushed in order), `den`
wraps like `UInt64` (Int64 = the same bits). Input = the entry's arguments as 8-byte LE words, output = one 8-byte LE word.

## Subset findings (task 3, `Testing/nano/edge.py`, oracle `Testing/nano/oracle.lean`)
The oracle runs Lean's REAL frontend (`IO.processCommands`, header-less file = `import Init`, errors = reject, entry evaluated by the
interpreter) and `nanoElab` + `Prog.eval` on the same text. `edge.py N seed`: ~350 hand-written edge cases (each as UInt64 and Int64) +
every root name of `Init` (1821) and every identifier-like parser token (168) as def / parameter / let name + 26 letters and digit/underscore
variants + token soups + mutations of valid programs + layout fuzz (random separators incl. column 0, tabs, CR) + shadowing of earlier defs.
Verdicts: both reject / nano rejects only (allowed) / both accept with equal values / BUG. Final runs: 0 BUGs (seeds 5, 11, 12, 13, 21, 31;
5501-10264 cases each, 200-440 accepted by both, the rest rejected by at least nano).
Bugs found in the pre-existing `nanoElab` (nano accepted, Lean rejects), all fixed by rejecting:
1. keywords as names (`def f (fun : UInt64)`, `let if := ..`, 168 tokens incl. `at from in by do ...`) and names that already exist in `Init`
   (`def id`, `ite`, `dite`, `panic`, `Nat`, `Id`, `Add`, `Type`, `sorry`, `_` ...: `def` of an existing root constant is an error): ONE
   rule, identifiers are `[a-z][0-9_]*` (no keyword has a digit or is a single letter, no `Init` root name is in the class: asserted by
   `edge.py` against `roots.txt`/`tokens.txt` produced by `Testing/nano/names.lean`; also checked against `Lean` + `Std`). The corpora were renamed
   (`sq`->`s`, `inc`->`i`, `mix`->`m`, ...), `Nano/Agree*.lean` regenerated.
2. tab characters and lone carriage returns (Lean: tabs forbidden, lone CR error): whitespace is space and newline only.
3. `g(x)(y)`, `g x(y)`, `h(x)`, `(x)y`: Lean needs whitespace before an application argument: `adjOk` rejects `[word|)]` directly before
   `(` and `)` directly before a word character.
4. an argument at column 0 (`g x\n\n5`): rejected by Lean, accepted by the token-based parser: a line may only start with space, newline or `def`.
5. duplicate def names (`def f ..; def f ..`: Lean "already declared"): rejected.
No "meanings differ" case was found (numerals >= 2^64, `-1`/`- 1`/`x -1` = `x - 1`, `x - y - z`, `x - y * z`, application vs binary
operators, unary minus on UInt64, shadowing of earlier defs by parameters/lets all agree). Accepted by Lean, rejected by nano (allowed, by
design): `-x`, `-(e)`, `let` without `;`, `let` mid-expression, comments, `x'`, unicode, empty file (Lean accepts it, nano: no entry), tabs/CRLF,
adjacent binder groups `(x : UInt64)(y : UInt64)`, 2^64-sized `0x..`/`1_000`/`1e3` literals, `.`-names, `|>.`, `$`, `fun`, `if`.
Alternative for the final spec: allow longer identifiers by a denylist (the 168 tokens plus the 28 lowercase-alphanumeric `Init` root names
`absurd .. trivial hash64`); the one-letter rule avoids any list.

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
B (the proved binary) covers ONLY the assembler stage `asm`; `nanoElab` and `genR` stay plain Lean. SELFHOST_PROBE
