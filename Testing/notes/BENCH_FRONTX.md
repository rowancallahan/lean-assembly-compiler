# Speed of the automatic front end (`Riscv/Frontx`) — instruction counts

Measured, not proved. Code: `Testing/asm/bench_frontx/` (`bench_frontx.py`, `bench.c`, `Bench.lean`, `x86main.c`, `trace.py`;
raw numbers `results/{rv,x86}.json`). Reproduce: `python3 bench_frontx.py rv`, then `lean -c build/Bench.c Bench.lean && leanc -O2 …`,
`gcc -O2 x86main.c bench.c …`, `python3 bench_frontx.py x86`.

## Method
- **ours** = `Testing/asm/frontx-words/<f>.words` (the committed output of `frontx_implements`, i.e. `compBFO`), run on
  `qemu-system-riscv64 -icount shift=0`, `csrr minstret` around the call (as `bench/bench.py`), cost of an empty `ret` subtracted.
  Calling convention of `Implements1` (a0 input, a1 length, a2 work block, a3 output, sp work end). Every run's output
  is asserted equal to a Python model (all 16 functions, 3 sizes, 0 mismatches).
- **gcc -O2** = `bench.c`, natural C of the same function, `riscv64-linux-gnu-gcc -march=rv64i -O2 -ffreestanding`, same driver.
- **Lean** = the same Lean definitions (copied from `Riscv/Frontx/*.lean`; the entry points are `f xs.data.toList` etc.) compiled
  `lean -c` → `leanc -O2` (Lean 4.29.0) and run on **x86-64**; counted with valgrind callgrind `Ir`, per-call cost = (3 calls − 1 call)/2.
  No RISC-V Lean runtime is available here, so **ours/Lean compares RV64 instructions to x86-64 instructions** (different ISAs; x86
  is usually somewhat denser). `Lean/gcc(x86)` is the same-ISA check: gcc -O2 on x86 (`bench.c`) vs Lean.
- **opt** = the hand-written optimised-path code (`opt-words`, `compileAFO`) where the same function exists (sum ≙ `tailSum`, inc ≙ `incEach`).
  No other frontx function has a `compileO/compileBFO` counterpart written by hand; the frontx words *are* `compBFO` output already.
- Inputs: 1 KiB, 64 KiB, 1 MiB pseudo-random bytes (`scan` inputs, bytes < 4, for `findnl`/`findfirstgt3` so the whole input is scanned).
  Per-byte cost is identical at all three sizes (±0.1); fixed cost of ours is 26–143 instructions (prologue: frame set-up by `slli/addi`
  chains, slot zeroing, registers initialised to 0).

## Table (instructions per input byte at 1 MiB; "whole call" where cost is constant)

| function | words | ours | gcc -O2 RV64 | ours/gcc | Lean (x86) | ours/Lean | Lean/gcc (x86) | opt |
|---|---|---|---|---|---|---|---|---|
| crcraw (CRC-32) | 170 | 70.00 | 69.00 | 1.01 | 79.0 | 0.89 | 1.1 | – |
| b64all | 144 | 55.22 | 11.12 | 4.97 | 58.9 | 0.94 | 3.9 | – |
| findnl (find) | 113 | 27.00 | 5.00 | 5.40 | 117.0 | 0.23 | 23.4 | – |
| tailsum | 77 | 12.00 | 4.00 | 3.00 | 201.5 | 0.06 | 40.3 | 4.00 (ours/opt 3.0) |
| nontailsum | 78 | 13.00 | 4.00 | 3.25 | 208.5 | 0.06 | 41.7 | – |
| drop5 | 135 | 26.00 | 5.00 | 5.20 | 132.5 | 0.20 | 22.1 | – |
| filterall | 72 | 21.95 | 6.97 | 3.15 | 240.3 | 0.09 | 30.2 | – |
| inceach (map) | 59 | 16.00 | 6.00 | 2.67 | 186.5 | 0.09 | 31.1 | 6.00 (2.67) |
| twice (append) | 108 | 47.00 | 7.00 | 6.71 | 287.9 | 0.16 | 48.0 | – |
| findfirstgt3 | 76 | 19.00 | 4.00 | 4.75 | 213.6 | 0.09 | 42.7 | – |
| taillength (count) | 73 | 10.00 | O(1): 45 total | n/m | 140.5 | 0.07 | O(1) | – |
| booklength (count) | 73 | 10.00 | O(1): 45 total | n/m | 147.5 | 0.07 | O(1) | – |
| finalof | 77 | 17.00 | O(1): 10 total | n/m | 138.5 | 0.12 | O(1) | – |
| take5 | 80 | 182 total | 39 total | 4.7 | 125.4 (per byte; `toList` of the whole input) | ≈0 | – | – |
| headof | 57 | 52 total | 9 total | 5.8 | 119.5 (per byte, `toList`) | ≈0 | – | – |
| be32at0 | 126 | 114 total | 62 total | 1.8 | n/a (dispatch noise) | – | – | – |

n/m = not meaningful: the natural C of `length`/`final?` is O(1) (`n`, `xs[n-1]`), the frontx code walks the list shape (a loop).

Reading the table:
- **vs gcc -O2: 2.7–6.7× more instructions** on every function that loops, except CRC (1.01×, the 8 unrolled bit steps dominate).
- **vs Lean: ours is 4–17× cheaper per byte** (except b64all/crc 0.9×) — but the Lean sources are `xs.data.toList`-based, so Lean's compiled
  code allocates a cons cell per byte (`take5` and `headof` cost O(n) in Lean because of `toList`, O(1) in ours); the per-byte Lean cost
  (60–290 Ir) is allocation, not looping. Against gcc on the same ISA Lean is 22–48× worse on the list functions. On the already
  array-shaped functions (crc, b64all) Lean is within 1.1×/3.9× of gcc and ours is within 1.0×/5.0×.
- **opt column:** the hand-written optimised code (sum 4, inc 6) equals gcc; frontx code for the same functions is 3.0× / 2.67× that.

## The worst three comparable ratios, from the generated code

(`trace.py FN [ours|c]` runs the words in a small RV64I interpreter and prints the per-pc counts of the steady-state loop; its totals
match the QEMU numbers: 27.0, 26.0, 47.0 per byte.) The cause is the same in all three; the numbers below split it.

### 1. `twice` (`xs ++ xs`): 47 vs 7 (6.7×)
Ours is two passes (`xs.data.toList ++ xs.data.toList` becomes two copy loops, each ≈ 23.5 instructions per byte, `.cp` mode loop of
`frontx_tailcopy`); gcc fuses them and stores both bytes in one 7-instruction iteration (`lbu; add; addi; sb; sb; addi; bne`).
Per copied byte, ours: `add a6,a0,a7; lbu; add a6,a3,t2; sb` (address arithmetic recomputed from base + index for source and
destination, 4), `addi/addi/add a7,zero,t5` (increment through a temporary, then a copy back, 3), `li a6,1` (loop flag), and
≈ 14 instructions of control that compute nothing: `add t4,zero,a6; xori t3,t4,0; seqz t3,t3; beqz` (flag test + negation, 4),
`sltu t5,a7,a1; xori; seqz; beqz` (the bound test turned into a 0/1 value and negated, 4), `li t5,0; bnez t5,…` (a one-iteration
inner loop whose exit flag is the constant 0, 2, twice) and `beqz t4`/`li t4,0; bnez` (2+). Two such loops run back to back.

### 2. `findnl` (`for … if at' bs j == c then return j`): 27 vs 5 (5.4×)
Loop body (27 executed instructions): `sltu t3,a6,a1; xori; seqz; beqz` (the `for _ in [i:bs.size]` range test, 4) +
`sltu t4,a7,a1; xori; seqz; beqz` (the `at'` guard `i < bs.size` — the same fact tested again with a second counter, 4) +
`add t1,a0,a7; lbu` (2; gcc: `add; lbu`) + `li t4,0; bnez t4` (dead one-shot loop, 2) + `beqz t3` (1) +
`xor; seqz; xori; seqz; beqz` (the `== c` test as a 0/1 value, negated, branched on, 5) + `beqz t3` (1) +
`addi a7; addi a6` (two counters, 2; gcc has one) + `li t3,0; bnez t3` (2) + `li t3,0; bnez t3` (2) + `beqz t2` + `bnez a4` (loop flags, 2).
gcc: `addi; beq; add; lbu; bne`. Roughly 5 of 27 do the work; 6 are `li 0; bnez` pairs, 7 are `xori/seqz` boolean round-trips,
8 are two bound tests, 3 are flag branches, 1 is the duplicate counter.

### 3. `drop5` (`Match.drop 5`): 26 vs 5 (5.2×)
Same shape plus a spill: the mode flag of the `.cp` loop lives in frame slot 9 (variables above 7 are in stack slots,
`NOTES.md` section 5): `sd t4,72(gp)` at the top and `ld t4,72(gp)` at the bottom of every iteration (2 memory instructions per byte).
Breakdown of 26: flag test 5 (incl. the store), bound test 4, `add; lbu; add; sb` 4, increments 7 (`li a6,1; addi; addi; add; add; li; bnez` —
two counters, each incremented into a temporary and moved back), exit-path flags 5 (`beqz t3; li t3,0; bnez t3; ld; beqz; bnez`). gcc: `lbu; addi; addi; sb; bne`.

### Where the extra instructions come from, and which existing pass removes them
Not register allocation and not per-byte copies of data: the code *does* use `compBFO` with 8 argument registers, and bytes move
only once. It is the shape of the `BStmt` the front end emits (`NOTES.md` section 5: "a conditional is two loop headers plus two flag
assignments; tests produce a 0/1 value that is tested again", item 9.5.5 "loop conditions without the flag variable"):

| symptom in the code | share (findnl/drop5/twice) | existing pass that would fix it | why it does not fire now |
|---|---|---|---|
| `li r,0; bnez r,back` one-shot loops and `beqz` on flags | 6+ / 5+ / 8+ | none exists for constants: `SR.lean` has copy propagation and DCE of temporaries only; `OPT.md` lists "constant folding beyond `op c₁ c₂`" as not done | needs branch folding on a constant test, then DCE |
| `xori t,x,0; seqz t,t` boolean round-trips, `sltu` result tested again | 7 / 4 / 8 | `Sel.lean` compare/branch fusion (`TstSpec`: a comparison becomes the branch itself) | it fuses within one expression tree; the front end assigns the comparison to a flag variable first, so the test is a separate statement the selector never sees |
| two counters (`a6`,`a7`) and `addi t; add a7,zero,t` increments | 3 / 7 / 6 | copy propagation in `SR.lean` (`add rd,x0,rs` of a temporary) | `sr` only fires on loops whose head code is trivial (`while i <u n`), these loops have flag heads, so `bodySR` falls back to the plain code |
| `add a6,a0,a7; lbu` address recomputed every byte | 1 / 2 / 4 | `SR.sr` strength reduction (pointer increment: sum/take/map reach 4/5/6 = gcc) | same: head not trivial |
| duplicate bound test (`i < size` in `at'` and in the `for` range) | 4 | none (would need a loop-invariant / range fact); `Arr.lean` `okA` relies on the source's own test | – |
| frame slot for the flag (`sd/ld 72(gp)`) | 2 (drop5) | liveness-based allocator / spill choice in `Alloc.lean` (OPT.md: "liveness checker, spill slots" done for `BStmt`, but the front end uses N=13 slots with fixed roles) | flag variable is variable 9 |
| `twice`: two passes | 23.5 extra | no existing pass (loop fusion) | follows the source (`xs ++ xs`) |

So the most effective single change is on the front end side (generate `BStmt` loops with the condition in the head and no flag variable,
as 9.5.5 says); after that the existing `SR` (strength reduction + copy propagation + DCE) applies and gives the 4/5/6-per-byte loops of
`OPT.md`. I did not run this (no Lean model build here); the claim that SR does not fire rests on the disassembly (no pointer increments
in the loops) and on `SR.lean`'s stated precondition.

## Caveats
- ours/Lean is RV64-vs-x86-64 instruction counts, not cycles, and Lean's number includes allocation/free of the list per call.
- `be32at0` Lean count is dispatch noise (the `main` string `match`), left out. Lean's `main` dispatch (≤16 string compares) is ~1000 Ir per call, negligible for the rest.
- Instruction counts, not time: gcc's loads/stores per instruction are not modelled; no cycle-accurate model was used.
- Only RV64 measured; ARM words for frontx do not exist yet.
