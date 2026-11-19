# Example programs for the nano compiler

Eight small programs in the nano subset, and a script that compiles each with the self-compiled compiler `B2`, runs the
result, and compares the output with the reference semantics. **Unproven glue**: the script and `nanorun` are not part
of the correctness theorem.

| program | computes |
|---|---|
| `count.lean` | number of input bytes (one byte) |
| `sum.lean` | sum of the input bytes mod 256 |
| `maxbyte.lean` | largest input byte |
| `upper.lean` | ASCII `a..z` to `A..Z` |
| `reverse.lean` | the input reversed |
| `hex.lean` | each byte as two hex digits |
| `rle.lean` | run-length encoding (length, byte) |
| `fib.lean` | Fibonacci number of the first byte, 8 bytes little-endian |

## Run everything

```
Testing/nano/v2self/examples/run_examples.sh              # all examples; NOSEM=1 skips the semrun comparison
Testing/nano/v2self/examples/run_examples.sh my.lean      # your own program
```

One line per program: input and output in hex, `nanorun`'s exit status and status line (`a0 = 0` ok, `1` ok with empty
output, `-1` out of work memory, `-2` buffer capacity), then `exp:OK` (output = the program's `-- expect` line) and
`sem:OK` (output = `semrun`'s output). Exit status 1 if anything differs.

Needs: a C compiler. For the `sem` column also Lean 4.29.0 and, once, `lake build Nano.V2Self.Proof.Main.Main`
(needs the Sail model at `../deps/sail-riscv-lean`, see the top-level README).

## The two steps by hand

```
cc -O2 Testing/nano/v2self/run/nanorun.c -o nanorun
grep -v '^--' prog.lean > prog.src                        # the compiler accepts no comments
./nanorun Testing/nano/v2self/B2.bin prog.src prog.bin    # (a) compile: source text in, RISC-V code out
./nanorun prog.bin input.bin output.bin                   # (b) run the compiled program
od -An -tx1 output.bin
```

A rejected program is **not** an error message: the compiler writes empty code (status line `a0 = 1 (ok, empty
output)`, `prog.bin` has 0 bytes). There is no diagnostic saying which construct was refused.

Reference semantics for the same source and input (a Lean error names the stage on a rejection):
`SRC=prog.src INP=input.bin OUT=sem.bin lake env lean Testing/nano/v2self/semrun/semrun.lean`

## Where B2.bin comes from

`Testing/nano/v2self/B2.bin` is checked in (sha256 in `B2.sha256`). It is the compiler compiled by itself.
To rebuild: `Testing/nano/v2self/boot/fixpoint.sh [OUTDIR]` (Lean 4.29 with `leanc`, `qemu-system-riscv64`,
`riscv64-linux-gnu-gcc`): it builds the Lean-compiled `B1`, runs it on the compiler's source to get `B2`, and checks
on QEMU that `B2` compiles the source to `B2` again. Without QEMU, the same check with the interpreter:
`make -C Testing/nano/v2self/run selfcheck`. Details: `Testing/nano/v2self/run/README.md`.

## Writing your own program

- The file is a list of `def`s. The last one is the entry: `def m (x : List UInt8) : List UInt8 := …`
  (input bytes in, output bytes out).
- For the script, add two comment lines: `-- input  (hex): 68 69` and `-- expect (hex): …` (bytes separated by spaces).
- Names: one lowercase letter, then digits (`f`, `s1`, `g_3`).
- Scalars are `UInt64` (wrapping). Operators: `+ - *`, `&&& ||| ^^^`, `<<< k`, `>>> k` (k a numeral), and in `if`
  conditions `==` and `<`.
- `if c then a else b`, `let v := e;` (with the `;`), calls of earlier defs with all arguments.
- Input: `rd x i` (byte i, 0 past the end), `len x`. Output: `put o b` appends the low byte of `b`; start from `[]`.
  Word buffers: `Buf`, `bnew`, `bsize`, `bget`, `bset`, `bpush`.
- The only loop is recursion on a fuel argument, written exactly like this (self call last, fuel `n`):
  ```lean
  def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
    | 0, x, i, o => o
    | n + 1, x, i, o => f n x (i + 1) (put o (rd x i))
  ```
  Fuel is a numeral or `len' x` (sums and products of these).
- The programs are also Lean: `cat Nano/V2Self/Prelude.lean prog.lean > t.lean && lean t.lean` checks one.

## What gets rejected (tried with B2, 2026-11-19)

- comments (`--`, `/- -/`): the script removes lines that start with `--`; write no other comments;
- `&&`, `||` in conditions: nest `if`s (see `upper.lean`, `rle.lean`);
- `<=`, `≤`, `!=`, `/`, `%`: only `==` and `<`; no division;
- a def that takes or returns the output list without also taking the input `x`
  (`def w (o : List UInt8) (v : UInt64) …` is rejected, with `(x : List UInt8)` added it is accepted);
- an entry not named `m`;
- everything else of Lean: `match` (other than the fuel pattern), `fun`, `where`, `namespace`, `open`, strings,
  other types, recursion that is not the fuel pattern, a self call that is not the last thing in its branch.

Limits: input at most 2^20 bytes, output at most 2 MiB in `nanorun`; buffers have a fixed capacity (status `-2`).

## Result here (Linux x86-64, B2 sha256 `bb5558a5…`, Lean 4.29.0)

All 8 programs: compiled by B2, output = `expect` line = `semrun` output. Each was also elaborated by Lean with the
prelude. One input per program; this is a smoke test, not evidence beyond those inputs.
