# `Implements1`: the user-facing statement, clause by clause

Definition: `Spec/Implements1.lean` (`Implements1With encA encB code f space maxLen retLen`; `Implements1` uses
the `Bytes` encodings of `Spec/Encode.lean`, `Implements1Raw` the identity encoding `encRaw` for raw byte lists).
It supersedes `Implements` of `Spec/Riscv.lean` (kept, marked OLD, because older theorems are stated with it).
ONE resource bound: `space n`, the bytes of work memory the code may use for an `n`-byte input.

## Hypotheses (what the caller / OS guarantees)

| clause | says | why |
|---|---|---|
| `x.length ≤ maxLen` | inputs up to `maxLen` bytes (default `2^20`) | keeps all lengths and addresses far below `2^32`/`2^64` so the code's 64-bit arithmetic cannot wrap; owner decision: leave as is for now |
| `Cfg s` | the fixed control state (M-mode, no interrupts, PMP off, one RAM PMA region `[2^31, 2^32)`) | the setting in which the Sail model is run; "a correctly functioning OS hosts the process" |
| `PC = entry`, `entry % 4 = 0`, code bytes at `entry` | the code is loaded anywhere (4-aligned) and execution starts at it | position independence |
| `a0 = input.base`, `a1 = |x|` | where the input is and how long | calling convention |
| `a2 = work.base`, `sp = work.base + work.len` | the work block; the stack grows down from its top | the ONE resource: all scratch, stack frame and spill slots live in this block |
| `a3 = output.base` | where to write the result | calling convention |
| `ra`, `ra % 4 = 0`, `ra` not inside the code | the return address | the run must end by returning to it |
| input bytes = `x`, `input.len = |x|` | the input block holds `encA a` | |
| `|y| ≤ output.len` | the output block has room for the result `y = encB (f a)` | |
| `space |x| ≤ work.len`, `work.base % 8 = 0` | the work block is big enough and 8-aligned | the only resource bound; alignment for 8-byte loads/stores (word arrays, spill slots) |
| all four regions in RAM, pairwise disjoint | input, output, work, code do not overlap and are executable/readable/writable RAM | |
| `Mapped s output`, `Mapped s work` | **hosting hypothesis**: every byte of the output and work blocks is present in the model's memory map | the Sail memory is a finite map; reading an absent address faults. The OS provides these blocks as allocated memory; code and input are present by their byte hypotheses |

## Conclusion (what the code guarantees)

| clause | says | why |
|---|---|---|
| `runsTo s (… PC = ra …)` | the machine runs, without a trap, to `ra` | termination + no fault; (`runsTo` is "some state reached", which is enough: see `SPEC_AUDIT.md` W6) |
| `bytesAt output.base |y| = y` | exactly the first `|y|` output bytes are the result | the part of the output block that is the result is stated exactly |
| `unchangedOutside s s' [⟨output.base, |y|⟩, work]` | **nothing else in memory changed**: the input, the output bytes beyond the result, and every other address (present or absent) are as before | no hidden side effects; the bytes after the result are UNCHANGED (not zeroed) |
| `abiSavedKept s s'` | `sp`, `gp`, `tp`, `s0..s11` (`x2, x3, x4, x8, x9, x18..x27`) have their old values | the RISC-V psABI callee-saved set (`gp`, `tp` are not to be changed by a function either). The merge sort uses `gp` as its frame register and restores it |
| (not stated) | `ra`, `t0..t6`, `a0..a7` may hold anything | the psABI lets a callee clobber them (`ra` is consumed by the return) |
| `Cfg s'` | the pinned control state holds again: privilege, `misa`, `mstatus`, `mcountinhibit`, `minstretcfg`, `pmpcfg`, HTIF, `elp`, `mseccfg`, the PMA region | these are therefore UNCHANGED (both states have the values `Cfg` fixes) |
| (not stated) | other CSRs: `mscratch`, `mtvec`, `mepc`, `mcause`, `mie`, `mip`, `satp`, `pmpaddr*`, counters (`minstret` necessarily changes) | not covered: the per-instruction step lemmas (`Next`) say nothing about them, so proving them unchanged needs new step lemmas (see `SPEC_AUDIT.md` W4) |
| `retLen = true → a1 = |y|` | for VARIABLE-length results, the result length is returned in `a1` (the second ABI return register, as `Compiler/Front/PipeStd*.lean`) | the caller cannot know `|y|` otherwise. Fixed-length results (sorts, maps, the 8-byte sum) use `retLen = false` |

## Proved instances (`Riscv/Examples/Implements1Ex.lean`, `Implements1Pipe.lean`, `Crc.lean`)

| theorem | function | `space n` | `retLen` |
|---|---|---|---|
| `Proven.sortCode_implements1` | insertion sort = `mergeSort` | `0` | false |
| `Proven.msortCode_implements1` | merge sort | `n + 71` | false |
| `Mach.Riscv.take_implements1 k` | `List.take k` | `15` | **true** |
| `Mach.Riscv.inc_implements1` | `List.map (· + 1)` | `15` | false |
| `Mach.Riscv.sum_implements1` | byte sum, 8-byte LE word | `15` | false |
| `Proven.compileP_implements1` | any accepted pipe with `Pipe.space ≤ Pipe.len` | `0` | false |
| `Mach.Riscv.crc32_implements1` | CRC-32 | `2048 + 15` | false |

`15` = the 8-byte frame cell in which `compBF` saves `gp`, plus up to 7 bytes of alignment below `sp`.
