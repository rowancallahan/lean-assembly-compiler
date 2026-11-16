# IR C oracle (work in progress)

Goal: untrusted `Ir.toC : Prog → String` (Compiler/Ir/ToC.lean, outside the proof chain) printing an IR program as C99, plus
`Testing/asm/ir_c_oracle.py` comparing gcc -O2 output with `Ir.run` and the QEMU results at `memoryNeeded` and `memoryNeeded - 1`, then fuzzing.

## State
- Nothing implemented yet. Only read `Compiler/Ir/Syntax.lean`, `Sem.lean`, `Examples.lean`, `Testing/asm/emit_ir.lean`.
- `git fetch origin main build-cache` was slow in this container (build-cache and ir-s2 not fetched; branch made from origin/main).

## Semantics to mirror in C
- Values: 64-bit word or pointer (block, cell offset); block 0 input bytes, 1 output bytes (grows on write), k+2 allocated cell blocks.
- Stuck cases (OOB, uninitialised cell read, pointer arithmetic on words, ordering compare on pointers) must `abort()`.
- Calling convention: main params = (input ptr, input length, output ptr); `emit_ir.lean` writes `.cases` lines `input output memoryNeeded`.
- Out-of-memory: work block of `memoryNeeded` bytes (8 per cell, frame = slots+1 cells per call, `peak` of the events); `memoryNeeded - 1` must return the OOM flag.

## Next steps
1. Write `Compiler/Ir/ToC.lean` (blocks as labels + gotos, vregs as `uint64_t` locals, pointers as address into the work block, bump/stack allocator matching `Proven.Top.Alloc` event model; check `Riscv/Back/Ir*.lean` for the exact OOM flag and allocator).
2. Write `Testing/asm/ir_c_oracle.py`: read `ir-words/*.cases`, compile C, compare outputs and OOM behaviour.
3. Fuzz with random inputs, shrink mismatches, add results here.
