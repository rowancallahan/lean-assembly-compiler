# shim_rv.c explained (for a reader who knows C but not RISC-V)

## 1. Why a shim: the compiled code is a bare function
The compiler's output is a block of machine instructions and nothing else. It has no `main`, makes no system calls,
opens no files and never calls `malloc`. It is one function: "given these bytes and this scratch memory, write the
result there and return". Something has to load it, hand it memory, call it and deal with files. That host is the shim.

## 2. The registers involved
A RISC-V processor has 32 registers, each a 64-bit variable. By convention some have roles:

| register | role here |
|---|---|
| `a0` | in: address of the input bytes. out: the status code |
| `a1` | in: number of input bytes. out: number of output bytes |
| `a2` | address of the start of the work block (scratch memory) |
| `a3` | address where the output bytes must be written |
| `sp` | stack pointer. On entry it must be the END of the work block |
| `ra` | return address: where the code jumps when it is done |
| `s1` | a "saved" register; the shim borrows it to remember its own stack pointer |

## 3. The assembly line, token by token
```c
__asm__ volatile("mv s1, sp\n mv sp, %[top]\n jalr ra, %[code], 0\n mv sp, s1"
    : "+r"(a0), "+r"(a1), "+r"(a2), "+r"(a3) : [top] "r"(top), [code] "r"(code)
    : "ra", "s1", "t0", …, "a7", "memory");
```
- `mv s1, sp` — copy `sp` into `s1`. (`mv dst, src`.) The C program's own stack pointer is now parked in `s1`.
- `mv sp, %[top]` — set `sp` to the end of the work block. `%[top]` is a placeholder: the C compiler puts the C variable
  `top` in some register and substitutes that register's name.
- `jalr ra, %[code], 0` — "jump and link": store the address of the next instruction in `ra`, then jump to the address
  in the register holding `code` (plus 0). This is the call. The code ends with a jump to `ra`, so it comes back here.
- `mv sp, s1` — put the C program's stack pointer back.
- After the first `:` come values the assembly both reads and writes. `"+r"(a0)` means: the C variable `a0` is in a
  register (`r`), is an input, and is changed (`+`). Because `a0` was declared `register long a0 __asm__("a0")`, that
  register is exactly `a0`. Same for `a1`, `a2`, `a3`. This is how the arguments go in and the results come out.
- After the second `:` come read-only inputs: `[top] "r"(top)` gives the C value `top` the name `%[top]`; same for `code`.
- After the third `:` is the clobber list: registers the C compiler must assume are destroyed. `ra` is overwritten by
  `jalr`. `s1` is overwritten by our first `mv` (so the C compiler saves and restores it around this function).
  `t0..t6` and `a4..a7` are scratch registers the called code is free to use. `"memory"` says the call reads and writes
  memory (the buffers), so the C compiler must not keep stale copies of them in registers.
- `volatile` tells the C compiler not to delete or move the statement.

## 4. Why `sp` = work top, and why `s1` is safe
The code keeps everything in the work block: its buffers grow upward from the base (`a2`), its stack grows downward
from the top (`sp`). If they meet, it returns status −1. So `sp` must point at the top of the work block, not at the C
program's stack. During the call the C stack pointer must survive somewhere; a register the code promises not to change
is the simplest place. `s1` is such a register: the code leaves `sp`, `gp`, `tp` and `s0..s11` as it found them. This
is part of what is proved about it (`KeptRegisters` in the correctness statement), so `mv sp, s1` restores the right value.

## 5. `mmap` with `PROT_EXEC`, and `clear_cache`
Ordinary memory (`malloc`, arrays) may be read and written but not executed. `mmap(… PROT_READ | PROT_WRITE |
PROT_EXEC …)` asks the system for memory that may also be executed; the code file is read into it.
`__builtin___clear_cache` tells the processor that these bytes are now instructions: processors keep a separate cache
for instructions, and it may still hold what was there before.

## 6. Status codes (the value of `a0` on return)
`0` success. `1` success with empty output. `−1` the work block was too small. `−2` a buffer inside the program reached
its fixed capacity. For 0 and 1 the shim writes `a1` bytes to stdout and exits 0; otherwise it exits 1.

## 7. Two steps: compile, then run
The compiler is itself such a code file (`B2.bin`), so the same shim runs both steps:
```
./shim_rv B2.bin   < prog.lean > prog.bin     # the compiler reads source text, writes machine code
./shim_rv prog.bin < input.bin > out.bin      # the compiled program reads input, writes output
```
On a machine that is not RISC-V, put `qemu-riscv64-static` in front of each command.

## 8. What changes on ARM (`shim_arm.c`, for a future back end, untested)
Same idea, other names: arguments in `x0..x3` instead of `a0..a3`; the return address lives in `x30`; the call is
`blr reg` (branch with link to register) instead of `jalr`, and a plain jump is `br`; the saved register used to park
`sp` is `x19`. On Apple Silicon, executable memory must be requested with `MAP_JIT`, writing to it is switched on and
off with `pthread_jit_write_protect_np`, and the cache call is `sys_icache_invalidate`.
