/* shim_rv: run code compiled by the nano compiler as a normal RISC-V Linux process (native, no interpreter).
 * UNPROVEN GLUE, not part of any theorem.
 *   riscv64-linux-gnu-gcc -O2 -static shim_rv.c -o shim_rv
 *   shim_rv CODE.bin INPUT [work_MB] > OUTPUT        (INPUT "-" = stdin)
 * The code's convention: a0 input, a1 length, a2 work base (8-aligned), a3 output, sp = work top, ra = return.
 * On return a0 = 0 ok / 1 ok, empty / -1 out of work memory / -2 buffer capacity; a1 = output length. */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>

#define OUT_CAP (2L << 20)                       /* the compiler never emits more than 1 MiB */

static long slurp(const char *path, unsigned char *buf, long cap) {   /* whole file (or stdin) into buf */
    FILE *f = path[0] == '-' && !path[1] ? stdin : fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    long n = (long)fread(buf, 1, (size_t)cap + 1, f);
    assert(n <= cap && "file too large");
    return n;
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 4) { fprintf(stderr, "usage: shim_rv CODE.bin INPUT|- [work_MB] > OUTPUT\n"); return 2; }
    long work_len = (argc == 4 ? atol(argv[3]) : 80) << 20, code_cap = 4L << 20, in_cap = 1L << 20;
    /* one executable mapping for the code; input, output and work are ordinary memory */
    unsigned char *code = mmap(0, (size_t)code_cap + 1, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    unsigned char *input = malloc((size_t)in_cap + 1), *output = malloc(OUT_CAP);
    unsigned char *work = mmap(0, (size_t)work_len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(code != MAP_FAILED && work != MAP_FAILED && input && output);   /* mmap memory is page-aligned and zero */
    long code_len = slurp(argv[1], code, code_cap), in_len = slurp(argv[2], input, in_cap);
    assert(code_len > 0 && code_len % 4 == 0);
    __builtin___clear_cache((char *)code, (char *)code + code_len);

    register long a0 __asm__("a0") = (long)input, a1 __asm__("a1") = in_len;
    register long a2 __asm__("a2") = (long)work, a3 __asm__("a3") = (long)output;
    long top = (long)work + work_len, sp_after;
    /* switch to the work block as stack, call, switch back.  The host sp waits in s1: the compiled code keeps
       sp, gp, tp and s0..s11 (that is part of its proved contract); everything else may be overwritten. */
    __asm__ volatile("mv s1, sp\n mv sp, %[top]\n jalr ra, %[code], 0\n mv %[spa], sp\n mv sp, s1"
        : [spa] "=&r"(sp_after), "+r"(a0), "+r"(a1), "+r"(a2), "+r"(a3)
        : [top] "r"(top), [code] "r"(code)
        : "ra", "s1", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a4", "a5", "a6", "a7", "memory");
    assert(sp_after == top && "the code did not restore sp");

    long status = a0, out_len = a1;
    fprintf(stderr, "shim_rv: a0 = %ld (%s), a1 = %ld output bytes\n", status,
            status == 0 ? "ok" : status == 1 ? "ok, empty output" : status == -1 ? "out of work memory"
            : status == -2 ? "buffer capacity reached" : "unknown status", out_len);
    if (status != 0 && status != 1) return 1;
    assert(out_len >= 0 && out_len <= OUT_CAP);
    assert(fwrite(output, 1, (size_t)out_len, stdout) == (size_t)out_len && fflush(stdout) == 0);
    return 0;
}
