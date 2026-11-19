/* shim_rv: run nano-compiled RISC-V code natively.  Usage: ./shim_rv CODE.bin < input > output
   Build: riscv64-linux-gnu-gcc -O2 -static shim_rv.c -o shim_rv.   UNPROVEN GLUE, no bounds checks. */
#include <stdio.h>
#include <sys/mman.h>
enum { CODE = 4 << 20, IN = 1 << 20, OUT = 2 << 20, WORK = 80 << 20 };          /* fixed sizes, bytes */
static unsigned char in[IN], out[OUT];
static long work[WORK / 8];                                                      /* 8-aligned, zero */

int main(int argc, char **argv) {
    FILE *f = argc == 2 ? fopen(argv[1], "rb") : 0;
    if (!f) return fprintf(stderr, "usage: shim_rv CODE.bin < input > output\n"), 2;
    unsigned char *code = mmap(0, CODE, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    long code_len = fread(code, 1, CODE, f), in_len = fread(in, 1, IN, stdin);
    if (code == MAP_FAILED || code_len == CODE || in_len == IN) return fprintf(stderr, "shim_rv: no executable memory, or code/input too large\n"), 2;
    __builtin___clear_cache((char *)code, (char *)code + code_len);

    /* the code's convention: a0 input, a1 its length, a2 work base, a3 output, sp = work top, ra = return */
    register long a0 __asm__("a0") = (long)in, a1 __asm__("a1") = in_len;
    register long a2 __asm__("a2") = (long)work, a3 __asm__("a3") = (long)out;
    long top = (long)work + WORK;
    /* park our sp in s1 (the code keeps sp and s0..s11), use the work block as stack, call, switch back */
    __asm__ volatile("mv s1, sp\n mv sp, %[top]\n jalr ra, %[code], 0\n mv sp, s1"
        : "+r"(a0), "+r"(a1), "+r"(a2), "+r"(a3) : [top] "r"(top), [code] "r"(code)
        : "ra", "s1", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a4", "a5", "a6", "a7", "memory");

    /* a0: 0 ok, 1 ok with empty output, -1 out of work memory, -2 buffer capacity; a1: output length */
    fprintf(stderr, "shim_rv: status %ld, %ld output bytes\n", a0, a1);
    if ((a0 != 0 && a0 != 1) || a1 < 0 || a1 > OUT) return 1;
    fwrite(out, 1, a1, stdout);
    return 0;
}
