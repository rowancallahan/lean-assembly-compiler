/* shim_arm: the same for AArch64 (macOS, Linux).  FOR THE FUTURE ARM BACK END, UNTESTED (the compiler emits RISC-V only).
   Usage: ./shim_arm CODE.bin < input > output.   Build: cc -O2 shim_arm.c -o shim_arm.   UNPROVEN GLUE. */
#include <stdio.h>
#include <sys/mman.h>
#ifdef __APPLE__                             /* macOS: executable memory must be MAP_JIT, written with protection off */
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#else                                        /* Linux: nothing special */
enum { MAP_JIT = 0 };
static void pthread_jit_write_protect_np(int on) { (void)on; }
static void sys_icache_invalidate(void *p, long n) { __builtin___clear_cache((char *)p, (char *)p + n); }
#endif
enum { CODE = 4 << 20, IN = 1 << 20, OUT = 2 << 20, WORK = 80 << 20 };
static unsigned char in[IN + 1], out[OUT];                                      /* +1: detect too long */
static long work[WORK / 8] __attribute__((aligned(16)));                        /* AArch64: sp must be 16-aligned */

int main(int argc, char **argv) {
    FILE *f = argc == 2 ? fopen(argv[1], "rb") : 0;
    if (!f) return fprintf(stderr, "usage: shim_arm CODE.bin < input > output\n"), 2;
    unsigned char *code = mmap(0, CODE + 1, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT, -1, 0);
    if (code == MAP_FAILED) return fprintf(stderr, "shim_arm: the host refuses writable+executable memory\n"), 2;
    pthread_jit_write_protect_np(0);
    long code_len = fread(code, 1, CODE + 1, f), in_len = fread(in, 1, IN + 1, stdin);   /* limits: <= CODE, <= IN */
    if (code_len > CODE || in_len > IN) return fprintf(stderr, "shim_arm: code > 4 MiB or input > 2^20 bytes\n"), 2;
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(code, code_len);

    /* x0 input, x1 its length, x2 work base, x3 output, sp = work top, x30 = return; our sp waits in x19.
       x0..x17 and x30 may be overwritten by the code; x18 (reserved by macOS) must not be touched by it. */
    register long x0 __asm__("x0") = (long)in, x1 __asm__("x1") = in_len;
    register long x2 __asm__("x2") = (long)work, x3 __asm__("x3") = (long)out;
    long top = (long)work + WORK;
    __asm__ volatile("mov x19, sp\n mov sp, %[top]\n blr %[code]\n mov sp, x19"
        : "+r"(x0), "+r"(x1), "+r"(x2), "+r"(x3) : [top] "r"(top), [code] "r"(code)
        : "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17", "x19", "x30", "memory");

    fprintf(stderr, "shim_arm: status %ld, %ld output bytes\n", x0, x1);
    if ((x0 != 0 && x0 != 1) || x1 < 0 || x1 > OUT) return 1;
    if (fwrite(out, 1, x1, stdout) != (size_t)x1 || fclose(stdout)) return fprintf(stderr, "shim_arm: write failed\n"), 3;
    return 0;
}
