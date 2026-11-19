/* shim_arm: the same shim for AArch64 (macOS on Apple Silicon, Linux).
 * FOR THE FUTURE ARM BACK END; UNTESTED: the compiler emits RISC-V only today, so there is no code this can run.
 * UNPROVEN GLUE, not part of any theorem.
 *   cc -O2 shim_arm.c -o shim_arm          (macOS: the binary needs the entitlement com.apple.security.cs.allow-jit
 *                                            when it is signed with the hardened runtime)
 *   shim_arm CODE.bin INPUT [work_MB] > OUTPUT        (INPUT "-" = stdin)
 * Convention (the RISC-V one moved to AArch64 registers): x0 input, x1 length, x2 work base (8-aligned), x3 output,
 * sp = work top (16-aligned, AArch64 requires it), x30 = return.  On return x0 = status, x1 = output length. */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#else
#define MAP_JIT 0
#endif

#define OUT_CAP (2L << 20)

static long slurp(const char *path, unsigned char *buf, long cap) {
    FILE *f = path[0] == '-' && !path[1] ? stdin : fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    long n = (long)fread(buf, 1, (size_t)cap + 1, f);
    assert(n <= cap && "file too large");
    return n;
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 4) { fprintf(stderr, "usage: shim_arm CODE.bin INPUT|- [work_MB] > OUTPUT\n"); return 2; }
    long work_len = (argc == 4 ? atol(argv[3]) : 80) << 20, code_cap = 4L << 20, in_cap = 1L << 20;
    /* macOS refuses writable+executable pages unless they are MAP_JIT; writing is then enabled per thread */
    unsigned char *code = mmap(0, (size_t)code_cap + 1, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT, -1, 0);
    unsigned char *input = malloc((size_t)in_cap + 1), *output = malloc(OUT_CAP);
    unsigned char *work = mmap(0, (size_t)work_len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(code != MAP_FAILED && work != MAP_FAILED && input && output);
#ifdef __APPLE__
    pthread_jit_write_protect_np(0);             /* this thread may write the JIT pages */
#endif
    long code_len = slurp(argv[1], code, code_cap), in_len = slurp(argv[2], input, in_cap);
    assert(code_len > 0 && code_len % 4 == 0);
#ifdef __APPLE__
    pthread_jit_write_protect_np(1);             /* back to executable */
    sys_icache_invalidate(code, (size_t)code_len);
#else
    __builtin___clear_cache((char *)code, (char *)code + code_len);
#endif

    register long x0 __asm__("x0") = (long)input, x1 __asm__("x1") = in_len;
    register long x2 __asm__("x2") = (long)work, x3 __asm__("x3") = (long)output;
    long top = (long)work + work_len, sp_after;
    /* the host sp waits in x19 (callee-saved; the future back end must keep x19..x29 and sp, as the RISC-V code keeps
       s0..s11 and sp).  x18 is the platform register on macOS: the back end must not touch it. */
    __asm__ volatile("mov x19, sp\n mov sp, %[top]\n blr %[code]\n mov %[spa], sp\n mov sp, x19"
        : [spa] "=&r"(sp_after), "+r"(x0), "+r"(x1), "+r"(x2), "+r"(x3)
        : [top] "r"(top), [code] "r"(code)
        : "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17", "x19", "x30", "memory");
    assert(sp_after == top && "the code did not restore sp");

    long status = x0, out_len = x1;
    fprintf(stderr, "shim_arm: x0 = %ld, x1 = %ld output bytes\n", status, out_len);
    if (status != 0 && status != 1) return 1;
    assert(out_len >= 0 && out_len <= OUT_CAP);
    assert(fwrite(output, 1, (size_t)out_len, stdout) == (size_t)out_len && fflush(stdout) == 0);
    return 0;
}
