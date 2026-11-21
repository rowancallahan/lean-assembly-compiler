/* nanorun: run code produced by the nano compiler C (RV64IM machine code) on any host, by interpretation.
 * UNPROVEN GLUE: not part of any theorem. See README.md.
 *
 *   cc -O2 nanorun.c -o nanorun
 *   nanorun CODE.bin INPUT OUTPUT [work_MB]
 *
 * CODE.bin: raw little-endian 32-bit instruction words (what the compiler writes).
 * Calling convention of the code (the one of the correctness theorem):
 *   a0 = input address, a1 = input length, a2 = work base (8-aligned), a3 = output address,
 *   sp = work top, ra = return address.  On return: a0 = status, a1 = output length.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define BASE 0x80000000ull          /* guest address of mem[0] (RAM start of the proved machine) */
#define CODE_OFF 0x1000ull          /* code starts here; mem[0..4) is the sentinel return address */
#define OUT_CAP (2ull << 20)        /* output block: the compiler never emits more than 1 MiB */

static uint8_t *mem;                /* one flat block: sentinel | code | input | output | work */
static uint64_t *prof;              /* NANORUN_PROF=file: executions per code word (uint64 array, written at exit) */
static uint64_t mem_size, code_end, out_off;

static void die(const char *what, uint64_t pc, uint32_t insn) {
    fprintf(stderr, "nanorun: TRAP: %s (pc = 0x%llx, instruction = 0x%08x)\n", what,
            (unsigned long long)pc, insn);
    exit(3);
}

/* INPUT file -> the input block at mem + off; returns its length */
static uint64_t load_input(const char *path, uint8_t **buf) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    assert(fseek(f, 0, SEEK_END) == 0);
    long n = ftell(f);
    assert(n >= 0);
    rewind(f);
    *buf = malloc((size_t)n + 1);
    assert(*buf);
    assert(fread(*buf, 1, (size_t)n, f) == (size_t)n);
    fclose(f);
    return (uint64_t)n;
}

static void write_output(const char *path, const uint8_t *ptr, uint64_t len) {
    FILE *f = fopen(path, "wb");
    if (!f) { perror(path); exit(2); }
    assert(fwrite(ptr, 1, (size_t)len, f) == (size_t)len);
    assert(fclose(f) == 0);
}

static inline uint64_t ld(uint64_t a, unsigned n, uint64_t pc, uint32_t insn) {
    uint64_t o = a - BASE, v = 0;
    if (a < BASE || o + n > mem_size) die("load outside memory", pc, insn);
    memcpy(&v, mem + o, n);         /* hosts are little-endian (x86-64, arm64) */
    return v;
}
static inline void st(uint64_t a, uint64_t v, unsigned n, uint64_t pc, uint32_t insn) {
    uint64_t o = a - BASE;
    if (a < BASE || o + n > mem_size) die("store outside memory", pc, insn);
    if (o < out_off) die("store into the code or the input block", pc, insn);
    memcpy(mem + o, &v, n);
}
static inline int64_t sx(uint64_t v, unsigned bits) { return (int64_t)(v << (64 - bits)) >> (64 - bits); }

int main(int argc, char **argv) {
    if (argc < 4 || argc > 5) {
        fprintf(stderr, "usage: nanorun CODE.bin INPUT OUTPUT [work_MB]\n");
        return 2;
    }
    { uint16_t one = 1; assert(*(uint8_t *)&one == 1 && "little-endian host required"); }
    uint8_t *code, *input;
    uint64_t code_len = load_input(argv[1], &code), in_len = load_input(argv[2], &input);
    uint64_t work_len = (argc == 5 ? strtoull(argv[4], 0, 10) : 80) << 20;
    assert(code_len % 4 == 0 && code_len > 0 && "CODE.bin must be non-empty 32-bit words");
    assert(in_len <= (1ull << 20) && "the compiler's contract covers inputs up to 2^20 bytes");
    assert(work_len >= 16);

    uint64_t in_off = (CODE_OFF + code_len + 15) & ~15ull;
    out_off = (in_off + in_len + 15) & ~15ull;
    uint64_t work_off = (out_off + OUT_CAP + 15) & ~15ull;
    mem_size = work_off + work_len;
    code_end = CODE_OFF + code_len;
    assert(BASE + mem_size <= 0x100000000ull && "memory must fit below 4 GiB (RAM of the proved machine)");
    mem = calloc(mem_size, 1);
    assert(mem && "out of host memory");
    memcpy(mem + CODE_OFF, code, code_len);
    memcpy(mem + in_off, input, in_len);

    uint64_t x[32] = {0};
    const uint64_t sentinel = BASE;                 /* ra: returning here ends the run */
    x[1] = sentinel;
    x[2] = BASE + work_off + work_len;              /* sp = work top */
    x[10] = BASE + in_off; x[11] = in_len;
    x[12] = BASE + work_off; x[13] = BASE + out_off;
    uint64_t pc = BASE + CODE_OFF, steps = 0;
    const char *prof_path = getenv("NANORUN_PROF");
    if (prof_path) { prof = calloc(code_len / 4, sizeof *prof); assert(prof && "out of host memory"); }

    while (pc != sentinel) {
        if (pc < BASE + CODE_OFF || pc >= BASE + code_end || (pc & 3)) die("pc outside the code", pc, 0);
        uint32_t i;
        memcpy(&i, mem + (pc - BASE), 4);
        uint32_t op = i & 0x7f, rd = (i >> 7) & 31, f3 = (i >> 12) & 7, rs1 = (i >> 15) & 31, rs2 = (i >> 20) & 31,
                 f7 = i >> 25;
        uint64_t a = x[rs1], b = x[rs2], r = 0, npc = pc + 4;
        int64_t immI = sx(i >> 20, 12);
        steps++;
        if (prof) prof[(pc - BASE - CODE_OFF) >> 2]++;
        switch (op) {
        case 0x37: r = (uint64_t)sx(i & 0xfffff000u, 32); break;                          /* LUI */
        case 0x17: r = pc + (uint64_t)sx(i & 0xfffff000u, 32); break;                     /* AUIPC */
        case 0x6f: {                                                                      /* JAL */
            uint64_t imm = ((i >> 31) << 20) | (((i >> 12) & 0xff) << 12) | (((i >> 20) & 1) << 11) | (((i >> 21) & 0x3ff) << 1);
            r = pc + 4; npc = pc + (uint64_t)sx(imm, 21); break; }
        case 0x67:                                                                        /* JALR */
            if (f3) die("unsupported instruction", pc, i);
            r = pc + 4; npc = (a + (uint64_t)immI) & ~1ull; break;
        case 0x63: {                                                                      /* branches */
            uint64_t imm = ((i >> 31) << 12) | (((i >> 7) & 1) << 11) | (((i >> 25) & 0x3f) << 5) | (((i >> 8) & 0xf) << 1);
            int t;
            switch (f3) {
            case 0: t = a == b; break; case 1: t = a != b; break;
            case 4: t = (int64_t)a < (int64_t)b; break; case 5: t = (int64_t)a >= (int64_t)b; break;
            case 6: t = a < b; break; case 7: t = a >= b; break;
            default: t = 0; die("unsupported instruction", pc, i);
            }
            if (t) npc = pc + (uint64_t)sx(imm, 13);
            rd = 0; break; }
        case 0x03: {                                                                      /* loads */
            uint64_t ad = a + (uint64_t)immI;
            switch (f3) {
            case 0: r = (uint64_t)sx(ld(ad, 1, pc, i), 8); break; case 1: r = (uint64_t)sx(ld(ad, 2, pc, i), 16); break;
            case 2: r = (uint64_t)sx(ld(ad, 4, pc, i), 32); break; case 3: r = ld(ad, 8, pc, i); break;
            case 4: r = ld(ad, 1, pc, i); break; case 5: r = ld(ad, 2, pc, i); break; case 6: r = ld(ad, 4, pc, i); break;
            default: die("unsupported instruction", pc, i);
            }
            break; }
        case 0x23: {                                                                      /* stores */
            uint64_t ad = a + (uint64_t)sx(((i >> 25) << 5) | ((i >> 7) & 31), 12);
            if (f3 > 3) die("unsupported instruction", pc, i);
            st(ad, b, 1u << f3, pc, i);
            rd = 0; break; }
        case 0x13:                                                                        /* register-immediate */
            switch (f3) {
            case 0: r = a + (uint64_t)immI; break;
            case 2: r = (int64_t)a < immI; break; case 3: r = a < (uint64_t)immI; break;
            case 4: r = a ^ (uint64_t)immI; break; case 6: r = a | (uint64_t)immI; break; case 7: r = a & (uint64_t)immI; break;
            case 1: if (i >> 26) die("unsupported instruction", pc, i); r = a << ((i >> 20) & 63); break;
            case 5:
                if ((i >> 26) == 0) r = a >> ((i >> 20) & 63);
                else if ((i >> 26) == 0x10) r = (uint64_t)((int64_t)a >> ((i >> 20) & 63));
                else die("unsupported instruction", pc, i);
                break;
            }
            break;
        case 0x1b: {                                                                      /* 32-bit register-immediate */
            uint32_t s = rs2;
            if (f3 == 0) r = (uint64_t)sx((uint32_t)(a + (uint64_t)immI), 32);
            else if (f3 == 1 && f7 == 0) r = (uint64_t)sx((uint32_t)a << s, 32);
            else if (f3 == 5 && f7 == 0) r = (uint64_t)sx((uint32_t)a >> s, 32);
            else if (f3 == 5 && f7 == 0x20) r = (uint64_t)(int64_t)((int32_t)a >> s);
            else die("unsupported instruction", pc, i);
            break; }
        case 0x33:                                                                        /* register-register */
            if (f7 == 0) {
                switch (f3) {
                case 0: r = a + b; break; case 1: r = a << (b & 63); break;
                case 2: r = (int64_t)a < (int64_t)b; break; case 3: r = a < b; break;
                case 4: r = a ^ b; break; case 5: r = a >> (b & 63); break; case 6: r = a | b; break; case 7: r = a & b; break;
                }
            } else if (f7 == 0x20 && f3 == 0) r = a - b;
            else if (f7 == 0x20 && f3 == 5) r = (uint64_t)((int64_t)a >> (b & 63));
            else if (f7 == 1) {                                                           /* M */
                switch (f3) {
                case 0: r = a * b; break;
                case 1: r = (uint64_t)(((__int128)(int64_t)a * (__int128)(int64_t)b) >> 64); break;
                case 2: r = (uint64_t)(((__int128)(int64_t)a * (__int128)(unsigned __int128)b) >> 64); break;
                case 3: r = (uint64_t)(((unsigned __int128)a * (unsigned __int128)b) >> 64); break;
                case 4: r = b == 0 ? ~0ull : ((int64_t)a == INT64_MIN && (int64_t)b == -1) ? a : (uint64_t)((int64_t)a / (int64_t)b); break;
                case 5: r = b == 0 ? ~0ull : a / b; break;
                case 6: r = b == 0 ? a : ((int64_t)a == INT64_MIN && (int64_t)b == -1) ? 0 : (uint64_t)((int64_t)a % (int64_t)b); break;
                case 7: r = b == 0 ? a : a % b; break;
                }
            } else die("unsupported instruction", pc, i);
            break;
        case 0x3b: {                                                                      /* 32-bit register-register */
            uint32_t a32 = (uint32_t)a, b32 = (uint32_t)b, s = b32 & 31;
            if (f7 == 0 && f3 == 0) r = (uint64_t)sx(a32 + b32, 32);
            else if (f7 == 0x20 && f3 == 0) r = (uint64_t)sx(a32 - b32, 32);
            else if (f7 == 0 && f3 == 1) r = (uint64_t)sx(a32 << s, 32);
            else if (f7 == 0 && f3 == 5) r = (uint64_t)sx(a32 >> s, 32);
            else if (f7 == 0x20 && f3 == 5) r = (uint64_t)(int64_t)((int32_t)a32 >> s);
            else if (f7 == 1 && f3 == 0) r = (uint64_t)sx(a32 * b32, 32);
            else if (f7 == 1 && f3 == 4) r = b32 == 0 ? ~0ull : ((int32_t)a32 == INT32_MIN && (int32_t)b32 == -1) ? (uint64_t)(int64_t)INT32_MIN : (uint64_t)(int64_t)((int32_t)a32 / (int32_t)b32);
            else if (f7 == 1 && f3 == 5) r = b32 == 0 ? ~0ull : (uint64_t)sx(a32 / b32, 32);
            else if (f7 == 1 && f3 == 6) r = b32 == 0 ? (uint64_t)sx(a32, 32) : ((int32_t)a32 == INT32_MIN && (int32_t)b32 == -1) ? 0 : (uint64_t)(int64_t)((int32_t)a32 % (int32_t)b32);
            else if (f7 == 1 && f3 == 7) r = b32 == 0 ? (uint64_t)sx(a32, 32) : (uint64_t)sx(a32 % b32, 32);
            else die("unsupported instruction", pc, i);
            break; }
        default:
            die("unsupported instruction (only RV64IM integer instructions are interpreted: no CSR, ecall, atomics, floating point, compressed)", pc, i);
        }
        if (rd) x[rd] = r;
        pc = npc;
    }

    if (prof) {
        FILE *pf = fopen(prof_path, "wb");
        if (!pf) { perror(prof_path); exit(2); }
        assert(fwrite(prof, sizeof *prof, code_len / 4, pf) == code_len / 4);
        assert(fclose(pf) == 0);
    }
    int64_t status = (int64_t)x[10];
    uint64_t out_len = x[11];
    const char *meaning = status == 0 ? "ok" : status == 1 ? "ok, empty output" : status == -1 ? "out of work memory"
                        : status == -2 ? "buffer capacity reached" : "unknown status";
    fprintf(stderr, "nanorun: a0 = %lld (%s), a1 = %llu output bytes, %llu instructions\n", (long long)status, meaning,
            (unsigned long long)out_len, (unsigned long long)steps);
    if (status == 0 || status == 1) {
        assert(out_len <= OUT_CAP && "output longer than the output block");
        write_output(argv[3], mem + out_off, out_len);
        return 0;
    }
    return 1;
}
