# Differential fuzzer: AArch64 cmp / cset / b.cond under qemu-aarch64 vs. intended formulas.
# Usage: python3 check_cmp.py <work_dir>
# Generates harness.c, builds it statically, runs it under qemu-aarch64-static, checks every case.
# (Written by the QF-CMP fuzz runner; committed by the lead. Result 2026-11-19: PASS, 201,280 cases.)
import os, random, subprocess, sys

M = 2**64
CONDS = ["eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc",
         "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"]
N_RANDOM = 100_000
SEED = 20260319

def to_signed(v):
    return v - M if v >= 2**63 else v

def flags(x, y):
    # cmp x, y  == subs xzr, x, y
    d = (x - y) % M
    N = d >> 63
    Z = int(d == 0)
    C = int(y <= x)
    sd = to_signed(x) - to_signed(y)
    V = int(not (-2**63 <= sd < 2**63))
    return N, Z, C, V

def cond_holds(i, N, Z, C, V):
    return [
        Z == 1, Z == 0, C == 1, C == 0, N == 1, N == 0, V == 1, V == 0,
        C == 1 and Z == 0, C == 0 or Z == 1, N == V, N != V,
        Z == 0 and N == V, Z == 1 or N != V, True, True,
    ][i]

def expected(x, y):
    N, Z, C, V = flags(x, y)
    nzcv = (N << 31) | (Z << 30) | (C << 29) | (V << 28)
    m = sum(int(cond_holds(i, N, Z, C, V)) << i for i in range(16))
    cs = m & 0x3FFF  # cset alias defined for 14 conditions (no al/nv)
    return nzcv, cs, m

# ---------- C harness generation ----------
def run_body(ins):
    out = ["    uint64_t r, t, m = 0, bm = 0;",
           '    __asm__ volatile("cmp %%1, %%2\\n\\tmrs %%0, nzcv" : "=&r"(r) : %s : "cc");' % ins]
    for i, c in enumerate(CONDS):
        if i < 14:  # GNU as rejects "cset ..., al/nv"; those two are covered by b.al/b.nv only
            out.append('    __asm__ volatile("cmp %%1, %%2\\n\\tcset %%0, %s" : "=&r"(t) : %s : "cc"); m |= t << %d;' % (c, ins, i))
        out.append('    __asm__ volatile("cmp %%1, %%2\\n\\tb.%s 1f\\n\\tmov %%0, #0\\n\\tb 2f\\n1:\\tmov %%0, #1\\n2:" : "=&r"(t) : %s : "cc"); bm |= t << %d;' % (c, ins, i))
    out.append("    o[0] = r; o[1] = m; o[2] = bm;")
    return "\n".join(out)

def make_c(imms):
    src = ['#include <stdio.h>', '#include <stdint.h>', '#include <stdlib.h>', '',
           'static void reg_run(uint64_t x, uint64_t y, uint64_t *o) {', run_body('"r"(x), "r"(y)'), '}', '']
    for k in imms:
        src += ['static void imm_%d(uint64_t x, uint64_t *o) {' % k, run_body('"r"(x), "I"(%d)' % k), '}', '']
    src += ['typedef void (*imm_fn)(uint64_t, uint64_t *);',
            'static imm_fn imm_tab[] = {' + ", ".join("imm_%d" % k for k in imms) + '};',
            'int main(void) {',
            '    char kind; unsigned long long a, b; uint64_t o[3];',
            '    while (scanf(" %c %llu %llu", &kind, &a, &b) == 3) {',
            "        if (kind == 'R') reg_run(a, b, o);",
            "        else if (kind == 'I') { if (b >= sizeof(imm_tab)/sizeof(imm_tab[0])) return 2; imm_tab[b](a, o); }",
            '        else return 3;',
            '        printf("%llu %llu %llu\\n", (unsigned long long)o[0], (unsigned long long)o[1], (unsigned long long)o[2]);',
            '    }', '    return 0;', '}', '']
    return "\n".join(src)

# ---------- case generation ----------
def edge_values():
    E = [0, 1, 2, 2**63 - 1, 2**63, 2**64 - 1, 2**63 + 1, 2**64 - 2, 2**32 - 1, 2**32]
    V = set(E)
    for e in E:
        V.add((e + 1) % M); V.add((e - 1) % M)
    return sorted(V)

def main():
    work = sys.argv[1]
    os.makedirs(work, exist_ok=True)
    rng = random.Random(SEED)
    E = edge_values()
    imms = [0, 1, 2, 3, 63, 64, 127, 128, 255, 256, 511, 512, 1023, 1024,
            2046, 2047, 2048, 2049, 4000, 4094, 4095]
    while len(imms) < 64:
        k = rng.randrange(4096)
        if k not in imms:
            imms.append(k)
    cases = []  # (line, x, y_or_imm_value)
    for x in E:
        for y in E:
            cases.append(("R %d %d" % (x, y), x, y))
        for k_idx, k in enumerate(imms):
            cases.append(("I %d %d" % (x, k_idx), x, k))
    for _ in range(N_RANDOM):
        x = rng.randrange(M)
        mode = rng.randrange(5)
        y = [rng.randrange(M), x, (x + 1) % M, (x - 1) % M, rng.randrange(2**12)][mode]
        cases.append(("R %d %d" % (x, y), x, y))
    for _ in range(N_RANDOM):
        x = rng.randrange(M) if rng.random() < 0.7 else rng.choice(E)
        k_idx = rng.randrange(len(imms))
        cases.append(("I %d %d" % (x, k_idx), x, imms[k_idx]))

    c_path = os.path.join(work, "harness.c")
    bin_path = os.path.join(work, "harness")
    with open(c_path, "w") as f:
        f.write(make_c(imms))
    subprocess.run(["aarch64-linux-gnu-gcc", "-O1", "-static", "-Wall", "-Werror", "-o", bin_path, c_path], check=True)

    inp = os.path.join(work, "cases.txt")
    with open(inp, "w") as f:
        f.write("\n".join(c[0] for c in cases) + "\n")
    res = subprocess.run(["qemu-aarch64-static", bin_path], stdin=open(inp), capture_output=True, text=True)
    assert res.returncode == 0, "harness exit %d: %s" % (res.returncode, res.stderr)
    got = res.stdout.split("\n")
    assert got[-1] == "", "missing trailing newline"
    got = got[:-1]
    assert len(got) == len(cases), "line count %d != %d" % (len(got), len(cases))

    bad = []
    per_cond_fail = [0] * 16
    for (line, x, y), g in zip(cases, got):
        nzcv, cs, bc = map(int, g.split())
        e_nzcv, e_cs, e_bc = expected(x, y)
        if (nzcv, cs, bc) != (e_nzcv, e_cs, e_bc):
            bad.append((line, x, y, (e_nzcv, e_cs, e_bc), (nzcv, cs, bc)))
            for i in range(16):
                if ((cs ^ e_cs) >> i) & 1 or ((bc ^ e_bc) >> i) & 1:
                    per_cond_fail[i] += 1

    n_reg = sum(1 for c in cases if c[0][0] == "R")
    print("cases: %d (reg cmp %d, imm cmp %d); edge values %d; imm forms %d" % (len(cases), n_reg, len(cases) - n_reg, len(E), len(imms)))
    if bad:
        print("MISMATCHES: %d" % len(bad))
        for line, x, y, exp, gotv in bad[:20]:
            print("  case x=%d y/imm=%d (%s): expected nzcv,cset,bcond=%s got=%s" % (x, y, line, exp, gotv))
        print("per-condition failure counts:", dict(zip(CONDS, per_cond_fail)))
    assert not bad, "%d mismatches" % len(bad)
    print("PASS: all %d cases match intended NZCV, cset (14 conds) and b.cond (16 conds)" % len(cases))

if __name__ == "__main__":
    main()
