#!/usr/bin/env python3
"""Semantic differential for rv2arm on straight-line J blocks (no branches). Runs the RISC-V words under qemu-riscv64 and the
A64 output of the nano translator (nanorun on rv2arm_rv.bin) under qemu-aarch64. Both start from the same registers and
memory and dump the same registers (x1,x2,x5..x8,x10..x15,x28..x31) and the 8 KiB memory at 0x40000000.
Base register x5 = 0x40001000 and sp = 0x40001800 are never written by the generated code; memory accesses use 8-aligned
offsets for ld/sd (the premise of the proof notes). usage: sem.py WORKDIR SECONDS SEED"""
import os, random, shutil, subprocess, sys, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rvgen as gen

ARM = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
W, SECONDS, SEED = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
os.makedirs(W, exist_ok=True)
NANORUN = os.path.join(W, 'nanorun')
if not os.path.exists(NANORUN):
    subprocess.run(['cc', '-O2', os.path.join(ARM, '..', 'run', 'nanorun.c'), '-o', NANORUN], check=True)
RV_GCC, A64_GCC = 'riscv64-linux-gnu-gcc', 'aarch64-linux-gnu-gcc'
QRV, QA64 = shutil.which('qemu-riscv64-static'), shutil.which('qemu-aarch64-static')
M = [1, 2, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 28, 29, 30, 31]       # mapped RV regs the generator writes
D = M                                                                # dumped regs
RMAP = {0: 31, 1: 30, 2: 4, 5: 5, 6: 6, 7: 7, 8: 8, 10: 0, 11: 1, 12: 2, 13: 3, 14: 14, 15: 15, 28: 12, 29: 13, 30: 10, 31: 11}
BASE, SP, DUMP = 0x40001000, 0x40001800, 0x40002000
MEM_LEN, DUMP_LEN = 8192, 256

def make_state(rng):
    regs = [0] * 32
    for r in M: regs[r] = rng.getrandbits(64)
    regs[5], regs[2] = BASE, SP
    mem = bytes(rng.getrandbits(8) for _ in range(MEM_LEN))
    return regs, mem

def write_state(d, regs):
    with open(os.path.join(d, 'state.s'), 'w') as f:
        f.write('    .section .data\n    .globl state\n    .p2align 3\nstate:\n')
        for r in range(32): f.write(f'    .quad {regs[r]:#x}\n')

def rv_asm(d, words):
    L = ['    .section .text', '    .globl _start', '_start:', '    la x9, state']
    L += [f'    ld x{r}, {8 * r}(x9)' for r in range(1, 32) if r != 9]
    L += [f'    .word {w:#010x}' for w in words]
    L += [f'    li x9, {DUMP:#x}'] + [f'    sd x{r}, {8 * k}(x9)' for k, r in enumerate(D)]
    L += [f'    li a7, 64', f'    li a0, 1', f'    li a1, 0x40000000', f'    li a2, {MEM_LEN + DUMP_LEN}', '    ecall',
          '    li a7, 93', '    li a0, 0', '    ecall']
    open(os.path.join(d, 'rv.s'), 'w').write('\n'.join(L) + '\n')

def a64_asm(d, words):
    L = ['    .text', '    .globl _start', '_start:', '    adr x9, state']
    L += [f'    ldr x{RMAP[r]}, [x9, #{8 * r}]' for r in M]
    L += [f'    .inst {w:#010x}' for w in words]
    L += [f'    ldr x9, =0x{DUMP:x}']
    for k, r in enumerate(D): L.append(f'    str x{RMAP[r]}, [x9, #{8 * k}]')
    L += [f'    mov x8, #64', f'    mov x0, #1', f'    ldr x1, =0x40000000', f'    mov x2, #{MEM_LEN + DUMP_LEN}', '    svc #0',
          '    mov x8, #93', '    mov x0, #0', '    svc #0']
    open(os.path.join(d, 'a64.s'), 'w').write('\n'.join(L) + '\n')

def build_run(d, asm, gcc, qemu, out):
    subprocess.run([gcc, '-nostdlib', '-static', '-Wl,--section-start=.mem=0x40000000', '-o', out + '.elf',
                    out + '.s', 'state.s', 'mem.s'], check=True, cwd=d)
    r = subprocess.run([qemu, out + '.elf'], cwd=d, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    return r.returncode, r.stdout

SHIM_RV = os.path.join(W, 'shim_rv')
if not os.path.exists(SHIM_RV):
    subprocess.run(['riscv64-linux-gnu-gcc', '-O2', '-static', os.path.join(ARM, '..', 'run', 'shim', 'shim_rv.c'), '-o', SHIM_RV], check=True)

def translate(d, rvbin):
    # RISC-V translator under qemu-riscv64 + shim_rv (the reference)
    env = dict(os.environ, RUN=f'{shutil.which("qemu-riscv64-static")} {SHIM_RV} {os.path.join(ARM, "rv2arm_rv.bin")}')
    return subprocess.run(['sh', os.path.join(ARM, 'rv2arm.sh'), rvbin], env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.DEVNULL).stdout

def mem_s(d, mem):
    open(os.path.join(d, 'mem.bin'), 'wb').write(mem + bytes(DUMP_LEN))
    open(os.path.join(d, 'mem.s'), 'w').write('    .section .mem,"aw"\n    .globl memarea\nmemarea:\n    .incbin "mem.bin"\n')

def check(d, words, regs, mem):
    """Returns None if equal, else a short description."""
    write_state(d, regs); mem_s(d, mem)
    rvbin = os.path.join(d, 'prog.rv')
    open(rvbin, 'wb').write(b''.join((w & 0xFFFFFFFF).to_bytes(4, 'little') for w in words))
    a64 = translate(d, rvbin)
    if len(a64) != 16 * len(words): return f'translation size {len(a64)} for {len(words)} words'
    a64w = [int.from_bytes(a64[i:i + 4], 'little') for i in range(0, len(a64), 4)]
    rv_asm(d, words); a64_asm(d, a64w)
    rc1, o1 = build_run(d, 'rv', RV_GCC, QRV, 'rv')
    rc2, o2 = build_run(d, 'a64', A64_GCC, QA64, 'a64')
    if rc1 != 0 or rc2 != 0: return f'exit codes rv={rc1} a64={rc2}'
    if o1 != o2:
        diff = [i for i in range(len(o1)) if o1[i] != o2[i]]
        return f'dump differs at {len(diff)} bytes, first at offset {diff[0]}'
    return None

def gen_ctl(rng):
    """Straight-line words with forward-only conditional branches (beq/bne/bltu/bgeu, incl. x0 operands). Targets are
    forward, so every run ends; a final addi x0,x0,0 is the target sink (the translator refuses targets == n)."""
    k = rng.choice([3, 6, 12, 24])
    words = []
    for i in range(k):
        if rng.random() < 0.4:
            t = rng.randint(i + 1, k)
            words.append(gen.B(rng.choice(gen.BR), rng.choice(gen.SRC), rng.choice(gen.SRC), 4 * (t - i)))
        else:
            words.append(gen.valid_word(rng, i, k + 1, straight=True))
    return words + [gen.I(0x13, 0, 0, 0, 0)]

def main():
    rng = random.Random(SEED)
    ctl = len(sys.argv) > 4 and sys.argv[4] == 'ctl'
    t0 = time.time(); n_ok = 0; nfail = 0; seen = set(); d = os.path.join(W, 'd'); os.makedirs(d, exist_ok=True)
    while time.time() - t0 < SECONDS:
        if ctl: words = gen_ctl(rng)
        else:
            k = rng.choice([1, 2, 4, 8, 16, 32])
            words = [gen.valid_word(rng, i, k, straight=True) for i in range(k)]
        regs, mem = make_state(rng)
        msg = check(d, words, regs, mem)
        if msg is None: n_ok += 1; continue
        nfail += 1
        key = msg.split(' at ')[0].split(' for ')[0]
        if key in seen: continue
        seen.add(key)
        print(json.dumps({'semantic_mismatch': msg, 'words_hex': [f'{w & 0xFFFFFFFF:08x}' for w in words], 'seed': SEED}), flush=True)
    print(json.dumps({'sem_summary': True, 'ok': n_ok, 'fails': nfail, 'seconds': round(time.time() - t0)}), flush=True)

if __name__ == '__main__':
    main()
