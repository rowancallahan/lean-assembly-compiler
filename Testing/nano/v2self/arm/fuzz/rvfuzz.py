#!/usr/bin/env python3
"""Differential fuzzer for rv2arm (UNPROVEN glue). Per input: rv2arm.py (oracle) vs rv2arm.sh+nanorun on rv2arm_rv.bin
vs rv2arm.sh+qemu-aarch64 on rv2arm_arm.bin. Checks: byte equality; empty output iff oracle refuses; every A64 word is in
the minimal set (mask table + objdump), x18..x29 and sp never written, branch targets on block starts.
usage: fuzz.py WORKDIR SECONDS SEED [FAILDIR]     (prints one JSON line per mismatch signature, and a count line)"""
import json, os, random, shutil, struct, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rvgen as gen

ARM = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NANO_SRC = os.path.join(ARM, '..', 'run', 'nanorun.c')
SHIM_SRC = os.path.join(ARM, '..', 'run', 'shim', 'shim_arm.c')
W, SECONDS, SEED = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
FAILDIR = sys.argv[4] if len(sys.argv) > 4 else os.path.join(W, 'fail')
os.makedirs(W, exist_ok=True); os.makedirs(FAILDIR, exist_ok=True)
NANORUN, SHIM, SHIM_RV = os.path.join(W, 'nanorun'), os.path.join(W, 'shim_arm'), os.path.join(W, 'shim_rv')
if not os.path.exists(NANORUN):
    subprocess.run(['cc', '-O2', NANO_SRC, '-o', NANORUN], check=True)
if not os.path.exists(SHIM):
    subprocess.run(['aarch64-linux-gnu-gcc', '-O2', '-static', SHIM_SRC, '-o', SHIM], check=True)
if not os.path.exists(SHIM_RV):
    subprocess.run(['riscv64-linux-gnu-gcc', '-O2', '-static', os.path.join(ARM, '..', 'run', 'shim', 'shim_rv.c'), '-o', SHIM_RV], check=True)
QEMU_RV = shutil.which('qemu-riscv64-static') or shutil.which('qemu-riscv64')
QEMU = shutil.which('qemu-aarch64-static') or shutil.which('qemu-aarch64')
CASE = os.path.join(W, 'case.rv')

# minimal A64 set (README table): (mask, value, name, dest kind). dest: 'imm' = Rd written, sp-forbidden; 'reg' = Rd, xzr ok;
# 'none'; 'bl' (writes x30); 'br'; 'bc'; 'b'.
MASKS = [
    (0xFFE00000, 0xD2800000, 'movz', 'reg'), (0xFF800000, 0x91000000, 'add-imm', 'imm'), (0xFF800000, 0xD1000000, 'sub-imm', 'imm'),
    (0xFFE0FC00, 0x8B000000, 'add', 'reg'), (0xFFE0FC00, 0xCB000000, 'sub', 'reg'), (0xFFE0FC00, 0xEB000000, 'cmp', 'cmp'),
    (0xFFE0FC00, 0x8A000000, 'and', 'reg'), (0xFFE0FC00, 0xAA000000, 'orr', 'reg'), (0xFFE0FC00, 0xCA000000, 'eor', 'reg'),
    (0xFFE0FC00, 0x9AC02000, 'lslv', 'reg'), (0xFFE0FC00, 0x9AC02400, 'lsrv', 'reg'), (0xFFE08000, 0x9B000000, 'madd', 'reg'),
    (0xFFC00000, 0xF9400000, 'ldr', 'reg'), (0xFFC00000, 0xF9000000, 'str', 'none'),
(0xFFC00000, 0x39400000, 'ldrb', 'reg'), (0xFFC00000, 0x39000000, 'strb', 'none'),
    (0xFC000000, 0x14000000, 'b', 'b'), (0xFC000000, 0x94000000, 'bl', 'bl'), (0xFF000010, 0x54000000, 'b.cond', 'bc'),
    (0xFFFFFC1F, 0xD61F0000, 'br', 'none'), (0xFF800000, 0xF2800000, 'movk', 'reg'), (0xFF000000, 0xB4000000, 'cbz', 'cbz'),
]
OBJ_OK = {'mov', 'add', 'sub', 'neg', 'and', 'orr', 'eor', 'lsl', 'lsr', 'mul', 'cmp', 'b', 'bl', 'br', 'ldr', 'str', 'ldur',
          'ldrb', 'strb', 'b.eq', 'b.ne', 'b.cs', 'b.cc', 'b.hs', 'b.lo', 'movk', 'cbz'}

# register fields (bit positions of Rd / Rn / Rm / Rt / Ra) per class: none may be 31 (no xzr, no sp)
FIELDS = {'movz': (0,), 'movk': (0,), 'add-imm': (0, 5), 'sub-imm': (0, 5), 'add': (0, 5, 16), 'sub': (0, 5, 16),
          'cmp': (5, 16), 'and': (0, 5, 16), 'orr': (0, 5, 16), 'eor': (0, 5, 16), 'lslv': (0, 5, 16), 'lsrv': (0, 5, 16),
          'madd': (0, 5, 16, 10), 'ldr': (0, 5), 'str': (0, 5), 'ldrb': (0, 5), 'strb': (0, 5), 'cbz': (0,), 'br': (5,)}

def sx(v, bits): return v - (1 << bits) if v >> (bits - 1) & 1 else v

def run(cmd, env=None):
    p = subprocess.run(cmd, input=None, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env)
    return p.returncode, p.stdout

def translators(data):
    with open(CASE, 'wb') as f: f.write(data)
    rc_o, out_o = run(['python3', os.path.join(ARM, 'rv2arm.py'), CASE])
    env = dict(os.environ)
    env['RUN'] = f'{QEMU_RV} {SHIM_RV} {os.path.join(ARM, "rv2arm_rv.bin")}'          # RISC-V reference
    rc_r, out_r = run(['sh', os.path.join(ARM, 'rv2arm.sh'), CASE], env)
    env['RUN'] = f'{QEMU} {SHIM} {os.path.join(ARM, "rv2arm_arm.bin")}'               # the A64 translator under qemu
    rc_q, out_q = run(['sh', os.path.join(ARM, 'rv2arm.sh'), CASE], env)
    env['RUN'] = f'{NANORUN} {os.path.join(ARM, "rv2arm_rv.bin")} /dev/stdin /dev/stdout'   # third opinion
    rc_n, out_n = run(['sh', os.path.join(ARM, 'rv2arm.sh'), CASE], env)
    return (rc_o, out_o), (rc_r, out_r), (rc_q, out_q), (rc_n, out_n)

def objcheck(o):
    """Returns a list of violations of the A64 output rules (empty = OK)."""
    bad = []
    if len(o) % 16: return ['size not a multiple of a 4-word block']
    ws = struct.unpack('<%dI' % (len(o) // 4), o)
    for idx, w in enumerate(ws):
        name = dest = None
        for m, v, nm, dk in MASKS:
            if w & m == v: name, dest = nm, dk; break
        if name is None: bad.append(f'word {idx}: {w:08x} not in minimal set'); continue
        rd = w & 31
        if dest in ('imm', 'reg') and name not in ('str', 'strb', 'stur') and 18 <= rd <= 29:
            bad.append(f'word {idx}: {name} writes x{rd}')
        for sh in FIELDS.get(name, ()):
            if w >> sh & 31 == 31: bad.append(f'word {idx}: {name} field at bit {sh} is 31 (xzr or sp)')
        if name == 'madd' and (w >> 10 & 31) != 17: bad.append(f'word {idx}: madd addend not x17')
        if name == 'madd' and (idx == 0 or ws[idx - 1] != 0xD2800011):
            bad.append(f'word {idx}: madd without movz x17,#0 just before')
        if dest in ('b', 'bl', 'bc', 'cbz'):
            imm = sx((w >> 5 & 0x7FFFF) if dest in ('bc', 'cbz') else (w & 0x3FFFFFF), 19 if dest in ('bc', 'cbz') else 26)
            if dest == 'bc' and (w & 15) > 3: bad.append(f'word {idx}: b.cond cond {w & 15}')
            tgt = 4 * idx + 4 * imm
            if tgt % 16 or not 0 <= tgt < len(o): bad.append(f'word {idx}: branch to {tgt} (not a block start in range)')
    p = subprocess.run(['aarch64-linux-gnu-objdump', '-D', '-b', 'binary', '-m', 'aarch64', '-'], input=o, stdout=subprocess.PIPE,
                       stderr=subprocess.DEVNULL)
    for line in p.stdout.decode().splitlines():
        parts = line.split('\t')
        if len(parts) >= 3 and ':' in parts[0]:
            mn = parts[2].split()[0] if parts[2].split() else ''
            if mn not in OBJ_OK: bad.append(f'objdump mnemonic {mn!r}')
    return bad

def check(data):
    """Returns (signature or None, detail)."""
    (rc_o, o), (rc_r, r), (rc_q, q), (rc_n, n) = translators(data)
    if rc_o == 0:
        for name, out in (('rvref-qemu', r), ('arm-qemu', q), ('nanorun', n)):
            if out != o: return f'{name}!=oracle', f'{name} {len(out)} B vs oracle {len(o)} B'
        bad = objcheck(o)
        if bad: return 'objcheck', '; '.join(bad[:3])
        return None, ''
    if r or q or n: return 'oracle-refuses-but-emits', f'rvref {len(r)} B, arm-qemu {len(q)} B, nanorun {len(n)} B'
    return None, ''

def minimize(data, sig):
    words = [data[i:i + 4] for i in range(0, len(data) - len(data) % 4, 4)]
    tail = data[len(data) - len(data) % 4:]
    changed = True
    while changed and len(words) > 1:
        changed = False
        for i in range(len(words)):
            t = words[:i] + words[i + 1:]
            if check(b''.join(t) + tail)[0] == sig:
                words = t; changed = True; break
    return b''.join(words) + tail

def main():
    rng = random.Random(SEED)
    counts = {}; seen = set(); t0 = time.time(); iters = 0; nfail = 0
    kinds = [('valid', 45), ('mutant', 25), ('random', 10), ('invalid1', 12), ('odd', 4), ('empty', 2), ('chunk', 0.25)]
    while time.time() - t0 < SECONDS:
        iters += 1
        kind = rng.choices([k for k, _ in kinds], [w for _, w in kinds])[0]
        n = 32000 + rng.choice([-1, 0, 1, 32000]) if kind == 'chunk' else None
        if kind == 'chunk': n = rng.choice([31999, 32000, 32001, 64000, 64001])
        label, data = gen.case(rng, kind, n)
        sig, detail = check(data)
        counts[label] = counts.get(label, 0) + 1
        if sig is None: continue
        nfail += 1
        small = minimize(data, sig) if len(data) < 4096 else data
        ws = [int.from_bytes(small[i:i + 4], 'little') for i in range(0, len(small) - 3, 4)]
        key = sig + '|' + ','.join(sorted({f'{w & 127:02x}/{w >> 12 & 7}' for w in ws}))
        if key in seen:
            counts['dup'] = counts.get('dup', 0) + 1; continue
        seen.add(key)
        sig2, detail2 = check(small)
        path = os.path.join(FAILDIR, f'{sig.replace("!=", "_ne_").replace("/", "_")}_{SEED}_{iters}.rv')
        with open(path, 'wb') as f: f.write(small)
        print(json.dumps({'mismatch': sig, 'detail': detail2 or detail, 'minimal_words_hex': [f'{w:08x}' for w in ws],
                          'file': path, 'seed': SEED, 'iter': iters}), flush=True)
    print(json.dumps({'summary': True, 'iters': iters, 'fails': nfail, 'distinct_keys': len(seen), 'by_kind': counts,
                      'seconds': round(time.time() - t0)}), flush=True)

if __name__ == '__main__':
    main()
