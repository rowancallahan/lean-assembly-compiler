#!/usr/bin/env python3
"""ARM path of the whole-program fuzzer (unproven glue; reuses nanogen.py and nanofuzz.mutate).

usage: armfuzz.py SEED N WORKDIR [MUT=0.5]
For each generated (or mutated) program, with edge-biased inputs:
  1. B2 compiles it under nanorun (B2.bin).  Accepted: the RISC-V code runs under qemu-riscv64 (shim_rv) and nanorun;
     both must agree on status and output bytes.
  2. The nano translator (arm/rv2arm.sh, RUN = qemu-aarch64 + shim_arm + rv2arm_arm.bin) translates the RISC-V code;
     the result must equal arm/rv2arm.py (oracle).  The ARM code runs under qemu-aarch64 + shim_arm: status and output
     bytes must equal the RISC-V run.
  3. ARM-B2 (arm/B2_arm.bin under qemu-aarch64 + shim_arm) compiles the same text: its code must equal B2's code
     (also for rejected programs: empty).
Mismatches are written to WORKDIR/mismatch/ (program + input) and counted; the run continues.
Needs: aarch64-linux-gnu-gcc, riscv64-linux-gnu-gcc, qemu-aarch64-static, qemu-riscv64-static, python3."""
import os, re, sys, random, subprocess, shutil, collections

HERE = os.path.dirname(os.path.abspath(__file__))
V2 = os.path.abspath(os.path.join(HERE, '..'))
ARM = os.path.join(V2, 'arm')
SEED, N, WORK = int(sys.argv[1]), int(sys.argv[2]), os.path.abspath(sys.argv[3])
MUT = float(sys.argv[4]) if len(sys.argv) > 4 else 0.5
BIG = os.environ.get('BIG') == '1'   # far-address mode: big buffers (nanobig.py), inputs up to 4 KB for the reference
R = random.Random(SEED)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nanobig

# nanofuzz reads its arguments at import; give it neutral ones, then use its mutate() and B2 helpers
_argv = sys.argv
sys.argv = ['nanofuzz', '0', '0', WORK]
sys.path.insert(0, HERE)
import nanofuzz as nf
sys.argv = _argv
nf.R = R
nf.WORK = WORK

def status_of(err):
    m = re.search(r'(?:a0 = |status )(-?\d+)', err)
    return int(m.group(1)) if m else None

def edge_inputs():
    """empty, 1 byte, 0x00/0xFF, mixed, deep (fuel-sized), and one long input (> 64 KB) with probability 1/4"""
    ins = [b'', b'\x00', b'\xff', b'\x01', bytes([0xff] * 37), bytes(range(256)) * 2]
    ins.append(bytes(R.randrange(256) for _ in range(R.choice([2, 3, 5, 8, 13, 40, 255]))))
    if BIG:
        ins.append(bytes(R.randrange(256) for _ in range(R.randrange(1000, 4001))))
    if R.random() < 0.25:
        ins.append(bytes(R.randrange(256) for _ in range(65536 + R.randrange(0, 4096))))
    return ins

def run_q(qemu, shim, code, inp_bytes, tag):
    """qemu shim run: status and output bytes (or None status on crash)"""
    ip = os.path.join(WORK, tag + '.in'); op = os.path.join(WORK, tag + '.out')
    with open(ip, 'wb') as f: f.write(inp_bytes)
    with open(ip, 'rb') as fi, open(op, 'wb') as fo:
        p = subprocess.run([*qemu, shim, code], stdin=fi, stdout=fo, stderr=subprocess.PIPE, text=True)
    return status_of(p.stderr), (open(op, 'rb').read() if status_of(p.stderr) in (0, 1) else None)

def nano_run(bn, inp_bytes, tag):
    ip = os.path.join(WORK, tag + '.in'); op = os.path.join(WORK, tag + '.out')
    with open(ip, 'wb') as f: f.write(inp_bytes)
    p = subprocess.run([os.path.join(WORK, 'nanorun'), bn, ip, op], capture_output=True, text=True)
    st = status_of(p.stderr)
    return st, (open(op, 'rb').read() if st in (0, 1) else None)

def main():
    shutil.rmtree(WORK, ignore_errors=True); os.makedirs(os.path.join(WORK, 'mismatch'))
    gdir = os.path.join(WORK, 'gen')
    subprocess.run([sys.executable, os.path.join(HERE, 'nanogen.py'), str(SEED), str(N), gdir], check=True)
    for tool in (['cc', '-O2', os.path.join(V2, 'run/nanorun.c'), '-o', os.path.join(WORK, 'nanorun')],
                 ['aarch64-linux-gnu-gcc', '-O2', '-static', os.path.join(V2, 'run/shim/shim_arm.c'), '-o', os.path.join(WORK, 'shim_arm')],
                 ['riscv64-linux-gnu-gcc', '-O2', '-static', os.path.join(V2, 'run/shim/shim_rv.c'), '-o', os.path.join(WORK, 'shim_rv')]):
        subprocess.run(tool, check=True)
    QA = ['qemu-aarch64-static']; QR = ['qemu-riscv64-static']
    SA = os.path.join(WORK, 'shim_arm'); SR = os.path.join(WORK, 'shim_rv')
    B2ARM = os.path.join(ARM, 'B2_arm.bin')
    cnt = collections.Counter(); mism = []

    def record(kind, name, detail, files):
        cnt['MISMATCH ' + kind] += 1
        mism.append((name, kind, detail))
        for suffix, data in files.items():
            with open(os.path.join(WORK, 'mismatch', name + suffix), 'wb') as f: f.write(data)

    # pass 1: generate, B2 compile, ARM-B2 compile (accepted and rejected)
    acc = []   # (name, text, b2 bin path, inputs)
    for i in range(N):
        text = open(os.path.join(gdir, f'g{i}.src')).read()
        name = f'g{i}'
        if BIG and R.random() < 0.8:
            text = nanobig.program(R); name = f'b{i}'
        elif R.random() < MUT:
            text = nf.mutate(text); name = f'm{i}'
        if R.random() < 0.3:   # deep recursion: large fuel numeral in the entry
            text = re.sub(r"(:= \w+ )(\(len' x\)|\d+)( x 0 \[\])", lambda mm: mm.group(1) + str(R.randrange(100, 256)) + mm.group(3), text)
        src = os.path.join(WORK, name + '.lean')
        with open(src, 'w') as f: f.write(text)
        cnt['programs'] += 1
        b2_out = os.path.join(WORK, name + '.bin')
        cs, _ = nf.b2_compile(name, text)
        code = open(b2_out, 'rb').read() if os.path.exists(b2_out) else b''
        ab = os.path.join(WORK, name + '.armb2.bin')
        subprocess.run([*QA, SA, B2ARM], stdin=open(src, 'rb'), stdout=open(ab, 'wb'), stderr=subprocess.PIPE, text=True)
        armb2 = open(ab, 'rb').read()
        if armb2 == code: cnt['ARM-B2 == B2 code'] += 1
        else: record('ARM-B2 code', name, 'B2 vs ARM-B2 code differ', {'.src': text.encode(), '.b2.bin': code, '.armb2.bin': armb2})
        if cs != 'acc':
            cnt['b2 rejects'] += 1
            continue
        cnt['b2 accepts'] += 1
        acc.append((name, text, b2_out, edge_inputs()))

    # pass 2: reference (semrun pipeline) on the inputs of at most 4 KB; longer inputs are ARM-vs-RV only
    short_of = {nm: [(k, inp) for k, inp in enumerate(ins) if len(inp) <= 4096] for nm, _, _, ins in acc}
    for nm, _, _, ins in acc:
        for j, (k, inp) in enumerate(short_of[nm]):
            with open(os.path.join(WORK, f'{nm}.in{j}'), 'wb') as f: f.write(inp)
    refs = nf.ref_batch([nm for nm, _, _, _ in acc], {nm: [inp for _, inp in short_of[nm]] for nm in short_of}) if acc else {}

    # pass 3: RISC-V (qemu, nanorun) and ARM (translator, qemu) against the reference and each other
    for name, text, b2_out, inputs in acc:
        for j, (k, inp) in enumerate(short_of[name]):
            rst, rout = refs[(name, j)]
            refok = rst == 'OK'
            rs, ro = nano_run(b2_out, inp, f'{name}.n{k}')
            qs, qo = run_q(QR, SR, b2_out, inp, f'{name}.q{k}')
            if refok and qs == -1 and (rs, ro) == (qs, qo):   # resource limit at 80 MiB: not compared to the reference
                cnt['rv oom at 80 MiB (ref OK; nanorun agrees)'] += 1
                continue
            ok = (qs, qo) == (rs, ro) and ((refok and qs in (0, 1) and qo == rout) or (not refok and qs not in (0, 1)))
            if ok: cnt['rv qemu == ref'] += 1
            else: record('rv qemu vs ref', name, f'input {k} ({len(inp)} B): ref {rst}, qemu {qs}, nanorun {rs}', {'.bin': open(b2_out, 'rb').read(), f'.in{k}': inp})
        armbin = os.path.join(WORK, name + '.arm.bin')
        env = dict(os.environ, RUN=f"qemu-aarch64-static {SA} {ARM}/rv2arm_arm.bin")
        tr = subprocess.run(['sh', os.path.join(ARM, 'rv2arm.sh'), b2_out], env=env, capture_output=True)
        if tr.returncode != 0:
            record('translate failed', name, tr.stderr.decode()[-300:], {'.bin': open(b2_out, 'rb').read()}); continue
        open(armbin, 'wb').write(tr.stdout)
        orc = subprocess.run([sys.executable, os.path.join(ARM, 'rv2arm.py'), b2_out], capture_output=True)
        if orc.stdout == tr.stdout: cnt['translator == oracle'] += 1
        else: record('translator != oracle', name, 'rv2arm.sh output differs from rv2arm.py', {'.bin': open(b2_out, 'rb').read()})
        for k, inp in enumerate(inputs):
            rs, ro = nano_run(b2_out, inp, f'{name}.n{k}')
            as_, ao = run_q(QA, SA, armbin, inp, f'{name}.a{k}')
            if (rs, ro) == (as_, ao): cnt['arm run == rv run'] += 1
            else: record('arm run vs rv run', name, f'input {k} ({len(inp)} B): rv {rs}, arm {as_}', {'.arm.bin': open(armbin, 'rb').read(), f'.in{k}': inp})
            if len(inp) > 4096: continue
            j = [kk for kk, _ in short_of[name]].index(k)
            rst, rout = refs[(name, j)]
            if rst == 'OK' and as_ == -1:
                cnt['arm oom at 80 MiB (ref OK; rv agrees)'] += 1
                continue
            if rst == 'OK':
                ok = as_ in (0, 1) and ao == rout
            else:
                ok = as_ not in (0, 1)
            if ok: cnt['arm == ref'] += 1
            else: record('arm vs ref', name, f'input {k}: ref {rst}, arm {as_}', {'.arm.bin': open(armbin, 'rb').read(), f'.in{k}': inp})
    with open(os.path.join(WORK, 'summary.txt'), 'w') as f:
        f.write(f'seed={SEED} programs={cnt["programs"]} b2_accepts={cnt["b2 accepts"]} b2_rejects={cnt["b2 rejects"]}\n')
        for k, v in sorted(cnt.items()):
            if k not in ('programs', 'b2 accepts', 'b2 rejects'): f.write(f'{v:7d}  {k}\n')
        f.write(f'mismatches={sum(v for k, v in cnt.items() if k.startswith("MISMATCH"))}\n')
        for name, kind, detail in mism: f.write(f'  {name}: {kind}: {detail}\n')
    print(open(os.path.join(WORK, 'summary.txt')).read())

if __name__ == '__main__':
    main()
