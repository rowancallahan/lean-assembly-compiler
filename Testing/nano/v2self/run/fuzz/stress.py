#!/usr/bin/env python3
"""I/O and limit stress for shim_rv / shim_arm against nanorun (UNPROVEN glue). Prints one line per check: OK or DIFF.

usage: stress.py SELF_DIR WORK_DIR        (build WORK_DIR first with build.sh)
"""
import hashlib, os, random, re, subprocess, sys, threading, time
from pathlib import Path

V, W = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
B2, TRANSLATOR, RV2ARM = V / 'B2.bin', V / 'arm' / 'rv2arm_arm.bin', V / 'arm' / 'rv2arm.sh'
CAP = 1 << 20
ENV = dict(os.environ, ASAN_OPTIONS='detect_leaks=0')
NR = [str(W / 'nanorun_asan')]
RV = ['qemu-riscv64-static', str(W / 'shim_rv')]
RV_1M = ['qemu-riscv64-static', str(W / 'shim_rv_1M')]
ARM = ['qemu-aarch64-static', str(W / 'shim_arm')]
T = W / 'stress'
T.mkdir(exist_ok=True)
fails = 0


def status(err):
    assert 'Sanitizer' not in err and 'runtime error' not in err, err[:500]
    m = re.search(r'(?:a0 = |status )(-?\d+)', err)
    return int(m.group(1)) if m else None


def check(name, ok, detail=''):
    global fails
    fails += 0 if ok else 1
    print(('OK   ' if ok else 'DIFF ') + name + (f'  [{detail}]' if detail else ''), flush=True)


def run_pipe(cmd, data, chunked=False, seed=0):
    """stdin through a pipe; a writer thread sends random chunks with short random sleeps."""
    p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=ENV)

    def writer():
        r = random.Random(seed)
        i = 0
        while i < len(data):
            k = r.randint(1, 4096) if chunked else len(data)
            p.stdin.write(data[i:i + k]); p.stdin.flush(); i += k
            time.sleep(r.random() * 0.002 if chunked else 0)
        p.stdin.close()

    t = threading.Thread(target=writer); t.start()
    out, err = p.stdout.read(), p.stderr.read()
    t.join(); p.wait()
    return p.returncode, out, status(err.decode(errors='replace'))


def run_file(cmd, path):
    p = subprocess.run(cmd, stdin=open(path, 'rb'), capture_output=True, env=ENV)
    return p.returncode, p.stdout, status(p.stderr.decode(errors='replace'))


def nano(code, inp_path):
    out = T / 'nr.out'; out.unlink(missing_ok=True)
    p = subprocess.run(NR + [str(code), str(inp_path), str(out)], capture_output=True, env=ENV)
    return p.returncode, status(p.stderr.decode(errors='replace')), out.read_bytes() if out.exists() else None


def compile_nano(src_bytes, name):
    s = T / f'{name}.src'; s.write_bytes(src_bytes)
    c = T / f'{name}.rv'; c.unlink(missing_ok=True)
    subprocess.run(NR + [str(B2), str(s), str(c)], capture_output=True, env=ENV)
    return c.read_bytes() if c.exists() and c.stat().st_size else b''


def translate(code, name):
    env = dict(ENV, RUN=' '.join(ARM + [str(TRANSLATOR)]))
    p = subprocess.run(['sh', str(RV2ARM), str(code)], capture_output=True, env=env)
    assert p.returncode == 0, p.stderr
    a = T / f'{name}.arm'; a.write_bytes(p.stdout)
    return a


def grep_src(path):
    return b'\n'.join(l for l in path.read_bytes().splitlines() if not l.startswith(b'--'))


# A. self-compile through a slow, chunked pipe (RISC-V and ARM), must equal B2.bin byte for byte
src = V / 'self_S_input.txt'
want = B2.read_bytes()
rc, out, st = run_pipe(RV + [str(B2)], src.read_bytes(), chunked=True, seed=1)
check('self-compile rv, chunked pipe stdin', rc == 0 and st == 0 and out == want, f'rc={rc} st={st} n={len(out)}')
arm_b2 = V / 'arm' / 'B2_arm.bin'
rc, out, st = run_pipe(ARM + [str(arm_b2)], src.read_bytes(), chunked=True, seed=2)
check('self-compile arm, chunked pipe stdin', rc == 0 and st == 0 and out == want, f'rc={rc} st={st} n={len(out)}')

# B. input boundaries with count.lean (output 1 byte): file stdin vs chunked pipe stdin
cnt = compile_nano(grep_src(V / 'examples' / 'count.lean'), 'count')
for n in (0, 1, CAP - 1, CAP, CAP + 1):
    data = bytes(random.Random(n).randrange(256) for _ in range(min(n, 3000))) + bytes(max(0, n - 3000))
    (T / 'bin.in').write_bytes(data)
    nr = nano(T / 'count.rv', T / 'bin.in')
    rc_f, out_f, st_f = run_file(RV + [str(T / 'count.rv')], T / 'bin.in')
    rc_p, out_p, st_p = run_pipe(RV + [str(T / 'count.rv')], data, chunked=True, seed=n)
    exp_refuse = n >= CAP
    if n > CAP:
        check(f'count rv n={n}: nanorun refuses', nr[0] not in (0, 1), f'nanorun rc={nr[0]}')
        check(f'count rv n={n}: shim refuses', rc_f == 2 and rc_p == 2, f'file rc={rc_f} pipe rc={rc_p}')
        continue
    same = (rc_f, out_f, st_f) == (rc_p, out_p, st_p) and out_p == nr[2] and st_p == nr[1]
    tag = 'known refusal (2^20)' if n == CAP else ''
    check(f'count rv n={n}: pipe == file == nanorun', same or (exp_refuse and rc_f == 2 and rc_p == 2),
          f'nanorun st={nr[1]} shim file st={st_f} pipe st={st_p} {tag}')

# C. exact output sizes through reverse (output length = input length), RISC-V and ARM
rev = compile_nano(grep_src(V / 'examples' / 'reverse.lean'), 'rev')
rev_arm = translate(T / 'rev.rv', 'rev')
for n in (CAP // 2 - 1, CAP // 2, CAP // 2 + 1):
    data = random.Random(n).randbytes(n)
    (T / 'rev.in').write_bytes(data)
    nr = nano(T / 'rev.rv', T / 'rev.in')
    rc_p, out_p, st_p = run_pipe(RV + [str(T / 'rev.rv')], data, chunked=True, seed=n)
    rc_a, out_a, st_a = run_pipe(ARM + [str(rev_arm)], data, chunked=True, seed=n + 1)
    ok = nr[2] is not None and out_p == nr[2] and out_a == nr[2] and nr[2] == data[::-1] and st_p == st_a == nr[1]
    check(f'reverse n={n} (exact output length {n})', ok or nr[1] == -2 and rc_p == rc_a == 1,
          f'nanorun st={nr[1]} rv st={st_p} arm st={st_a} len={len(out_p)}')

# D. stdout to a file vs a pipe; stdout to /dev/full (must not report success)
(T / 'cnt.in').write_bytes(b'hello')
res_file = subprocess.run(RV + [str(T / 'count.rv')], stdin=open(T / 'cnt.in', 'rb'), stdout=open(T / 'stdout.bin', 'wb'),
                          stderr=subprocess.PIPE, env=ENV)
res_pipe = subprocess.run(RV + [str(T / 'count.rv')], input=b'hello', capture_output=True, env=ENV)
check('stdout to file == stdout to pipe', (T / 'stdout.bin').read_bytes() == res_pipe.stdout == b'\x05' and res_file.returncode == res_pipe.returncode == 0)
full = subprocess.run(RV + [str(T / 'count.rv')], input=b'hello', stdout=open('/dev/full', 'wb'), stderr=subprocess.PIPE, env=ENV)
nr_full = subprocess.run(NR + [str(T / 'count.rv'), str(T / 'cnt.in'), '/dev/full'], capture_output=True, env=ENV)
check('stdout /dev/full: both fail visibly (nonzero exit)', full.returncode != 0 and nr_full.returncode != 0,
      f'shim rc={full.returncode} nanorun rc={nr_full.returncode}')

# E. work memory exhaustion: self-compile needs more than 1 MiB; both must report -1 (exit 1), no output
src_bytes = src.read_bytes()
(T / 'self.src').write_bytes(src_bytes)
rc_w, out_w, st_w = run_pipe(RV_1M + [str(B2)], src_bytes, chunked=False)
check('work memory 1 MiB: shim_rv status -1 and exit 1', rc_w == 1 and st_w == -1 and out_w == b'', f'rc={rc_w} st={st_w}')
w1 = subprocess.run(NR + [str(B2), str(T / 'self.src'), str(T / 'w1.bin'), '1'], capture_output=True, env=ENV)
check('work memory 1 MiB: nanorun status -1 and exit 1 (same as shim)', w1.returncode == 1 and status(w1.stderr.decode()) == -1,
      f'rc={w1.returncode}')

# F. malformed code files: nanorun refuses (assert or trap); the shims run the bytes as they are
(T / 'odd.rv').write_bytes(b'\x13\x00\x00\x00\x00')
(T / 'one.in').write_bytes(b'x')
w_odd = subprocess.run(NR + [str(T / 'odd.rv'), str(T / 'one.in'), str(T / 'o.bin')], capture_output=True, env=ENV)
check('odd-size code: nanorun refuses', w_odd.returncode not in (0, 1), f'rc={w_odd.returncode}')
rc_o = subprocess.run(RV + [str(T / 'odd.rv')], input=b'x', capture_output=True, env=ENV).returncode
print(f'INFO odd-size code on shim_rv: rc={rc_o} (no check: shim has no code-size validation)')
(T / 'empty.rv').write_bytes(b'')
rc_e = subprocess.run(RV + [str(T / 'empty.rv')], input=b'x', capture_output=True, env=ENV).returncode
print(f'INFO empty code on shim_rv: rc={rc_e} (nanorun asserts on empty code)')

print(f'done: {fails} DIFF', flush=True)
