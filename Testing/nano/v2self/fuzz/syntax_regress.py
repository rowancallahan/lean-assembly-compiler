#!/usr/bin/env python3
"""syntax_regress.py: regression cases for the syntax-1 reject rules (owner rule: nano accepts only what Lean accepts).
Each case is a program text and whether Lean 4.34.1 accepts it (checked by hand with `lake env lean`). Both compilers
(RISC-V B2.bin under qemu-riscv64, native ARM GA_arm.bin under qemu-aarch64) must accept exactly the Lean-accepted
ones. Exit 1 on any difference.   usage: syntax_regress.py   (from any directory of the checkout)"""
import os, subprocess, sys, tempfile
R = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', '..'))
V = f'{R}/Testing/nano/v2self'
M = 'def m (x : List UInt8) : List UInt8 := []\n'
G = 'def g (n : UInt64) : UInt64 := match n with\n  | 0 => 1\n  | {} => 2\n  | _ => 3\n'
CASES = [  # (name, text, Lean accepts)
    ('plain', M, True),
    ('doc', '/-- d -/\n' + M, True),
    ('F1 tab after /--', '/--\tfoo -/\n' + M, False),
    ('F1 lone CR after /--', '/-- \r x -/\n' + M, False),
    ('F1 CR LF after /--', '/--\r\n x -/\n' + M, True),
    ('F2 /-/ skips a byte', '/-/- -/\n' + M, True),
    ('F2 /-/ then stray -/', '/-/- -/ -/\n' + M, False),
    ('doc with nested comment', '/-- /- c -/ d -/\n' + M, True),
    ('A doc mid-expression', 'def m (x : List UInt8) : List UInt8 := /-- d -/ []\n', False),
    ('A doc before nothing', M + '/-- d -/\n', False),
    ('A attr inline', '@[inline] ' + M, True),
    ('A attr not whitelisted', '@[simp] ' + M, False),
    ('A attr implemented_by', '@[implemented_by m] ' + M, False),
    ('A doc attr private', '/-- d -/\n@[inline] private ' + M, True),
    ('A private before attr', 'private @[inline] ' + M, False),
    ('A attr before doc', '@[inline] /-- d -/\n' + M, False),
    ('C distinct arms', G.format(1) + M, True),
    ('C duplicate arm', G.format(0) + M, False),
]
W = tempfile.mkdtemp(prefix='synreg_')
for c, s in (('riscv64-linux-gnu-gcc', 'shim_rv'), ('aarch64-linux-gnu-gcc', 'shim_arm')):
    subprocess.run([c, '-O2', '-static', f'{V}/run/shim/{s}.c', '-o', f'{W}/{s}'], check=True)
COMP = [('rv', ['qemu-riscv64', f'{W}/shim_rv', f'{V}/B2.bin']),
        ('arm', ['qemu-aarch64', f'{W}/shim_arm', f'{V}/native_arm/GA_arm.bin'])]
bad = 0
for name, text, lean in CASES:
    for cn, cmd in COMP:
        acc = len(subprocess.run(cmd, input=text.encode(), capture_output=True, timeout=300).stdout) > 0
        if acc != lean: bad += 1; print(f'FAIL {cn}: {name}: nano {"accepts" if acc else "rejects"}, Lean {"accepts" if lean else "rejects"}')
print(f'syntax_regress: {len(CASES)} cases x {len(COMP)} compilers, {bad} failures')
sys.exit(1 if bad else 0)
