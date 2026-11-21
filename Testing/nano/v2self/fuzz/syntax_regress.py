#!/usr/bin/env python3
"""syntax_regress.py: regression cases for the syntax-1 reject rules (owner rule: nano accepts only what Lean accepts).
Each case is a program text and whether Lean 4.34.1 accepts it (checked by hand with `lake env lean`). Both compilers
(RISC-V B2.bin under qemu-riscv64, native ARM GA_arm.bin under qemu-aarch64) must accept exactly the Lean-accepted
ones. Exit 1 on any difference.   usage: syntax_regress.py [--lean]   (--lean: also check each verdict with `lean`, Init only)
env RV / ARM: other compiler binaries (default: the checked-in B2.bin, native_arm/GA_arm.bin)."""
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
    ('A attr implemented_by', '@[implemented_by m] ' + M, False),
    ('A doc attr private', '/-- d -/\n@[inline] private ' + M, True),
    ('A private before attr', 'private @[inline] ' + M, False),
    ('A attr before doc', '@[inline] /-- d -/\n' + M, False),
    ('C distinct arms', G.format(1) + M, True),
    ('C duplicate arm', G.format(0) + M, False),
    ('E namespace', 'namespace Fz1\n' + M + 'end Fz1\n', True),
    ('E namespace left open', 'namespace Fz1\n' + M, True),
    ('E section in namespace', 'namespace Fz1\nsection\n' + M + 'end\nend Fz1', True),
    ('E module docs around', '/-! a -/\nnamespace Fz1\n/-! b -/\n' + M + '/-! c -/\nend Fz1\n', True),
    ('E/F3 stray end', M + 'end\n', False),
    ('E/F3 end before', 'end\n' + M, False),
    ('E end wrong name', 'namespace Fz1\n' + M + 'end Fz2\n', False),
    ('E end unnamed closes namespace', 'section\nnamespace Ab1\n' + M + 'end\n', False),
    ('E end named closes section', 'section\n' + M + 'end Fz1\n', False),
    ('E too many ends', 'namespace Ab1\n' + M + 'end Ab1\nend\n', False),
    ('E namespace two names', 'namespace Fz1 Fz2\n' + M, False),
    ('E module doc mid-expression', 'def g (n : UInt64) : UInt64 := n /-! x -/ + 1\n' + M, False),
    ('M2 numeral 2^64 - 1', 'def g (n : UInt64) : UInt64 := 18446744073709551615\n' + M, True),
    ('A protected def at the root', 'protected ' + M, False),
    ('E module doc before def', 'def g (n : UInt64) : UInt64 := n\n/-! x -/\n' + M, True),
]
REJ_NANO_ONLY = [  # Lean accepts, nano rejects (stricter, allowed): the frame rule's name form
    ('E namespace Int8 (Lean root)', 'namespace Int8\n' + M),
    ('E dotted namespace', 'namespace Fz1.Fz2\n' + M),
    ('E lowercase namespace', 'namespace foo\n' + M),
    ('A attr not whitelisted', '@[simp] ' + M),
    ('E namespace between defs', M + 'namespace Fz1\n' + M),
    ('E def after end', 'namespace Fz1\n' + M + 'end Fz1\n' + M),
    ('E open', 'open Nat\n' + M),
    ('E module doc at the end', M + '/-! d -/\n'),
    ('A partial def', 'partial ' + M),
    ('M2 numeral 2^64 (Lean: wraps as UInt64, is 2^64 as fuel)', 'def g (n : UInt64) : UInt64 := 18446744073709551616\n' + M),
    ('M2 numeral 10^20', 'def g (n : UInt64) : UInt64 := 100000000000000000000\n' + M),
    ('A unsafe def', 'unsafe ' + M),
    ('A noncomputable def', 'noncomputable ' + M),
    ('A opaque', 'opaque g : UInt64\n' + M),
]
W = tempfile.mkdtemp(prefix='synreg_')
for c, s in (('riscv64-linux-gnu-gcc', 'shim_rv'), ('aarch64-linux-gnu-gcc', 'shim_arm')):
    subprocess.run([c, '-O2', '-static', f'{V}/run/shim/{s}.c', '-o', f'{W}/{s}'], check=True)
COMP = [('rv', ['qemu-riscv64', f'{W}/shim_rv', os.environ.get('RV', f'{V}/B2.bin')]),
        ('arm', ['qemu-aarch64', f'{W}/shim_arm', os.environ.get('ARM', f'{V}/native_arm/GA_arm.bin')])]
bad = 0
if '--lean' in sys.argv:
    for name, text, lean in CASES + [(n, s, True) for n, s in REJ_NANO_ONLY]:
        open(f'{W}/l.lean', 'w').write(text)
        acc = subprocess.run(['lean', f'{W}/l.lean'], capture_output=True).returncode == 0
        if acc != lean: bad += 1; print(f'FAIL lean: {name}: Lean {"accepts" if acc else "rejects"}, table says otherwise')
for name, text in REJ_NANO_ONLY: CASES.append((name, text, False))
for name, text, lean in CASES:
    for cn, cmd in COMP:
        acc = len(subprocess.run(cmd, input=text.encode(), capture_output=True, timeout=300).stdout) > 0
        if acc != lean: bad += 1; print(f'FAIL {cn}: {name}: nano {"accepts" if acc else "rejects"}, Lean {"accepts" if lean else "rejects"}')
print(f'syntax_regress: {len(CASES)} cases x {len(COMP)} compilers, {bad} failures')
sys.exit(1 if bad else 0)
