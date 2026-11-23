#!/usr/bin/env python3
"""syntax_regress.py: regression cases for the syntax-1 reject rules (owner rule: nano accepts only what Lean accepts).
Each case is a program text and whether Lean 4.34.1 accepts it (checked by hand with `lake env lean`). Both compilers
(RISC-V B2.bin under qemu-riscv64, native ARM GA_arm.bin under qemu-aarch64) must accept exactly the Lean-accepted
ones. Exit 1 on any difference.   usage: syntax_regress.py [--lean]   (--lean: also check each verdict with `lake env lean`, with Nano.Main.Prelude for the prims)
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
    ('M17 let x := [] unused', 'def m (x : List UInt8) : List UInt8 := let t := []; put [] 1\n', False),
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
    ('M17 let x := [] used (Lean infers it)', 'def m (x : List UInt8) : List UInt8 := let t := []; put t 1\n'),
    ('M2 numeral 2^64 (Lean: wraps as UInt64, is 2^64 as fuel)', 'def g (n : UInt64) : UInt64 := 18446744073709551616\n' + M),
    ('M2 numeral 10^20', 'def g (n : UInt64) : UInt64 := 100000000000000000000\n' + M),
    ('A unsafe def', 'unsafe ' + M),
    ('A noncomputable def', 'noncomputable ' + M),
    ('A opaque', 'opaque g : UInt64\n' + M),
]
# class B (literal typing, Nat step 1: NumSpec.numOkP), checked with Lean
F = 'def f : Nat → List UInt8 → UInt64 → UInt64\n  | 0, x, a => a\n  | n + 1, x, a => f n x (a + 1)\n'
CASES += [
    ('M15 tuple-let as a comparison operand in a recursive call', 'def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64\n'
     '  | 0, x, i, a => a\n  | n + 1, x, i, a => f n x (i + 1) (if 5 == (let (a1, b1) := (rd x 5, rd x 2); a1) then 1 else 2)\n'
     'def m (x : List UInt8) : List UInt8 := put [] (f 3 x 0 0)\n', False),
    ('M15 tuple-let in an if-branch of a comparison operand', 'def m (x : List UInt8) : List UInt8 := put [] (if 0 == '
     '(if 318 &&& rd x 5 < rd x 4 then rd x 2 else (let (a0, b0) := (127, 2); a0)) then 1 else 2)\n', False),
    ('M12 numeral left of a shift', 'def g (a : UInt64) : UInt64 := 7 + (a >>> 2)\n' + M, False),
    ('N Nat literal comparison', 'def g (n : UInt64) : UInt64 := if 3 == 4 then 1 else 2\n' + M, True),
    ('N let literal used as UInt64', 'def g (n : UInt64) : UInt64 := let k := 5; n + k\n' + M, True),
    ('N literal fuel argument', F + 'def m (x : List UInt8) : List UInt8 := put [] (f 3 x 0)\n', True),
    ('N fuel literal reused as UInt64', F + 'def m (x : List UInt8) : List UInt8 := let k := 3; put [] (f k x k)\n', False),
    ('N literal shift operand', 'def g (n : UInt64) : UInt64 := n + (1 <<< 3)\n' + M, False),
]
T = 'def g (n : UInt64) : UInt64 := n\ndef t (x : List UInt8) (c : UInt64) : UInt64 := '
CASES += [(n, T + s + '\n' + M, ok) for n, s, ok in [  # GAP1: literal then-branch, "post" else-branch, untyped position
    ('G1 if literal/shift as a let value', 'let q := (if c == 0 then 97 else (c >>> 2)); q', False),
    ('G1 if literal/shift as a tuple field', 'let (p, q) := (1, if c == 0 then 97 else (c >>> 2)); q', False),
    ('G1 if literal/shift-tree as a let value', 'let q := (if c == 0 then 97 else ((c >>> 2) + c)); q', False),
    ('G1 if literal/nested-if shift', 'let q := (if c == 0 then 97 else (if c == 1 then c >>> 2 else c)); q', False),
    ('G1 if literal/let-shift', 'let q := (if c == 0 then 97 else (let w := c; w >>> 2)); q', False),
    ('G1 if literal/shift as an operand', 'let q := (if c == 0 then 97 else (c >>> 2)) + c; q', False),
    ('G1 if shift/literal as a let value', 'let q := (if c == 0 then (c >>> 2) else 97); q', True),
    ('G1 if literal/plain as a let value', 'let q := (if c == 0 then 97 else c + 1); q', True),
    ('G1 if literal/nested-if plain then', 'let q := (if c == 0 then 97 else (if c == 1 then c else c >>> 2)); q', True),
]] + [(n, T + s + '\n' + M, ok) for n, s, ok in [  # GAP2: a slot typed late is the left operand of a shift
    ('G2 let with a spine let, left of a shift', 'let v := (let (p, q) := (c, c); p ||| 5); v >>> 2', False),
    ('G2 tuple field with a spine let, left of a shift', 'let (a, b) := ((let (p, q) := (c, c); p ||| 5), 1); a >>> 2', False),
    ('G2 let with a spine let, shift inside a sum', 'let v := (let (p, q) := (c, c); p ||| 5); (v >>> 2) + 1', False),
    ('G2 let with a spine let, plain use', 'let v := (let (p, q) := (c, c); p ||| 5); v + 1', True),
    ('G2 let with a spine let, compared', 'let v := (let (p, q) := (c, c); p ||| 5); if v == 1 then 2 else 3', True),
]]
LV = 'let v := (let (p, q) := (c, c); p ||| 5); '
CASES += [(n, T + s + '\n' + M, ok) for n, s, ok in [  # GAP2: lateness propagates (an operand tree or if that waits)
    ('G2 copy of a late slot, left of a shift', LV + 'let w := v; w >>> 2', False),
    ('G2 late slot plus a literal, bound', LV + 'let w := v + 0; w >>> 2', False),
    ('G2 late slot as a tuple field', LV + 'let (w, z) := (v, 1); w >>> 2', False),
    ('G2 late slot plus a literal, left of a shift', LV + '(v + 0) >>> 2', False),
    ('G2 if late/literal, left of a shift', LV + '(if c == 0 then v else 5) >>> 2', False),
    ('G2 if late/literal, bound', LV + 'let w := (if c == 0 then v else 5); w >>> 2', False),
    ('G2 if literal/late, bound', LV + 'let w := (if c == 0 then 5 else v); w >>> 2', False),
    ('G2 two copies of a late slot', LV + 'let w := v; let u := w; u >>> 2', False),
    ('G2 late slot plus a typed operand', LV + 'let w := v + c; w >>> 2', True),
    ('G2 late slot or a typed operand', LV + '(v ||| c) >>> 2', True),
    ('G2 if late/typed', LV + '(if c == 0 then v else c) >>> 2', True),
    ('G2 copy of a late slot, no shift', LV + 'let w := v; w + 1', True),
    ('G2 late slot compared', LV + 'if v == 3 then 1 else 2', True),
    ('G2 if match/call, bound', 'let w := (if c == 0 then (let (p, q) := (c, c); p) else g c); w >>> 2', True),
    ('G2 if match/literal, bound', 'let w := (if c == 0 then (let (p, q) := (c, c); p) else 5); w >>> 2', False),
]]
REJ_NANO_ONLY += [  # Lean computes these in Nat (3 - 4 = 0, bignum arithmetic): nano rejects Nat arithmetic
    ('M1 literal arithmetic in a comparison', 'def g (n : UInt64) : UInt64 := if 3 - 4 == 0 then 1 else 2\n' + M),
    ('N Nat arithmetic on literals', F + 'def m (x : List UInt8) : List UInt8 := put [] (f (2 + 1) x 0)\n'),
]
W = tempfile.mkdtemp(prefix='synreg_')
for c, s in (('riscv64-linux-gnu-gcc', 'shim_rv'), ('aarch64-linux-gnu-gcc', 'shim_arm')):
    subprocess.run([c, '-O2', '-static', f'{V}/run/shim/{s}.c', '-o', f'{W}/{s}'], check=True)
COMP = [('rv', ['qemu-riscv64', f'{W}/shim_rv', os.environ.get('RV', f'{V}/B2.bin')]),
        ('arm', ['qemu-aarch64', f'{W}/shim_arm', os.environ.get('ARM', f'{V}/native_arm/GA_arm.bin')])]
bad = 0
if '--lean' in sys.argv:
    for name, text, lean in CASES + [(n, s, True) for n, s in REJ_NANO_ONLY]:
        open(f'{W}/l.lean', 'w').write('import Nano.Main.Prelude\n' + text)
        acc = subprocess.run(['lake', 'env', 'lean', f'{W}/l.lean'], capture_output=True, cwd=R).returncode == 0
        if acc != lean: bad += 1; print(f'FAIL lean: {name}: Lean {"accepts" if acc else "rejects"}, table says otherwise')
for name, text in REJ_NANO_ONLY: CASES.append((name, text, False))
for name, text, lean in CASES:
    for cn, cmd in COMP:
        acc = len(subprocess.run(cmd, input=text.encode(), capture_output=True, timeout=300).stdout) > 0
        if acc != lean: bad += 1; print(f'FAIL {cn}: {name}: nano {"accepts" if acc else "rejects"}, Lean {"accepts" if lean else "rejects"}')
print(f'syntax_regress: {len(CASES)} cases x {len(COMP)} compilers, {bad} failures')
sys.exit(1 if bad else 0)
