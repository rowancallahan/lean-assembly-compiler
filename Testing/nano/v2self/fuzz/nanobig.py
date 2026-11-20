#!/usr/bin/env python3
"""Big-buffer nano programs for the far-address mode of armfuzz.py (BIG=1).

A buffer (Buf) of len(x) words is filled by a fuel loop, updated element by element with a random expression of
rd x i / i / constants (large constants force big immediates), and summed by a second fuel loop.  With inputs of tens of
KB the buffer is hundreds of KB, so loads and stores go to far offsets from the buffer base.  The output is the low
three bytes of the sum.  Valid for B2 and the reference in the probes (small and 5000-byte inputs)."""
import random

ALPHA = 'abcdefghjklpqrstuvwyz'

def expr(R, d=2):
    r = R.random()
    if d <= 0 or r < 0.3:
        return R.choice(['(rd x i)', 'i', str(R.randrange(0, 2**20)), str(2**64 - 1 - R.randrange(0, 2**40)),
                         '(len x)', str(R.randrange(0, 300))])
    op = R.choice(['+', '-', '*', '&&&', '|||'])
    if R.random() < 0.2:
        return f"({expr(R, d-1)} {R.choice(['<<<', '>>>'])} {R.randrange(0, 64)})"
    return f"({expr(R, d-1)} {op} {expr(R, d-1)})"

def program(R):
    e = expr(R)
    return (
        "def p : Nat → UInt64 → Buf → Buf\n"
        "  | 0, i, b => b\n"
        "  | n + 1, i, b => p n (i + 1) (bpush b 0)\n"
        "def f : Nat → List UInt8 → UInt64 → Buf → Buf\n"
        "  | 0, x, i, b => b\n"
        f"  | n + 1, x, i, b => f n x (i + 1) (bset b i {e})\n"
        "def s : Nat → UInt64 → Buf → UInt64 → UInt64\n"
        "  | 0, i, b, a => a\n"
        "  | n + 1, i, b, a => s n (i + 1) b (a + bget b i)\n"
        "def m (x : List UInt8) : List UInt8 := "
        "let t := s (len' x) 0 (f (len' x) x 0 (p (len' x) 0 bnew)) 0; "
        "put (put (put [] t) (t >>> 8)) (t >>> 16)\n"
    )
