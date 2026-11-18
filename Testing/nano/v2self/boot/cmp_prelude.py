#!/usr/bin/env python3
"""B1 (Array prelude) vs B1L (List prelude): identical output bytes on small sources.  usage: cmp_prelude.py B1 B1L"""
import subprocess, sys
src = [
 "def m (x : List UInt8) : List UInt8 := put (put [] (rd x 0)) (len x)\n",
 "def m (x : List UInt8) : List UInt8 := put [] (bget (bpush (bnew) 7) 0)\n",
 "def m (x : List UInt8) : List UInt8 := put [] 5\n",
 "def m (x : List UInt8) : List UInt8 := put [] (rd x 0 + rd x 1 * 3)\n",
 "def m (x : List UInt8) : List UInt8 := let a := rd x 0; let b := a + 1; put (put [] a) b\n",
 "def m (x : List UInt8) : List UInt8 := if rd x 0 == 0 then put [] 1 else put [] 2\n",
 "def m (x : List UInt8) : List UInt8 := if rd x 0 < rd x 1 then put [] 1 else put [] 2\n",
 "def m (x : List UInt8) : List UInt8 := put [] (bsize (bpush (bpush bnew 1) 2))\n",
 "def m (x : List UInt8) : List UInt8 := put [] (bget (bset (bpush bnew 1) 0 9) 0)\n",
 "def f (a : UInt64) : UInt64 := a + 1\ndef m (x : List UInt8) : List UInt8 := put [] (f (rd x 0))\n",
 "def f (a b : UInt64) : UInt64 := a * b\ndef m (x : List UInt8) : List UInt8 := put [] (f (rd x 0) (rd x 1))\n",
 "def f : Nat → List UInt8 → UInt64 → UInt64\n  | 0, x, s => s\n  | n + 1, x, s => f n x (s + rd x s)\ndef m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0)\n",
 "def f : Nat → UInt64 → UInt64 → UInt64\n  | 0, a, b => a\n  | n + 1, a, b => f n b (a + b)\ndef m (x : List UInt8) : List UInt8 := put [] (f 10 0 1)\n",
 "def f (p : UInt64 × UInt64) : UInt64 := let (a, b) := p; a + b\ndef m (x : List UInt8) : List UInt8 := put [] (f (1, 2))\n",
 "def m (x : List UInt8) : List UInt8 := put (put (put [] 1) 2) 3\n",
 "def m (x : List UInt8) : List UInt8 := x\n",                      # reject or odd
 "def m (x : List UInt8) : UInt64 := 3\n",                          # no main shape
 "def m (x : List UInt8) : List UInt8 := put [] (rd x\n",           # syntax
 "def m (x : List UInt8) : List UInt8 := put [] (1 << 2)\n",        # lex reject
 "",                                                                # empty
]
from concurrent.futures import ThreadPoolExecutor
def run(b, s): return subprocess.run([b], input=s.encode(), capture_output=True).stdout
def one(s): return s, run(sys.argv[1], s), run(sys.argv[2], s)
with ThreadPoolExecutor(4) as ex: res = list(ex.map(one, src))
bad = [s for s, a, b in res if a != b]
for s in bad: print("MISMATCH", repr(s))
print(f"{len(src)} sources: Array vs List prelude mismatches = {len(bad)}; accepted (non-empty output): {sum(1 for s, a, b in res if s and a)} / {len(src)}; outputs of the Array build: {[len(a) for s, a, b in res]}")
