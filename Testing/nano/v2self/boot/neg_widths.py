#!/usr/bin/env python3
"""Width/shape negative tests for Par1 (via B1 parse) with VALID companions (non-vacuity: valid must be accepted).  usage: neg_widths.py B1"""
import subprocess, sys
B1 = sys.argv[1]
M = "def m (x : List UInt8) : List UInt8 := put [] ("
NEG = {
 "call-too-few": "def f (a b : UInt64) : UInt64 := a + b\n" + M + "f 1)\n",
 "call-too-many": "def f (a : UInt64) : UInt64 := a\n" + M + "f 1 2)\n",
 "call-wrong-type": "def f (a : UInt64) : UInt64 := a\n" + M + "f bnew)\n",
 "call-pair-for-word": "def f (a : UInt64) : UInt64 := a\n" + M + "f (1, 2))\n",
 "continue-missing-state": "def f : Nat → UInt64 → UInt64 → UInt64\n  | 0, a, b => a\n  | n + 1, a, b => f n a\n" + M + "f 3 0 0)\n",
 "continue-extra-state": "def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, a => f n a a\n" + M + "f 3 0)\n",
 "continue-wrong-type": "def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, a => f n bnew\n" + M + "f 3 0)\n",
 "continue-pair-for-word": "def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, a => f n (a, a)\n" + M + "f 3 0)\n",
 "if-branch-widths": "def f (a : UInt64) : UInt64 := if a == 0 then (1, 2) else 3\n" + M + "f 1)\n",
 "loop-input-extra": "def f : Nat → List UInt8 → UInt64 → UInt64\n  | 0, x, a => a\n  | n + 1, x, a => f n x\n" + M + "f 3 x 0)\n",
}
POS = {
 "call": "def f (a b : UInt64) : UInt64 := a + b\n" + M + "f 1 2)\n",
 "continue-2": "def f : Nat → UInt64 → UInt64 → UInt64\n  | 0, a, b => a\n  | n + 1, a, b => f n b a\n" + M + "f 3 0 1)\n",
 "continue-pair": "def f : Nat → UInt64 × UInt64 → UInt64\n  | 0, p => let (a, b) := p; a\n  | n + 1, p => let (a, b) := p; f n (b, a)\n" + M + "f 3 (1, 2))\n",
 "loop-input-1": "def f : Nat → List UInt8 → UInt64 → UInt64\n  | 0, x, a => a\n  | n + 1, x, a => f n x (a + 1)\n" + M + "f 3 x 0)\n",
 "loop-input-3": "def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64\n  | 0, x, a, b, c => a + b + c\n  | n + 1, x, a, b, c => f n x b c (a + 1)\n" + M + "f 3 x 0 0 0)\n",
 "call-input": "def g (x : List UInt8) (a b : UInt64) : UInt64 := a + b + rd x 0\n" + M + "g x 1 2)\n",
}
run = lambda s: subprocess.run([B1, "parse"], input=s.encode(), capture_output=True).stdout
nok = [k for k, s in NEG.items() if not run(s)]; pok = [k for k, s in POS.items() if run(s)]
for k, s in NEG.items():
    if run(s): print("NEGATIVE ACCEPTED:", k)
for k, s in POS.items():
    if not run(s): print("VALID REJECTED:", k)
print(f"VALID accepted {len(pok)} / {len(POS)} (must be 100%); NEGATIVE rejected {len(nok)} / {len(NEG)}")
sys.exit(0 if len(pok) == len(POS) and len(nok) == len(NEG) else 1)
