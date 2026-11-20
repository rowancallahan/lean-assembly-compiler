#!/usr/bin/env python3
"""Deterministic benchmark inputs: in_10.bin, in_1k.bin, in_100k.bin, in_1m.bin in the given directory (seed 1, uniform random bytes).
usage: make_inputs.py DIR"""
import os, random, sys
d = sys.argv[1]
for name, n in [("10", 10), ("1k", 1 << 10), ("100k", 100 << 10), ("1m", 1 << 20)]:
    open(os.path.join(d, f"in_{name}.bin"), "wb").write(random.Random(1).randbytes(n))
