#!/usr/bin/env python3
"""Synthetic compiler-scaling inputs (for run_bench.sh). Writes DIR/chain_K.lean (K helper defs, each calling the previous one)
and DIR/expr_K.lean (one def whose body is a sum of K byte reads). usage: synth_scaling.py DIR"""
import os, sys
d = sys.argv[1]
for K in [10, 20, 40, 80, 160, 320]:
    with open(os.path.join(d, f"chain_{K}.lean"), "w") as f:
        f.write("def h0 (x : List UInt8) (a : UInt64) : UInt64 := a + rd x 0\n")
        for i in range(1, K):
            f.write(f"def h{i} (x : List UInt8) (a : UInt64) : UInt64 := h{i-1} x (a + {i % 250})\n")
        f.write(f"def m (x : List UInt8) : List UInt8 := put [] (h{K-1} x 0)\n")
    with open(os.path.join(d, f"expr_{K}.lean"), "w") as f:
        f.write("def m (x : List UInt8) : List UInt8 := put [] (" + " + ".join(f"rd x {i % 8}" for i in range(K)) + ")\n")
# flat family: K independent defs (no calls between them), m sums them all
for K in [10, 20, 40, 80, 160, 320]:
    with open(os.path.join(d, f"flat_{K}.lean"), "w") as f:
        for i in range(K):
            f.write(f"def h{i} (x : List UInt8) (a : UInt64) : UInt64 := a + rd x {i % 8} + {i % 250}\n")
        f.write("def m (x : List UInt8) : List UInt8 := put [] (" + " + ".join(f"h{i} x 0" for i in range(K)) + ")\n")
