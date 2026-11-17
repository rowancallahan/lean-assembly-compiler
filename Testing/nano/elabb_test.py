#!/usr/bin/env python3
"""nanoElabB stage 1 (`Nano.Self.lexBE`, machine theorem `lexBE.implements1`) on QEMU and the Sail C emulator against
executed Lean, in the Implements1 convention (Testing/asm/frontx_test.py).  Inputs: corpus, boundary-fuzz mutations,
prefixes, random bytes, edge cases (Testing/nano/elabb_inputs.py).  The Lean side (emit_elabb.lean) also checks every
expected output against the spec (`decL (lexB x) = lexT x`, the lexer of `nanoElab`).
usage (repo root): python3 Testing/nano/elabb_test.py [N inputs] [seed]; afterwards rm -rf Testing/asm/ctest"""
import os, subprocess, sys
D = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(D, "..", ".."))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 400; SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 1
os.makedirs(os.path.join(D, "work"), exist_ok=True)
sh = lambda c: subprocess.run(f"cd {ROOT} && PATH=$HOME/.elan/bin:$PATH {c}", shell=True, check=True)
sh(f"python3 Testing/nano/elabb_inputs.py {N} {SEED} > Testing/nano/work/elabb_in.txt")
sh("lake env lean --tstack=400000 Testing/nano/emit_elabb.lean")
os.chdir(os.path.join(ROOT, "Testing", "asm"))
sys.argv = ["frontx_test.py", "-", "0", "lexbe"]
import frontx_test as F
F.LISTS.add("lexbe")
F.check(len(F.CASES))
