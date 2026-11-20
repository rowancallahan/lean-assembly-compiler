#!/usr/bin/env bash
# Self-compile fixed point: self_S.lean (from the C files) -> input text -> B1 (Lean-compiled, TRUSTED) -> B2 := B1(S)
# -> B3 := B2(S) on QEMU (64 MiB work) -> cmp B3 B2.  usage: Testing/nano/v2self/boot/fixpoint.sh [OUTDIR]
set -euo pipefail
O=${1:-/tmp/fixpoint}; mkdir -p "$O"; V=Testing/nano/v2self
python3 $V/build_self_S.py
python3 - "$V" <<'PY'
import re, sys
V = sys.argv[1]; t = open(f"{V}/self_S.lean").read()
a = t.split("\n", 4)[4].replace("end C\n", "")
b = re.sub(r"/-.*?-/", "", a, flags=re.S)
c = "\n".join(l for l in b.split("\n") if not l.startswith("--"))
open(f"{V}/self_S_input.txt", "w").write(re.sub(r"\n\n+", "\n\n", c))
PY
python3 $V/boot/build_B1.py
lean $V/boot/B1.lean -c "$O/B1.c" > /dev/null
leanc -O2 "$O/B1.c" -o "$O/B1"
"$O/B1" < $V/self_S_input.txt > "$O/B2.bin"
test -s "$O/B2.bin"
python3 - "$O" "$V" <<'PY'
import sys
O, V = sys.argv[1:3]; b = open(f"{O}/B2.bin", "rb").read(); assert len(b) % 4 == 0
open(f"{O}/P.words", "w").write("B2 code\n" + " ".join(f"{int.from_bytes(b[i:i+4], 'little'):08x}" for i in range(0, len(b), 4)) + "\n")
open(f"{O}/src.txt", "wb").write(open(f"{V}/self_S_input.txt", "rb").read())
PY
rm -f "$O/O.bin"
python3 $V/selfrun.py "$O" 96 512
cmp "$O/O.bin" "$O/B2.bin"
echo "FIXED POINT: B3 == B2 ($(stat -c %s "$O/B2.bin") bytes, sha256 $(sha256sum "$O/B2.bin" | cut -d' ' -f1))"
