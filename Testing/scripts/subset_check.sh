#!/usr/bin/env bash
# subset_check.sh: the compiler's OWN source stays in the bootstrap subset (owner rule, ROADMAP).  Checks the texts the
# compilers actually compile, regenerated from the C files (Nano/{Main/Chain,Lexer,Parser,Ownership,Codegen}):
#   Testing/nano/v2self/self_S_input.txt (RISC-V compiler; must equal the checked-in copy) and
#   Testing/nano/v2self/native_arm/self_A_input.txt (native ARM compiler).
# Fails on any construct newer than the subset: `match`/`with`, `namespace`/`open`/`section`/`end`, `private`,
# attributes `@[…]`, doc comments (slash-dash-dash, slash-dash-bang).  Plain comments (dash-dash lines, nested
# slash-dash block comments) are allowed.
# usage: Testing/scripts/subset_check.sh   (from any directory of the checkout; rewrites the generated files in place)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
V=Testing/nano/v2self
cp $V/self_S_input.txt /tmp/subset_check_S.txt
python3 $V/build_self_S.py > /dev/null
python3 - "$V" <<'PY'
import re, sys
V = sys.argv[1]; t = open(f"{V}/self_S.lean").read()
a = t.split("\n", 4)[4].replace("end C\n", "")
b = re.sub(r"/-.*?-/", "", a, flags=re.S)
c = "\n".join(l for l in b.split("\n") if not l.startswith("--"))
open(f"{V}/self_S_input.txt", "w").write(re.sub(r"\n\n+", "\n\n", c))
PY
rc=0
cmp -s $V/self_S_input.txt /tmp/subset_check_S.txt || { echo "subset_check: FAIL: self_S_input.txt was stale (regenerated; commit it)"; rc=1; }
python3 $V/native_arm/build_self_A.py > /dev/null
python3 - $V/self_S_input.txt $V/native_arm/self_A_input.txt <<'PY'
import re, sys
BAD_WORDS = {"match", "with", "namespace", "open", "section", "end", "private"}
bad = []
for f in sys.argv[1:]:
    s = open(f).read(); out, i, n = [], 0, len(s)
    while i < n:
        if s.startswith("/--", i) or s.startswith("/-!", i):
            bad.append(f"{f}: doc comment at offset {i}"); out.append(" "); i += 3
        elif s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j
        elif s.startswith("/-", i):
            d, j = 0, i + 2
            while True:
                assert j < n, f"{f}: unterminated block comment"
                if s.startswith("-/", j):
                    j += 2
                    if d == 0: break
                    d -= 1
                elif s.startswith("/-", j): d += 1; j += 2
                else: j += 1
            i = j
        else: out.append(s[i]); i += 1
    code = "".join(out)
    if "@[" in code: bad.append(f"{f}: attribute @[")
    for w in sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", code)) & BAD_WORDS):
        bad.append(f"{f}: word `{w}`")
if bad:
    print("subset_check: FAIL\n" + "\n".join(bad)); sys.exit(1)
print("subset_check: OK (self_S_input.txt, self_A_input.txt in the bootstrap subset; plain comments allowed)")
PY
exit $rc
