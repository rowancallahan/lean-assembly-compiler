#!/usr/bin/env bash
# usage: accept.sh File.lean decl1 decl2 ...   (core-Lean-only file; exports ONLY the named decls + closure)
# env: LEAN4EXPORT, CONLECHE (binaries)
set -euo pipefail
: "${LEAN4EXPORT:?}" "${CONLECHE:?}"
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$PATH"
f=$(realpath "$1"); shift
# no decl names given -> every top-level theorem/def/abbrev in the file (namespace-aware)
[ $# -gt 0 ] || mapfile -t names < <(python3 -I - "$f" <<'PY'
import re, sys
ns = []
for l in open(sys.argv[1]):
    m = re.match(r"namespace (\S+)", l)
    if m: ns.append(m.group(1)); continue
    m = re.match(r"end (\S+)", l)
    if m and ns and ns[-1] == m.group(1): ns.pop(); continue
    m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:protected\s+)?(?:noncomputable\s+)?(?:theorem|def|abbrev|instance)\s+([^\s:({\[]+)", l)
    if m: print(".".join(ns + [m.group(1)]))
PY
) && set -- "${names[@]}"
[ $# -gt 0 ]
d=$(mktemp -d); m=$(basename "$f" .lean)
cp "$f" "$d/$m.lean"
(cd "$d" && lean -o "$m.olean" "$m.lean")
t0=$(date +%s.%N)
(cd "$d" && LEAN_PATH="$d:$(lean --print-libdir)" "$LEAN4EXPORT" "$m" -- "$@" > "$m.ndjson")
t1=$(date +%s.%N)
set +e
out=$(python3 -I - "$CONLECHE" "$d/$m.ndjson" <<'PY' 2>&1
import resource, subprocess, sys
r = subprocess.run([sys.argv[1], "--verified", sys.argv[2]], capture_output=True, text=True)
print(r.stdout + r.stderr, end="")
print("maxrss_kb=%d" % resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
sys.exit(r.returncode)
PY
)
rc=$?
set -e
t2=$(date +%s.%N)
[ $rc -eq 0 ] && st=ACCEPTED || st=REJECTED
echo "$out"
echo "$st file=$m export_s=$(echo "$t1-$t0"|bc) check_s=$(echo "$t2-$t1"|bc) ndjson_bytes=$(stat -c%s "$d/$m.ndjson")"
exit $rc
