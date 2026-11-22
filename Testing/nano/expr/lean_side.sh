#!/usr/bin/env bash
# lean_side.sh OUT SRC... : Lean's normalized Expr of every def of the nano sources, in the S format (EXPR.md).
# One file: `import Lean` + Nano/Main/Prelude.lean + each SRC (in `namespace P<i>` when there are several) +
# lean_expr.lean, elaborated with plain `lean`. PREDEFS="u40 ..": defs read via the pre-definition (see lean_expr.lean). A def Lean rejects is printed as `X name` (elaboration errors: OUT.log).
set -euo pipefail
R=$(cd "$(dirname "$0")/../../.." && pwd); D=$(cd "$(dirname "$0")" && pwd)
O=$1; shift
W=$(mktemp -d); F=$W/LeanSide.lean; names=()
{ echo "import Lean"; echo "set_option linter.unusedVariables false"; echo "set_option maxRecDepth 100000"; echo "set_option maxErrors 1000000"
  cat "$R/Nano/Main/Prelude.lean"; echo
  i=0
  for s in "$@"; do
    if [ $# -gt 1 ]; then p="P$i."; echo "namespace P$i"; else p=""; fi
    cat "$s"; echo
    [ $# -gt 1 ] && echo "end P$i"
    for n in $(grep -oP '^def \K[^ ]+' "$s"); do names+=("\`$p$n"); done
    i=$((i+1))
  done
  echo "def srcDefs : List Lean.Name := [$(IFS=,; echo "${names[*]}")]"
  echo "def xOut : Bool := ${XOUT:-false}"
  echo "def preDefs : List Lean.Name := [$(for n in ${PREDEFS:-}; do printf '`%s,' "$n"; done | sed 's/,$//')]"
  cat "$D/lean_expr.lean"; } > "$F"
export PATH=$HOME/.elan/bin:$PATH
lean -DmaxErrors=0 "$F" > "$W/out" 2>&1 || true
grep -v '^[DX] ' "$W/out" > "$O.log" || true
grep '^[DX] ' "$W/out" | grep -v $'^X [^ ]*\t' > "$O"
grep $'^X [^ ]*\t' "$W/out" > "$O.x" || true
test "$(wc -l < "$O")" = "${#names[@]}" || { tail -5 "$O.log"; echo "lean_side: missing output"; exit 1; }
