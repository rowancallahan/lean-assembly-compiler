#!/usr/bin/env bash
# lean_side.sh SRC OUT : Lean's normalized Expr of every def of the nano source SRC, in the S format (EXPR.md).
# Elaborates `import Lean` + Nano/Main/Prelude.lean + SRC + lean_expr.lean as one file with plain `lean`.
set -euo pipefail
R=$(cd "$(dirname "$0")/../../.." && pwd); D=$(cd "$(dirname "$0")" && pwd)
W=$(mktemp -d); F=$W/LeanSide.lean
{ echo "import Lean"; echo "set_option linter.unusedVariables false"; echo "set_option maxRecDepth 100000"
  cat "$R/Nano/Main/Prelude.lean"; echo; cat "$1"; echo
  echo "def srcDefs : List Lean.Name := [$(grep -oP '^def \K[^ ]+' "$1" | sed 's/^/`/' | paste -sd,)]"
  cat "$D/lean_expr.lean"; } > "$F"
export PATH=$HOME/.elan/bin:$PATH
lean "$F" > "$W/out" 2>&1 || { tail -20 "$W/out"; exit 1; }
{ grep -v '^D ' "$W/out" || true; } | head -5
grep '^D ' "$W/out" > "$2"
test "$(wc -l < "$2")" = "$(grep -c '^def ' "$1")"
