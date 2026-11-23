#!/usr/bin/env bash
# usage: gen_eqs.sh OUT.lean SRC.lean [NAMESPACE]   -> OUT.lean (prelude + SRC + Lean-generated `f.eq_def` pointwise equations),
# OUT.names = the eq_def theorem names to export.  Equations are Lean's own `getUnfoldEqnFor?` (kernel-checked), one per def.
set -euo pipefail
R=$(cd "$(dirname "$0")/../.." && pwd); out=$1; src=$2; ns=${3:-}; p=${ns:+$ns.}
{ echo "import Lean"; echo "set_option maxRecDepth 100000"
  sed -n '1,/^def bpush/p' "$R/Testing/nano/v2self/boot/B1L.lean"; echo
  grep -v '^import ' "$src"; echo
  echo "open Lean Meta Elab Command in"
  echo "elab \"gen_eqs\" : command => liftTermElabM do"
  echo "  for n in [$(grep -oP '^def \K[^ ]+' "$src" | sed "s/^/\`$p/" | paste -sd,)] do"
  echo "    discard <| getUnfoldEqnFor? n (nonRec := true)"
  echo "gen_eqs"; } > "$out"
grep -oP '^def \K[^ ]+' "$src" | sed "s/^/$p/; s/\$/.eq_def/" > "${out%.lean}.names"
