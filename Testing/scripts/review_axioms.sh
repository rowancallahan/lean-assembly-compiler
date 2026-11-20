#!/usr/bin/env bash
# Pinned axioms of the REVIEW theorems (Nano/V2Self/REVIEW.lean): extracts every `#print axioms` result, one line per
# theorem, and diffs against Testing/scripts/review_axioms.txt.  Fails loudly on any difference.
# usage: Testing/scripts/review_axioms.sh          (check)
#        Testing/scripts/review_axioms.sh --pin    (rewrite the pinned file; only after an approved change)
set -euo pipefail
export PATH=$HOME/.elan/bin:$PATH
lake build Nano.V2Self.REVIEW > /dev/null
GOT=$(lake env lean Nano/V2Self/REVIEW.lean 2>&1 | tr -d '\n' | grep -o "'[^']*' depends on axioms: \[[^]]*\]\|'[^']*' does not depend on any axioms" | tr -s ' ')
if [ "${1:-}" = "--pin" ]; then printf '%s\n' "$GOT" > Testing/scripts/review_axioms.txt; echo "pinned $(wc -l < Testing/scripts/review_axioms.txt) theorems"; exit 0; fi
diff Testing/scripts/review_axioms.txt <(printf '%s\n' "$GOT") && echo "OK: $(wc -l < Testing/scripts/review_axioms.txt) theorems, axioms as pinned"
