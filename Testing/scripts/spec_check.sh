#!/bin/bash
# Held-out spec check: every file under Spec/ must match Spec/FROZEN.sha256 (sha256 of each file, sorted by path).
#   Testing/scripts/spec_check.sh           check (exit 1 and print the diff on any change / new / removed file)
#   Testing/scripts/spec_check.sh --freeze  re-freeze after an owner-approved change to Spec/
set -eo pipefail
H=$(cd "$(dirname "$0")" && pwd); R=$(cd "$H/../.." && pwd); cd "$R"
cur() { find Spec -type f ! -name FROZEN.sha256 | LC_ALL=C sort | xargs sha256sum; }
if [ "${1:-}" = "--freeze" ]; then cur > Spec/FROZEN.sha256; echo "re-frozen: $(wc -l < Spec/FROZEN.sha256) files"; exit 0; fi
[ -f Spec/FROZEN.sha256 ] || { echo "SPEC CHECK: Spec/FROZEN.sha256 missing"; exit 1; }
if D=$(diff Spec/FROZEN.sha256 <(cur)); then echo "  Spec/ matches FROZEN.sha256 ($(wc -l < Spec/FROZEN.sha256) files)"
else echo "$D"; echo "SPEC CHECK: Spec/ differs from Spec/FROZEN.sha256 (re-freeze: Testing/scripts/spec_check.sh --freeze)"; exit 1; fi
