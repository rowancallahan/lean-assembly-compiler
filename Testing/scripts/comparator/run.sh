#!/bin/bash
# Run leanprover/comparator (commit 2a00b30, the last on Lean v4.29.0) on Challenge.lean / Solution.lean.
# One-time setup (network: github.com + Go proxy):
#   git clone https://github.com/leanprover/comparator ~/leanprover/comparator
#   git -C ~/leanprover/comparator worktree add ~/leanprover/comparator-429 2a00b30
#   (cd ~/leanprover/comparator-429 && lake build lean4export comparator)
#   GOBIN=$HOME/gobin go install github.com/zouuup/landrun/cmd/landrun@main
#   (cd Testing/scripts/comparator && lake update && rm -rf .lake/packages/Sail &&
#    ln -s "$PWD/../../../.lake/packages/Sail" .lake/packages/Sail)   # reuse the built Sail, do not rebuild the model
# bin/landrun wraps the real landrun (--best-effort; this kernel has Landlock ABI v7).  ~3-4 min, ~2 GB.
set -eo pipefail
C=$(cd "$(dirname "$0")" && pwd); cd "$C"
CMP=${COMPARATOR_DIR:-$HOME/leanprover/comparator-429}
export LANDRUN_REAL=${LANDRUN_REAL:-$HOME/gobin/landrun}
export PATH=$C/bin:$CMP/.lake/packages/lean4export/.lake/build/bin:$HOME/.elan/bin:$PATH
lake env "$CMP/.lake/build/bin/comparator" config.json
