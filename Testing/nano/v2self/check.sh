#!/bin/bash
# Nano/V2Self status: (1) the modules compile, (2) nano's own front end (frontElabK) accepts each stage text, (3) the
# differential test against Nano/V2S. Usage: bash Testing/nano/v2self/check.sh   (run from the repo root)
set -e
lake build Nano.V2Self.Driver
lake env lean --run Testing/nano/v2self/check.lean Nano/V2Self/Asm.lean Nano/V2Self/Expand.lean Nano/V2Self/Lex.lean \
  Nano/V2Self/Inl.lean Nano/V2Self/Parse.lean || true
lake env lean Testing/nano/v2self/diff_test.lean
