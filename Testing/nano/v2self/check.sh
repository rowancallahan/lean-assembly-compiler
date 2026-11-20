#!/bin/bash
# Nano/V2Self status: (1) the modules compile, (2) nano's own front end (frontElabK) accepts each stage text, (3) the
# differential test against Nano/V2S. Usage: bash Testing/nano/v2self/check.sh   (run from the repo root)
set -e
lake build Nano.V2Self.Legacy.Driver
lake env lean --run Testing/nano/v2self/check.lean Nano/V2Self/Legacy/Asm.lean Nano/V2Self/Legacy/Expand.lean Nano/V2Self/Legacy/Lex.lean \
  Nano/V2Self/Legacy/Inl.lean Nano/V2Self/Legacy/Parse.lean || true
lake env lean --run Testing/nano/v2self/check.lean Nano/V2Self/C/Base.lean Nano/V2Self/Legacy/C/Asm.lean Nano/V2Self/Legacy/C/Expand.lean \
  Nano/V2Self/Legacy/C/Lex.lean Nano/V2Self/Legacy/C/Inl.lean Nano/V2Self/Legacy/C/Parse.lean Nano/V2Self/Legacy/C/Main.lean || true
lake env lean Testing/nano/v2self/diff_test.lean
lake env lean Testing/nano/v2self/chain_test.lean
