#!/bin/bash
# Port a copy of opencompl/sail-riscv-lean@51c635c4 (+ its Sail v5 dependency) to Lean 4.34.1. usage: port_model.sh DIR (a copy of the model, no .lake)
set -ex
cd $1
echo 'leanprover/lean4:v4.34.1' > lean-toolchain
lake update 2>/dev/null || true   # fetch Sail v5 into .lake/packages (first `lake build` does this too)
lake build Sail || true
# 1. `assert` became a keyword in Lean 4.34 (experimental intrinsic verification syntax): rename the Sail function (lean-sail v10 calls it sail_assert) and all uses
sed -i -E 's/^def assert /def sail_assert /' .lake/packages/Sail/Sail/ConcurrencyInterfaceV1.lean .lake/packages/Sail/Sail/ArchSem.lean
grep -rlE "^\s*assert " LeanRV64D | xargs sed -i -E 's/^(\s*)assert /\1sail_assert /'
sed -i 's/PreSail\.assert\b/PreSail.sail_assert/; s/^abbrev assert (p/abbrev sail_assert (p/' LeanRV64D/SpecializationV1.lean
sed -i '449s/then assert /then sail_assert /' LeanRV64D/Step.lean
# 2. new `do` elaborator is exponential on print_rvfi_exec (19 `(pure (print_bits .. (← ..)))` statements): use the legacy elaborator for that one def
sed -i 's/^def print_rvfi_exec /set_option backward.do.legacy true in\ndef print_rvfi_exec /' LeanRV64D/RvfiDii.lean
lake build
