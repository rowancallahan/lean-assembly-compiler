#!/bin/bash
# usage: Testing/leanzip/run.sh reject | cases   (repo root, after `lake build Riscv.Frontx.Machine`)
# reject: one `frontx_compile` per function, 120 s timeout each (a translator run may not terminate)
O=${TMPDIR:-/tmp}/leanzip-olean; mkdir -p $O
lake env lean -o $O/Orig.olean Testing/leanzip/Orig.lean || exit 1
export LEAN_PATH=$(lake env printenv LEAN_PATH):$O
case $1 in
  reject)
    grep '^frontx_compile' Testing/leanzip/Reject.lean | while read _ n; do
      echo "=== $n"
      { sed -n '1,/^set_option/p' Testing/leanzip/Reject.lean; echo "frontx_compile $n"; } > $O/one.lean
      timeout 120 lean $O/one.lean 2>&1 | grep -v "libleanshared\|libc.so\|PANIC\|backtrace" | cut -c1-300 | head -12
      [ ${PIPESTATUS[0]} = 124 ] && echo "TIMEOUT 120 s"
    done ;;
  cases) lean Testing/leanzip/EmitCases.lean ;;
esac
