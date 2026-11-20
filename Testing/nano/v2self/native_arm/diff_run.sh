#!/usr/bin/env bash
# diff_run.sh COMPILER_CMD prog.lean input : compile with B2 (RISC-V) and with the native-ARM compiler (COMPILER_CMD reads
# source on stdin, writes A64 code), run both (qemu-riscv64 + shim_rv, qemu-aarch64 + shim_arm), compare status and output.
# Prints "OK n_rv n_a64" (static code words) or "DIFF ..." and exits 1.  PROTOTYPE, UNPROVEN glue.
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd); T=${TMPD:-$(mktemp -d)}; S=${SHIMS:-/tmp/claude-0/na}
grep -v '^--' "$2" > "$T/src"
qemu-riscv64 "$S/shim_rv" "$D/../B2.bin" < "$T/src" > "$T/rv" 2>/dev/null
$1 < "$T/src" > "$T/a64" 2>/dev/null
if [ ! -s "$T/rv" ] || [ ! -s "$T/a64" ]; then
  [ "$(stat -c%s "$T/rv")" = 0 ] && [ "$(stat -c%s "$T/a64")" = 0 ] && { echo "OK rejected"; exit 0; }
  echo "DIFF accept rv=$(stat -c%s "$T/rv") a64=$(stat -c%s "$T/a64")"; exit 1; fi
r1=$(timeout 60 qemu-riscv64 "$S/shim_rv" "$T/rv" < "$3" 2>&1 >"$T/o_rv" | tail -1 || true)
r2=$(timeout 60 qemu-aarch64 "$S/shim_arm" "$T/a64" < "$3" 2>&1 >"$T/o_a64" | tail -1 || true)
s1=${r1#shim_rv: }; s2=${r2#shim_arm: }
if [ "$s1" = "$s2" ] && cmp -s "$T/o_rv" "$T/o_a64"; then echo "OK $(( $(stat -c%s "$T/rv") / 4 )) $(( $(stat -c%s "$T/a64") / 4 )) $s1"
else echo "DIFF rv[$s1] a64[$s2]"; exit 1; fi
