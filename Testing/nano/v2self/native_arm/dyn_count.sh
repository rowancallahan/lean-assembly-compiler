#!/usr/bin/env bash
# dyn_count.sh rv|a64 SHIM CODE INPUT : dynamic instruction count of the generated code only (QEMU exec log, one
# instruction per TB; PCs below 0x1000000 = the static shim, not counted).  Slow (~1 µs per instruction).
set -euo pipefail
case $1 in rv) Q=qemu-riscv64 ;; a64) Q=qemu-aarch64 ;; esac
$Q -one-insn-per-tb -d nochain,exec -D /dev/stdout "$2" "$3" < "$4" 2>/dev/null |
  awk -F'[][/]' '/^Trace/ { if (substr($3, 1, 10) != "0000000000") n++ } END { print n + 0 }'
