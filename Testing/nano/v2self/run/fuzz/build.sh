#!/bin/sh
# build.sh SELF_DIR WORK_DIR : nanorun (ASan+UBSan), shim_rv (RISC-V), shim_arm (AArch64) into WORK_DIR.
set -eu
V=$(cd "$1" && pwd); W=$2; mkdir -p "$W"
cc -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all "$V/run/nanorun.c" -o "$W/nanorun_asan"
riscv64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_rv.c" -o "$W/shim_rv"
aarch64-linux-gnu-gcc -O2 -static "$V/run/shim/shim_arm.c" -o "$W/shim_arm"
sed 's/WORK = 1 << 30/WORK = 1 << 20/' "$V/run/shim/shim_rv.c" > "$W/shim_rv_1M.c"
riscv64-linux-gnu-gcc -O2 -static "$W/shim_rv_1M.c" -o "$W/shim_rv_1M"
for mb in 72 73; do                       # work-limit boundary variants (self-compile needs 73 MiB under nanorun)
  sed "s/WORK = 1 << 30/WORK = $mb << 20/" "$V/run/shim/shim_rv.c" > "$W/shim_rv_${mb}M.c"
  riscv64-linux-gnu-gcc -O2 -static "$W/shim_rv_${mb}M.c" -o "$W/shim_rv_${mb}M"
done
echo "built in $W"
