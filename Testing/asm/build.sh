#!/bin/sh -e
cd "$(dirname "$0")"
riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -nostdlib -static -Wl,-T,link.ld -Wl,--no-relax -Wl,--build-id=none start.S sort.S -o sort.elf
riscv64-linux-gnu-objdump -d -M no-aliases sort.elf > sort.dis
