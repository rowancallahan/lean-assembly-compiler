#!/bin/bash
# Reproducible setup of a box to run asm/triple.py. Run from the repo root as root. Lean build is run separately (see end).
set -ex
D=/home/user/deps
mkdir -p $D
# 12G swap (lake build of the Sail model is memory hungry)
[ -e /swapfile ] || { fallocate -l 12G /swapfile; chmod 600 /swapfile; mkswap /swapfile; }
swapon /swapfile || true
# apt tools
apt-get update -qq
apt-get install -y -qq zstd qemu-system-misc qemu-system-arm gcc-riscv64-linux-gnu gcc-aarch64-linux-gnu
# elan from GitHub release, Lean 4.29.0 from GitHub (releases.lean-lang.org is blocked)
T=~/.elan/toolchains/leanprover--lean4---v4.29.0
mkdir -p ~/.elan/bin $T
W=$(mktemp -d)
curl -fsSL https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz -C $W
$W/elan-init -y --default-toolchain none --no-modify-path
curl -fsSL https://github.com/leanprover/lean4/releases/download/v4.29.0/lean-4.29.0-linux.tar.zst | zstd -d | tar x -C $T --strip-components=1
export PATH=~/.elan/bin:$PATH
# RISC-V Lean model
[ -d $D/sail-riscv-lean ] || git clone https://github.com/opencompl/sail-riscv-lean $D/sail-riscv-lean
git -C $D/sail-riscv-lean checkout 51c635c460125ac87955d061fcd902ce03b8011f
# Sail C emulator (path hard-coded in asm/triple.py)
S=$D/sailsim; mkdir -p $S
curl -fsSL https://github.com/riscv/sail-riscv/releases/download/0.9/sail-riscv-Linux-x86_64.tar.gz | tar xz -C $S
test -x $S/sail-riscv-Linux-x86_64/bin/sail_riscv_sim
# Then (slow, tracked background job): lake build Proven.CompilerArm
