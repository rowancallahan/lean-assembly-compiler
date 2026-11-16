# Build cache (not source)

Prebuilt Lean build output so cloud boxes do not rebuild from scratch.

- `sail-riscv-lean.tar.zst`: the whole `../deps/sail-riscv-lean` checkout (opencompl/sail-riscv-lean @51c635c) with
  its `.lake` build, Lean 4.29.0. Restore from the repo root:
  `mkdir -p ../deps && zstd -dc sail-riscv-lean.tar.zst | tar xf - -C ../deps`
Then `lake build <target>` should rebuild only this repo's own modules.
- `sailsim.tar.zst`: the Sail RISC-V simulator binary used by Testing/asm/frontx_test.py
  (`SAIL = /home/user/deps/sailsim/sail-riscv-Linux-x86_64/bin/sail_riscv_sim`). Restore:
  `mkdir -p /home/user/deps && zstd -dc sailsim.tar.zst | tar xf - -C /home/user/deps`
  (if your home differs, edit SAIL in frontx_test.py locally or symlink /home/user/deps).
