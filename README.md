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
- `repo-build.tar.zst.part-aa` … `-ad`: this repo's `.lake/build` at main f1cfb76 (2026-11-17: paged arrays, con-leche hard cases, round 1, IR S3; Lean 4.29.0), zstd, split in
  90 MB parts. Restore from the repo root (after the Sail dependency above):
  `for p in $(git ls-tree --name-only origin/build-cache | grep '^repo-build.tar.zst.part-' | sort); do git show origin/build-cache:$p; done | zstd -dc | tar xf -`
  Then `lake build` rebuilds only modules changed since f1cfb76.
- No zstd on the box? `apt-get install -y zstd` (package registries are reachable), or ask the parent for .tar.gz.

## Without zstd: gzip copies (same contents)
- `sail-riscv-lean.tar.gz`: `mkdir -p ../deps && git show origin/build-cache:sail-riscv-lean.tar.gz | tar xzf - -C ../deps`
- `sailsim.tar.gz`: `mkdir -p /home/user/deps && git show origin/build-cache:sailsim.tar.gz | tar xzf - -C /home/user/deps`
- repo-build: zstd only from f1cfb76 on (the environment's setup script installs zstd); older gzip parts removed.
