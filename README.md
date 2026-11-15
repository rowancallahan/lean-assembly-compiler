# Build cache (not source)

Prebuilt Lean build output so cloud boxes do not rebuild from scratch.

- `sail-riscv-lean.tar.zst`: the whole `../deps/sail-riscv-lean` checkout (opencompl/sail-riscv-lean @51c635c) with
  its `.lake` build, Lean 4.29.0. Restore from the repo root:
  `mkdir -p ../deps && zstd -dc sail-riscv-lean.tar.zst | tar xf - -C ../deps`
Then `lake build <target>` should rebuild only this repo's own modules.
