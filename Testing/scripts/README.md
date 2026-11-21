# Testing/scripts

Gates and checks run on the whole checkout. The one-command release check is `release_check.sh` (see its header for
the gates and knobs); the other scripts are its parts or stand-alone tools.

## Self-hosting guards (owner rule: self-hosting is a gate on every merge)

| script | what |
|---|---|
| `selfhost_gate.sh [WORKDIR]` | one PASS/FAIL line per step, exit 1 on any FAIL: **gen** (the self-host proofs `Nano/SelfHost/{Cert,SrcLink}` regenerate from C's current source with no change), **fix** (B1 via Lean → B2 = committed `B2.bin`, B2 → B3 = B2), **arm** (rebuilt native-ARM compiler = committed `native_arm/GA_arm.bin`, it compiles its own source to itself, its B2 build reproduces `B2.bin`, examples + edge programs), **cross** (RISC-V / rv2arm / native builds of both compilers agree), **subset** (`subset_check.sh`, when present). Also `release_check.sh` gate `selfhost` |
| `regress_fuzz.py [-n N] [--old-rv …] [--old-arm …]` | an OLD compiler binary (default: the one at `origin/main`) vs the NEW one (working tree), RISC-V and native ARM: the same programs (examples, C's source, N fuzz programs of 4 families) must be accepted alike and RUN alike on QEMU (status and output bytes; code bytes may differ). Prints `*** REGRESSION …` and exits 1 on any difference |
| `lean_run.sh FILE ARGS` | `lean --run` with the repo modules: `lake env` when the project's dependencies are present, else it builds only FILE's import closure with plain `lean` (cached) |

Binaries legitimately change when the compiler changes: the gate checks consistency (committed = rebuilt, fixed
points), never equality with an old release's hashes. The sha256s it prints are for the record.
Needs: elan (this checkout's toolchain, with `leanc`), python3, `riscv64-linux-gnu-gcc`, `aarch64-linux-gnu-gcc`,
`qemu-riscv64`, `qemu-aarch64`.
After a compiler change: rebuild and commit `B2.bin`/`B2.sha256`/`B3.bin` (`boot/fixpoint.sh`), the generated proofs
(`cert/gen_cert.py`, `srclink/gen.lean … 800`), and `native_arm/GA_arm.bin` + `SHA256SUMS` (`native_arm/test_native.sh`),
then run `selfhost_gate.sh` and `regress_fuzz.py`.
