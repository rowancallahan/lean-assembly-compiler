# CONLECHE_S2 status

## Setup

| Step | Result |
|---|---|
| 1. `git fetch origin build-cache main` | done |
| 2. `git show origin/build-cache:sail-riscv-lean.tar.zst \| zstd -dc \| tar xf - -C ../deps` | **FAILED** |
| 3. sailsim extraction to /home/user/deps | not attempted (stopped at step 2 failure) |
| 4. `git merge origin/main` | not attempted |
| 5. elan install + `lake build Frontx` | not attempted |

Exact error (step 2; step 3 fails identically):

```
/bin/bash: line 1: zstd: command not found
tar: This does not look like a tar archive
tar: Exiting with failure status due to previous errors
```

`which zstd` returns nothing in this container. The downloaded archive `/tmp/s.tar.zst` was not decompressed.

## Targets

Not started. No functions were gated, compiled, emitted, or tested.
