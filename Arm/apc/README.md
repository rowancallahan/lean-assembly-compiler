# `Arm/apc`: the middle layer on DeepMind's AArch64 semantics, and a bridge to the Sail ARM model

Lean 4.34.1. Check everything: `Arm/apc/check.sh` (prints the axioms below). `NOTES.md` is the record of the
work on branch `apc` (paths there say `apc/`; this directory is that one, moved).

## Dependency (not in this repo)

`github.com/google-deepmind/code-verification` (Apache-2.0) at commit `b0f729a`, package `arm64`
(`arm64-semantics/Arm64/lakefile.toml`: `Arm64.lean`, `Arm64/Trusted`, `Arm64/Legacy`; no dependencies). Referenced
by path from `lakefile.toml` (`/home/user/deps/code-verification`), never copied. Set-up:

    cd /home/user/deps && git clone --filter=blob:none --no-checkout --sparse https://github.com/google-deepmind/code-verification.git
    cd code-verification && git sparse-checkout set arm64-semantics/Arm64 arm64-semantics/ProofLib && git checkout b0f729a

Their toolchain file says 4.34.0; `check.sh` builds `arm64` with Lean 4.34.1 (`lake` of 4.34.1 called directly,
nothing of theirs edited): 192 jobs, 162 s here. `ProofLib` (their program logic) is checked out but neither
built nor used.

## Files (ours)

| file | what |
|---|---|
| `Apc/Mach.lean` | `apc (L : Lay) : Machine`: all 9 laws of `Compiler/Iface.lean` on their `Arm64.Step` (`runsTo` = `Steps` to a state; `ok` = Running + code range executable + data range readable/writable; `writable` = data range; `keep` = x30, sp) |
| `Apc/Stack.lean` | `compile_apc` (expressions), `gcd_apc` (loop), `sort_apc` (insertion sort = `List.mergeSort`, region form) from `Machine.compile_ok` / `compF_ok` / `compAF_ok` |
| `Apc/Flags.lean`, `Apc/Agree.lean`, `Apc/AgreeAll.lean` | `agree_emitted`: on each of the 216 words of `emitted`, their `evalInst` = our small machine `armStep` (x0..x30, NZCV), PC + 4, mem/sp/status unchanged. NZCV identities by hand (no `bv_decide`) |
| `Apc/Small.lean` | verbatim copy of `AState`/`armStep`/`emitted` (`Arm/proofs/Arm/Small.lean`, `Words.lean`) so the lake package needs no Sail model; the bridge does NOT use it |
| `Bridge.lean` | `ArmProof.apc_eq_sail` (below); checked by `check.sh` in one environment with the Sail model |
| `stage.sh` | stages model-free source facts (gcd/sort `Exec` lemmas) from `Riscv/` into `Apc/Src/` (not committed), four one-line `simp` edits for 4.34 |
| `Apc/Emit.lean`, `test/` | emitted words and the QEMU / Sail-runner tests of branch `apc` (not re-run here) |

`lakefile.toml` takes `Spec/Code.lean`, `Spec/ArrCode.lean`, `Compiler/{Iface,Logic,Exp,Stmt,Mem,Arr}.lean` from the
repo root unchanged. These files are identical on `main` and on branch `apc` (the `writable` change was already
merged), so the 9 laws ported without any change.

## What is proved, on which model (checked here, 2026-11-14)

| theorem | model | axioms |
|---|---|---|
| `Proven.Apc.apc` (9 laws) | DeepMind `Arm64.Step` | propext, Classical.choice, Quot.sound |
| `Proven.Apc.compile_apc`, `gcd_apc`, `sort_apc` | DeepMind `Arm64.Steps` | same three |
| `Proven.Apc.agree_emitted` | DeepMind `evalInst` vs our `armStep` (in the bridge: `armStep`/`emitted` of `Arm/proofs`) | same three |
| `ArmProof.apc_eq_sail` | DeepMind `Arm64.Step` and Sail ARMv9 `stepModel` (`/home/user/armv9-lean`, `Reduce__1` partial) | same three |

`apc_eq_sail`: for each `w ∈ emitted`, from a Sail state `s` with `ArmFull s` and a DeepMind state `t` agreeing on
x0..x30, NZCV and PC (PC 4-aligned, `< 2^29`), both holding `w` at the PC (`MemWord`; `canExec` + `read32`), `t`
Running: one full Sail step and one DeepMind step succeed and end in states that again agree on x0..x30, NZCV and PC,
`ArmFull` holds again, and both memories are unchanged. Composition of `full_word` (`Arm/proofs/Arm/Full.lean`) and
`agree_emitted`.

**Scope of the bridge: the 216 expression words only** (`emitted`: add/sub/and/orr/eor/lsl/lsr/asr, cmp + cset,
cmp + csel, movz, add-imm, mov, for the register patterns the `Exp` compiler emits). Not in it: `ret`, branches
(`cbz`, `b`), loads/stores (`ldrb`/`strb`), `movk`; no relation between the two memories beyond the instruction word.
So `compile_apc`/`gcd_apc`/`sort_apc` are results on DeepMind's semantics (a hand-written user-mode model, tested
by them against Unicorn and Sail, not proved); only the expression words are tied to Sail by proof.

Deviations in `apc` (from `NOTES.md`): `li` is the doubling chain of `Arm/CompilerArm.lean` (`movz` + `add`), not
`movz/movk`; `bzOK n`/`jmpOK n` are `n < 1024` (decode facts by enumeration, `decide +kernel`); `sort_apc` is in
region form (no `ImplementsMapped`/`List UInt8` wrapper).

## Times (this box, 4 cores, one process; `check.sh` total 1366 s)

`arm64` 162 s (first build; 0 s when built) · Apc lake build 221 s (`Apc.Mach` 46 s, `AgreeAll` most of the rest) ·
`Arm/proofs/check.sh` 938 s (`Arm/Words` 646 s; skip with `SKIP_ARM=1` when `Arm/proofs/build` is current) ·
bridge: `Br/Agree` 12 s, `Br/AgreeAll` 192 s, `Bridge` 1 s.

## What remains for ARM

- `MachineF` (`Compiler/Frame.lean`: frames, spill slots, 8-byte `ld`/`sd`), calls (`Compiler/Call.lean`) and the
  wide laws (`Compiler/Wide.lean`) have no ARM instance, neither on DeepMind's semantics nor on Sail. On DeepMind's
  semantics they are the same pattern as the 9 laws (`ldr`/`str` with `fp` offsets; a reserved frame register).
- Bridge beyond expressions: Sail full-step lemmas for `cbz`, `b`, `ret` (`full_ret` exists), `ldrb`/`strb`, `movk`,
  and a stated relation between the Sail memory and DeepMind's `Memory` + permissions (byte or aligned accesses only:
  the Sail model faults on unaligned 8-byte accesses with the MMU off).
- Symbolic-immediate decode lemmas for `cbz`/`b` (to lift `n < 1024`), and the `ImplementsMapped` form of `sort_apc`.
