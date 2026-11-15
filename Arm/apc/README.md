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
| `Apc/Mach.lean` | `apc (L : Lay) : Machine`: all 9 laws of `Compiler/Iface.lean` on their `Arm64.Step` (`runsTo` = `Steps` to a state; `ok` = Running + code range executable + data range readable/writable; `writable` = data range; `keep` = sp and every register outside the abstract ones x0..x7, x9..x15, i.e. x8, x16..x30). `li` = `movz` (+ 3 `movk`), `bz` = `cbz` (`n < 2^18`), `jmp` = `b` (`0 < n ≤ 2^25`) |
| `Apc/Sym.lean` | symbolic-immediate decoding: a template word (literal opcode bits ++ symbolic fields) is decoded by `simp`, each opcode test decided from the known bits (`tst_false`/`tst_true`/`tst_eq`); `movz`/`movk` (any chunk), `b`/`bl` (26-bit), `cbz`/`b.cond` (19-bit); `li4` (`movz`+3 `movk` = the constant), `off_fwd`/`off_back` |
| `Apc/Mem8.lean` | 8-byte memory: `read64`/`write64` against our byte view (`Mem.wr`, `le8`), `Pres` (stores keep permissions), stores never touch executable bytes (`w64_code`) |
| `Apc/Frame.lean` | `apcF L : MachineF` (frame register x28; `enter n` = `sub x9, sp, #8(n+1); str x28, [x9]; mov x28, x9; str xzr, [x28, #8(j+1)]…`, `leave` = `ldr x28, [x28]`, slots `[x28, #8(j+1)]`, `ld`/`sd` = `ldr`/`str [xa]`; frame `[sp - 8(n+1), sp)`, `enterOK`: n ≤ 16, sp 8-aligned, frame in the data range) |
| `Apc/Msort.lean` | `msort_apc`: the branchy merge sort `msortProgB` (`Riscv/Examples/MsortB.lean`, source proof staged unchanged) = `List.mergeSort`, through `MachineF.compBF_ok` |
| `Apc/Call.lean`, `Apc/Calls.lean` | `apcC L : MachineC` (`call` = `bl` (±2^25 words), link x30; `enterC` = `sub x28, x28, #8(n+1); str x30, [x28]`; `leaveC` = `ldr x30, [x28]; add x28, …`; `stA` = `stur [x28, #-8m]`); `ImplementsA` (the ARM analogue of `ImplementsW`), `callsCode_implements_apc`, `sumTo_apc`, `fib_apc`, `isEven_apc`, `treeEval_apc` (source proofs of `Riscv/Examples/{CallExamples,TreeEval}.lean` staged unchanged; `wf_apc` checks well-formedness by evaluation) |
| `Apc/WideDec.lean`, `Apc/Wide.lean` | `apcw L : Wide`, `apcwF L : WideF`: every wide operation with ARBITRARY registers (register fields decoded by enumeration, `decide +kernel`, ≈ 5 min; branch offsets symbolic). `immOK = false` (immediates go through the scratch register), `offOK off := off = 0` (the only offset the selection emits), `br` = `cmp; b.cond` (fwd `1 ≤ n ≤ 2^18`, back `n < 2^18`), `jmp` = `b` |
| `Apc/Opt.lean` | `compBFOA L N bv wv p` = the optimised words (`WideF.optB` over `apcwF`, register assignment by the untrusted search of `Riscv/Back/OptB.lean`, staged) or the `compBF` words; `compBFOA_ok` (conclusion of `compBF_ok`); `optB_L` (optimised words independent of the layout); `msortO_apc`; CRC-32: `crc_apc_of`, `crc_apc` (unoptimised), `crcO_apc` (optimised; source proof `crcP_exec` staged) |
| `mid.patch` | the middle-layer change ARM needs, applied by `stage.sh` to copies of `Compiler/{Frame,BExp,BStmt,Call,CStmt,CProg,Wide,Opt/Lower}.lean` in `Mid/` (not committed): `writable` hypotheses on the store laws (below) |
| `cut.py` | stage helper: drops the RISC-V-only `_wf`/`_implements` theorems of an example file |
| `Apc/Stack.lean` | `compile_apc` (expressions), `gcd_apc` (loop), `sort_apc` (insertion sort = `List.mergeSort`, region form) from `Machine.compile_ok` / `compF_ok` / `compAF_ok` |
| `Apc/Flags.lean`, `Apc/Agree.lean`, `Apc/AgreeAll.lean` | `agree_emitted`: on each of the 216 words of `emitted`, their `evalInst` = our small machine `armStep` (x0..x30, NZCV), PC + 4, mem/sp/status unchanged. NZCV identities by hand (no `bv_decide`) |
| `Apc/Small.lean` | verbatim copy of `AState`/`armStep`/`emitted` (`Arm/proofs/Arm/Small.lean`, `Words.lean`) so the lake package needs no Sail model; the bridge does NOT use it |
| `Bridge.lean` | `ArmProof.apc_eq_sail` (below); checked by `check.sh` in one environment with the Sail model |
| `stage.sh` | stages model-free source facts from `Riscv/` into `Apc/Src/` (not committed): gcd/sort `Exec` lemmas, `BStmt` + both merge sorts, `toMS`, `Computes` + call examples, `Implements1Ex`/`Crc` heads, the OptB search (over `apcwF L0`); one-line `simp`/`show` edits for 4.34 (listed in the script) |
| `Apc/Emit.lean`, `test/{loop,sort}_test.py` | emitted words and the QEMU / Sail-runner tests of branch `apc` (not re-run here) |
| `Apc/Emit2.lean`, `test/words2.txt`, `test/ext_test.py` | words of the new examples (`lake env lean Apc/Emit2.lean > test/words2.txt`) and their QEMU test |

`lakefile.toml` takes `Spec/{Code,ArrCode,Encode,Tree}.lean`, `Compiler/{Iface,Logic,Exp,Stmt,Mem,Arr,BLang,CLang}.lean`
and `Compiler/Opt/*` (except `Lower`) from the repo root unchanged, and the patched copies from `Mid/`. These files are identical on `main` and on branch `apc` (the `writable` change was already
merged), so the 9 laws ported without any change.

## What is proved, on which model (checked here, 2026-11-14; re-checked 2026-11-15)

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

Since 2026-11-15 `li` is `movz` (+ 3 `movk`), not the doubling chain of `Arm/CompilerArm.lean` that `emitted` holds:
the `li` words of `compile_apc` / `gcd_apc` / `sort_apc` are no longer among the 216 bridged words (all other
words are).

## Frames, calls, the optimising back end (2026-11-15)

| theorem | what | axioms |
|---|---|---|
| `Proven.Apc.apcF` | `MachineF` (frames, spill slots, 8-byte `ld`/`sd`) | propext, Classical.choice, Quot.sound |
| `Proven.Apc.msort_apc` | branchy merge sort `msortProgB` = `List.mergeSort` (region form, as `sort_apc`) | same three |
| `Proven.Apc.apcC` | `MachineC` (calls) | same three |
| `Proven.Apc.callsCode_implements_apc` | every well-formed program with calls whose source run computes `f` within `need n` stack bytes implements `f` (`ImplementsA`, `space n = need n + 16`) | same three |
| `Proven.Apc.sumTo_apc`, `fib_apc`, `isEven_apc`, `treeEval_apc` | the call clients (recursion, mutual recursion, recursive-descent tree evaluator) | same three |
| `Proven.Apc.apcw`, `apcwF` | `Wide`, `WideF` (any registers) | same three |
| `Proven.Apc.compBFOA_ok` | the optimising spill-slot compiler (search + `optB`, fallback `compBF`) | same three |
| `Proven.Apc.msortO_apc` | optimised branchy merge sort = `List.mergeSort` | same three |
| `Proven.Apc.crc_apc_of`, `crc_apc`, `crcO_apc` | CRC-32 (`crc32` of `Riscv/Examples/Crc.lean`), unoptimised and optimised words | same three |

**The interface change (`mid.patch`).** DeepMind's memory refuses stores to bytes that are not `w ∧ ¬x`
(`Memory.canWrite`), so code bytes are never writable. The store laws of `MachineF` (`law_stS`, `law_sd`), `MachineC`
(`law_enterC`, `law_stA`) and `Wide` (`w_stS`, `w_sd`) assume only "in RAM", and RAM must contain the code
(`codeOK`); a store into the code would fault, so these laws cannot be proved on this model as stated (`law_sb` /
`w_sb` already take `writable`). `mid.patch` adds `(∀ i < 8, writable s (addr + i))` to those six laws, writability
of the frame to `enterOK_frame` (as `WideF.enterOK_frame` already has) and to `Frm`, of word blocks to `Lay`/`PLay`/
`Ctx` (`wwr`), of the stack area to `PLay`/`Ctx` (`stw`), and threads them through the proofs (≈ 40 changed lines,
`Mid/` holds the patched copies). It is the "to do: give them `writable` too" of `Testing/notes/MACH.md`; RISC-V
satisfies the new hypotheses trivially (its laws ignore them). Until it is upstreamed, `stage.sh` must find the
root files as the patch expects (it fails loudly otherwise). One more hunk is a 4.34 `simpa` fix in `Opt/Lower.lean`.

Code and layout: the theorems quantify over the layout `L` and state the code as `(apcF L).codeF …` /
`callsCode L …` / `compBFOA L …`; the words do not depend on `L` (the encodings ignore it; `optB_L` proves it for the
optimised words), and `Apc/Emit2.lean` prints them for `L0`.

**Tests** (`python3 test/ext_test.py KIND DIR 300`, qemu-system-aarch64 virt / cortex-a72; output, input unchanged,
guard bytes, sp and x28 restored): msort (507 words), msortO (244), crc (218), crcO (170), sumTo (59), fib (76),
isEven (77), tree (100): 300 inputs each, 0 mismatches (a mutated word gives 40/50 mismatches).
`test/sort_test.py` re-run with the new `li` (`test/words.txt` re-emitted): 300/300; `loop_test.py` (needs the
Sail runner of branch `arm-exe`) not re-run.

Remaining deviations: register fields of the wide operations are decoded by enumeration (`Apc/WideDec.lean`,
≈ 5 min); `immOK = false`; `offOK off := off = 0`; `sort_apc` / `msort*_apc` / `crc*` are in region form (no
`ImplementsMapped` / `Implements1` wrapper on this model); `stS`/`ldS` slots `< 16`.

## Times (this box, 4 cores, one process)

2026-11-15, `SKIP_ARM=1 ./check.sh` with the `Apc`/`Compiler` oleans removed: 620 s — `arm64` 0 s (built) · Apc lake
build 414 s (`Apc.WideDec` ≈ 345 s of it: the register enumerations) · bridge 205 s (`Br/AgreeAll` 190 s).
Earlier (2026-11-14, total 1366 s): `arm64` 162 s on a first build, `Arm/proofs/check.sh` 938 s (`Arm/Words` 646 s;
skip with `SKIP_ARM=1` when `Arm/proofs/build` is current).

## What remains for ARM

- Upstream `mid.patch` into `Compiler/` (RISC-V instances need only `_` for the new hypotheses).
- Symbolic decoding of the register fields (the `Apc/Sym.lean` method applies; would remove the 5-minute
  enumeration), immediate forms for `bini`, nonzero load/store offsets.
- Bridge beyond expressions: Sail full-step lemmas for `cbz`, `b`, `bl`, `b.cond`, `ret` (`full_ret` exists),
  `ldrb`/`strb`, `ldr`/`str`/`stur`, `movz`/`movk`, and a stated relation between the Sail memory and DeepMind's
  `Memory` + permissions (byte or aligned accesses only: the Sail model faults on unaligned 8-byte accesses with the
  MMU off).
- `ImplementsMapped` / `Implements1` statement forms on this model.
