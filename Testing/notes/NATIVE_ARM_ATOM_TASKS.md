# M3 round 2: one simulation lemma per ATOM of the native image

Coordinator: NATIVE-ARM-PROOF (session_01MfKuVdPLvBuV5j9a1hUQC5). Base branch `nap-m2`. This replaces the
whole-template lemmas of round 1 as the path to the top theorem (round-1 files stay as checks; finish yours only if
it is one build away). Rules, build and report format: as in `Testing/notes/NATIVE_ARM_M3_TASKS.md` ("Rules").

## What changed
The image of a J program is a list of ATOMS (`Nano/Run/NatImg.lean`, `inductive NTm`, 19 kinds): `NTm.j` = the atom's
J instructions (1–3, or `liT`), `NTm.a π q h` = its A64 words, `NTm.ok` = its side conditions, `reads` / `writes` /
`kills` = its use of J registers. The segment law of the target is proved atom by atom.

## Your lemma
`theorem asim_<atom> (S : A64SemN M X W) {params} (hok : (NTm.<atom> params).ok = true) : ASim M X W (NTm.<atom> params)`
`ASim` is defined in `Nano/Run/NatSim.lean`; READ its definition and the worked case `asim_alu` there and copy that
proof's structure exactly:
1. `intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz`; unpack `hok`.
2. J side: get the J instruction(s) from `hJ i`, then `cases hrun with | head hS hs hrest`; `simp only [SafeX, c0] at
   hS` (side conditions: ranges, `wok` / `bok` / `sok` of the touched cells, no wrap) and `simp only [CallProbe.step,
   c0, Option.some.injEq] at hs; subst hs`. For an atom of 2–3 J instructions repeat on `hrest`; if `hrest` could be
   the empty run, `hz` (the run does not end inside the atom) excludes it: `cases hrest` gives `z = (q + 1, _)`,
   contradiction with `hz 1`. Then `m` = (number of J steps − 1).
3. A64 side: the words from `hA i` (`simpa [NTm.a] using …`), then the ArmNat steps (`Nano/Run/ArmNat.lean`) on the
   view `v`. Operands: `v.x r = st.x r` for every register the atom reads (`hag.x` + `hrd`); memory: `hag.m : v.m = st.m`.
4. Close with the final `NMid` at `π c.1` (`hft` for the fall-through, `htg` + the branch-offset shape for targets),
   the new agreement (`agree_wr … |>.mono`; for stores show `v'.m = c.2.m`), `b` / `ly` unchanged, and the exit kind.
Addresses: J uses `CallProbe.ea (st.x n) off` (an Int sum, `.toNat`); SafeX gives `0 ≤ x + off` and `wok K (ea …)`.
Branch words: `ArmEnc.bc c ((π p : Int) − (h + 1))` etc. match `n_cmpbr` / `n_cbz` / `n_cbnz` / `n_b` / `n_bl` with
`q' := π p` up to a `push_cast; omega` rewrite of the offset (see `n_ifHead` in ArmNatTm.lean).
Model-neutral: only `A64SemN` through ArmNat steps.

## Files and branches
Your file: `Nano/Run/NatA/<File>.lean` (new), first line `import Nano.Run.NatA.Base`, `namespace JT`, branch
`a-<name>` off `nap-m2`. The glob `Nano.Run.NatA.+` is already in `Arm/apc/lakefile.toml` (do not edit it).
Build: `cd Arm/apc && lake build Nano.Run.NatA.<File>`, or a `.build-request` on YOUR ref `build-slot-5-a-<name>`
(`dir: Arm/apc`, `targets: Nano.Run.NatA.<File>`). Missing ArmNat steps: write them in your file, section "for
ArmNat", and report them. First send a ≤ 6-line note only if the statement cannot be proved as given (e.g. `NTm.ok`
or `SafeX` does not give a needed fact): say exactly which fact is missing. Otherwise just build and report.

## Assignments
| task | atoms | file | notes |
|---|---|---|---|
| T01 | `li`, `addi` | `NatA/Li.lean` | `li d v` ↔ `liL`: J side is `liT d v` (1 or 17 J steps; use the J run lemma for `liT` in `Nano/Run/Expr.lean` or step it), A64 side your `n_li`. `addi d n imm`: `n = 0` → `liL` of the immediate; else `add` / `sub` imm (`n_addi` / `n_subi`) |
| T02 | `ld`, `sd` | `NatA/Mem.lean` | the 3 forms of `memW` (your `n_slotLd` / `n_slotSt` generalised from base x8 to any mapped base); `sd 0 n off`: `movz x17, #0` then the store of x17 |
| T03 | `ldp` | `NatA/Ldp.lean` | 2 J loads (either order, `sw`) ↔ `n_ldp`; `ok` gives x ≠ y, x ≠ n, y ≠ n |
| T04 | `cj` | `NatA/Cj.lean` | `b<c> a b 2; jal 0 off` ↔ `subs; b.<not c>`: J takes 1 step (compare true: to q+2) or 2 (the `jal`: to `jt q (1+off)`); A64 `n_cmpbr` with `cjC` |
| T05 | `bgeu` | `NatA/Bgeu.lean` | 1 J step ↔ `n_cmpbr` c = 2 |
| T06 | `lpz`, `bnez`, `beqz` | `NatA/Cbz.lean` | `n_cbnz` / `n_cbz`; `lpz` = `beq r 0 2; jal 0 off` (1 or 2 J steps) |
| T07 | `bgetI` | `NatA/BGetI.lean` | 3 J steps ↔ `n_addLsl3_16` + `n_ldr` (base 16); afterwards J 5, 6 are dead (`kills`), 14 written |
| T08 | `bsetI` | `NatA/BSetI.lean` | 3 J steps ↔ `n_addLsl3_16` + `n_str` (base 16); J 6 dead afterwards |
| T09 | `bpushI` | `NatA/BPushI.lean` | 2 J steps ↔ `add x15, x5, x7, lsl #3` (your general `n_addLsl3`) |
| T10 | `jal`, `jalr` | `NatA/Jump.lean` | `jal 0` ↔ `n_b`; `jal 1` ↔ `n_bl` (link: `hlo` gives `st.lo (q+1) = 4·(h+1)`, `hb`); `jalr 14` ↔ `n_br` (SafeX: `x14 = K.base + st.lo j`; `hlk` turns it into word `π j`; exit kind 3). `jalr 1`: same proof |
| T11 | `ldrbx` | `NatA/Ldrbx.lean` | `alu 1 d n m; lbu d d 0` ↔ `n_ldrbR` |
| T12 | `align8`, `sb` | `NatA/Start.lean` | `srli; slli` ↔ `movz x16, #3; lsrv; lslv` (your `n_alu16`); `sb s n 0` ↔ `n_strb` + byte store |
