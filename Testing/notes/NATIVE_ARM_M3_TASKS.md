# M3 template tasks (native AArch64 proof): one helper per GenArm template kind

Coordinator: NATIVE-ARM-PROOF (session_01MfKuVdPLvBuV5j9a1hUQC5). Subject: `Nano/Codegen/GenArm.lean` at native-arm
d6db803 (do not edit it). Base branch: `nap-m2`. Read first: `Testing/notes/NATIVE_ARM_TEMPLATES.md` (your section:
the J list, the A64 word list, the alignment, the differences), `Nano/Run/ArmNat.lean` (the relation `NMid` and one
step lemma per A64 instruction: `n_movz n_movn n_movk n_addi n_subi n_addLsl3_16 n_alu n_mul n_cbz n_cbnz n_cmpbr n_b
n_bl n_br n_ldr n_str n_ldur n_stur n_ldp n_ldrbR nmid_scr nmid_set nmid_jump nmid_store8 nmid_byte`),
`Nano/Run/ArmNatTm.lean` (finished template lemmas: `n_push n_pop2 n_bin n_binMul n_rd n_ifHead n_loopHead
n_loopDec`: copy their style exactly), `Nano/Run/A64SemN.lean` + `A64Sem.lean` (the instruction facts).

## What a template lemma is
`theorem n_<kind> (S : A64SemN M X W) {h …} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
[(hL : A.length < 2 ^ 18)] (a0 : A[h]? = some (ArmEnc.… )) (a1 : A[h + 1]? = some …) … (side conditions) :
let st1 := … ; … ∃ s', Runs M s s' ∧ NMid X W K A s0 <final view> <final word index> s'`
* The words are given as hypotheses `A[h + i]? = some (ArmEnc.<enc> (armReg r) …)` (J register numbers through
  `armReg`: 5 6 7 8 14 15 ↦ same, 28 29 30 31 ↦ x12 x13 x10 x11, 1 ↦ x30, 10..13 ↦ x0..x3; scratch x16 / x17 are
  raw numbers). That GenArm's `a1`…`a36` produce these numbers is NOT your job (M4).
* The final view is written with `CallProbe.wr`, `CallProbe.upd`, `{ st with m := … }`, `CallProbe.lbm`, `CallProbe.sbm`
  applied to the start view `st`, in the order the A64 instructions act (nested `let`s as in `n_bin`). It must be what
  the A64 code does; matching it with the J template's result is a later step, but choose the form closest to the J
  template's state (same `wr` targets) wherever the two agree.
* Memory side conditions as hypotheses: `wok K a` for every 8-byte cell read or written, `bok K a` for a byte read,
  `sok K a` for a byte written; branch targets as word indices with `≤ A.length`.
* Model-neutral: only `A64SemN` fields through ArmNat's steps. Nothing about armDM, Sail, permissions or decoding.
* Value-dependent shapes (li: 1..4 words; slot access: 1 or 2 words): one lemma per shape, then one lemma over the
  emitting function's case split if you can state it cleanly; say in your plan which.

## Rules
* Your file: `Nano/Run/NatT/<File>.lean` (new), `import Nano.Run.NatT.Base`, `namespace JT`. Your branch:
  `m3-<kind>` off `nap-m2`. Touch nothing else. If you need a new instruction step or a shared helper (e.g. a raw
  x16-base variant, the byte store `nmid_store1` + `n_strb`), put it in YOUR file under a clearly marked section
  "for ArmNat" and tell the coordinator; it is moved to ArmNat when merged. If you need a lemma of another task,
  state it as a hypothesis-free `theorem` in your plan and ask; do not wait: take the other task's statement from
  this file's table and prove yours against a local copy of the statement only if the coordinator says so.
* No `sorry`, `admit`, `native_decide`, `bv_decide`, new axioms; `decide`, `omega`, `simp`, `bv_omega` are fine.
  No `Spec/` change. Short proofs: compose the step lemmas; do not unfold `A64SemN`.
* First message to the coordinator (≤ 10 lines): the exact statement(s) you propose, the proof plan (which steps in
  which order), A64SemN facts / ArmNat steps you are missing, risks. Then draft and build; do not wait for an answer
  unless the statement is in doubt.
* Build: `cd Arm/apc && lake build Nano.Run.NatT.<File>` (Lean 4.34.1; set-up in `Arm/apc/README.md`: elan +
  `/home/user/deps/code-verification` at b0f729a, about 5 min the first time; the glob `Nano.Run.NatT.+` is already
  in `Arm/apc/lakefile.toml`, so do not edit the lakefile). If you cannot build locally, push a commit with a
  `.build-request` file at the repo root to YOUR OWN ref `build-slot-5-<kind>` (`reply: <your session id>` /
  `targets: Nano.Run.NatT.<File>` / `dir: Arm/apc`), and remove that file from your branch.
* Report (≤ 8 lines) when it builds: branch + sha, statements, anything GenArm does that surprised you, what is not
  done. Commit trailers as the lead gave them. Low token use.

## Assignments
| task | kind | notes section | file | content |
|---|---|---|---|---|
| T01 | li (constants) | 2, 2a | `NatT/Li.lean` | `a6`/`a7`/`a8`: movz; movn; movz/movn + movk chain over the 16-bit chunks; result `wr st d v` for every v; CONST = li + `n_push` |
| T02 | slot access + signed add | 3 | `NatT/Slot.lean` | `a9` load and store in its 3 reachable forms (`ldr`/`str` uimm, `ldur`/`stur`, `sub x16` + `ldr`/`str [x16]`), `a5` (add/sub imm form); address = `(st.x 8).toNat + off` as an Int offset |
| T03 | LOCAL | 4 | `NatT/Local.lean` | per word: slot load into x5 (use T02's statement) + `n_push`; then the w-word induction |
| T04 | pop into slots (LET, CONTINUE) | 5 | `NatT/PopSlot.lean` | per word: `ldr x5,[x11]; add x11,#8;` slot store (T02); then the w-word induction |
| T05 | ISIZE / LEN, BSIZE | 8.1, 8.4 | `NatT/PrimSmall.lean` | the three small prims |
| T06 | BNEW | 8.3 | `NatT/BNew.lean` | uses li (T01's statement) twice, room check `subs`+`b.lo` to word 1, `movz x17,#0; str x17`, `n_push` |
| T07 | BGET | 8.5 | `NatT/BGet.lean` | bounds check, `add x16, x5, x6, lsl 3`, `ldr [x16,#16]`; note the dead temporaries |
| T08 | BSET | 8.6 | `NatT/BSet.lean` | as BGET with the store |
| T09 | BPUSH / PUT | 8.7 | `NatT/BPush.lean` | both branches |
| T10 | def prologue | 12 | `NatT/Prologue.lean` | `a26`: frame set-up, room check to word 1, saves |
| T11 | def epilogue | 13 | `NatT/Epilogue.lean` | `epi`: loads, result copy loop (q words), `br x14` (`n_br`) |
| T12 | stubs, start code | 14, 15 | `NatT/Start.lean` | word 0 jump, both stubs, the 34-word start code incl. the byte copy loop; needs `n_strb` + the byte store on `NMid` (write them, section "for ArmNat"; pattern: `mid_store1` in `Nano/Run/ArmTarget.lean`) |
