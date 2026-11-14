# apc: AlphaProof-Code AArch64 semantics as an additional ARM target (evaluation, second box)

Source: github.com/google-deepmind/code-verification at b0f729a (blobless + sparse clone, 12,002 files in the tree).
Nothing of theirs is copied into this repo; `apc/lakefile.toml` requires their `arm64` package by path
(`../deps/code-verification`, a clone next to the repo). Our own files used: `Spec/Code.lean`, `Compiler/Iface.lean`
(from the repo root, unchanged), and a verbatim copy of our `AState`/`armStep`/`emitted` in `apc/Apc/Small.lean`.

## 1. Facts about their repo
- LICENSE (top level): "All code is licensed under the Apache License, Version 2.0", Copyright 2026 Google LLC.
  Exceptions listed there: `third_party/hashbrown-0.17.1` (MIT), `third_party/libsignal` (AGPL-3), ELF binaries containing
  MIT code. `arm64-semantics/LICENSE` is the full Apache-2.0 text (202 lines). So depending on or vendoring
  `arm64-semantics/Arm64` is permitted under Apache-2.0 conditions (keep license + notices, state changes).
  This is my reading of the files, not a legal review.
- Lean: `leanprover/lean4:v4.34.0` (root and `arm64-semantics`).
- Dependencies: package `arm64` (`arm64-semantics/Arm64/lakefile.toml`): NONE (no Std package, no Mathlib).
  `prooflib` requires only `arm64`. Mathlib comes in only at the repo root via VCVio (crypto game definitions) and dylean.
- Layout (`arm64-semantics/`): `Arm64/Trusted` (TCB, definitions only), `Arm64/Testing` (66 files, 33,007 lines),
  `ProofLib` (untrusted: tactics, symbolic execution, separation logic; 315 files, 184,747 lines),
  `VerifiedLibraries` (209 files, 118,338), `CaseStudies` (64 files, 52,859), `tools` (Rust). Repo root: `LibsignalBinary`,
  `Computational`, `Symbolic`.
- Trusted semantics, `wc -l` (comments included; 16,767 lines in `Arm64/Trusted`):
  | part | files | lines |
  |---|---|---|
  | ISA: Syntax 631, Decode 1299, Memory 397, State 689, Float 793, Eval 3072, Semantics 285 | 7 | 7,166 |
  | Syscalls (model of 31 Linux syscalls) | 27 | 2,774 |
  | Process (ELF parse/load, `ElfRunsTo`) | 7 | 1,715 |
  | Object (relocatable objects, placement) | 3 | 1,276 |
  | Spec (SepLogic 581, Hoare 525, Rust/alloc contracts) | 9 | 1,967 |
  | Surface (spec DSL elaborators) | 6 | 1,779 |
- Build on this box (4 cores, 15 GB, no swap): `lake -d Arm64 build` (trusted semantics, incl. native precompile):
  192 jobs, 50 s wall, peak RSS 1.07 GB. `lake -d ProofLib build`: see end of file.

## 2. The semantics (quotes from `Arm64/Trusted/ISA/*.lean`)
State (`State.lean`): one record, total functions, no monad.

    structure State where
      regs : RegFile          -- regs : BitVec 5 → BitVec 64   (x0..x30; index 31 unused)
      vregs : VRegFile        -- BitVec 5 → BitVec 128
      sp pc : BitVec 64
      pstate : PState         -- n z c v : Bool
      mem : Memory
      status : ExecStatus     -- Running | Halted | Exited c | Signaled s | Panicked | OutOfMemory | Exception msg ...
      tpidrEl0, fpsr, brk, fs (file system), oracle, exclFails, trace, symtab, sigActions, physMemAvail, ...

Register access distinguishes xzr / sp syntactically in the decoded instruction:

    def readReg64 (s : State) (r : Reg) : BitVec 64 :=
      match r with | .gpr idx => if idx == 31#5 then 0#64 else s.regs.read idx | .sp => s.sp | .xzr => 0#64

Memory (`Memory.lean`): byte cells with optional permission.

    structure Perm where r w x : Bool; lazyFree : Bool := false; anon : Bool := true
    structure Memory where cells : BitVec 64 → Option (Option Perm × BitVec 8)
    def read8 (m) (addr) : BitVec 8 := match m.cells addr with | some (_, b) => b | none => 0#8
    def canRead  m addr n := m.allPerm (·.r) addr n && m.allNoLazyFree addr n
    def canWrite m addr n := m.allPerm (fun p => p.w && !p.x) addr n      -- W^X: executable bytes are never writable
    def canExec  m addr n := m.allPerm (·.x) addr n

Loads/stores check permission and otherwise set a fault status (no exception vector, no alignment requirement on data):

    def execStr size rt addr s := if !checkAddrSPAligned s addr then s.setStatus (.Exception "SP alignment fault") else
      let (ea, wb) := evalAddrMode s addr
      if !s.mem.canWrite ea size.bytes then s.setStatus (.Exception "permission fault") else ... writeSized ... advancePC

Fetch/decode (`Semantics.lean`, `Decode.lean`): from memory, every step.

    def decode (w : BitVec 32) : Option Instr            -- Instr: inductive AST, 467 instructions per their README
    def fetchMem (prog : Program) (m : Memory) (pc : BitVec 64) : Option Instr :=
      if (prog.externAt? pc).isSome then none else if pc.toNat % 4 ≠ 0 then none
      else if !m.canExec pc 4 then none else decode (m.read32 pc)

Execution: a pure function per instruction, e.g.

    | .b offset => s.setPC (s.pc + offset)
    | .ret rn => s.setPC (s.readReg64 rn)
    def execAddSubShift w op rd rn rm shift amount s :=
      let (res, optPs) := evalAddSub w op (s.readReg w rn) (shiftVal w (s.readReg w rm) shift amount) none
      let s1 := s.writeReg w rd res; (match optPs with | some ps => s1.setPState ps | none => s1).advancePC

Step relation (deterministic; `prog` carries hooks for extern functions and the `svc` handler):

    inductive Step (prog : Program) : State → State → Prop where
      | exec (h_run : s.status = .Running) (h_fetch : prog.fetchMem s.mem s.pc = some inst) : Step prog s (prog.evalInst inst s)
      | halt_unmapped (h_run) (h_fetch : ... = none) (h_ext : prog.externAt? s.pc = none) : Step prog s { s with status := .Halted }
      | extern ... | extern_fault ...
    inductive Steps (prog) : State → State → Prop      -- reflexive-transitive closure

Whole-program statement (`Process/Semantics.lean`):

    def ElfRunsTo (elfBytes : List (BitVec 8)) (pre : ProcessInputs → Prop) (post : ProcessInputs → ProcessOutcome → Prop)
        (oom := fun _ _ => False) (prog : Program := Program.pureMem) : Prop :=
      ∃ img, ElfImage.parse elfBytes = .ok img ∧ ∀ inputs, pre inputs →
        ∃ s0, img.loadState inputs = .ok s0 ∧ ProcessRunsTo prog s0 (post inputs) (oom inputs)
    -- ProcessRunsTo = ProcessTerminates (exits with an outcome satisfying post) ∧ ProcessPartialRunsTo (every reachable
    --   state is terminated-with-post, or OOM, or Running with a next step)

Function-level statement (`Spec/Hoare.lean`): `subroutine_ok prog entry spec := ∀ x R s0, s0.pc = entry → Running →
(s0.mem ⊨ spec.pre x s0 ∗ R) → sp aligned → reaches_outcome ...` (separation-logic frame `R` built in).
Scope: user mode only. No exception levels, no system registers, no MMU; a fault is a status value.

## 3. Our interface on their semantics (prototype, `apc/Apc/Inst.lean`, 113 lines, Lean 4.34.0)
`Spec/Code.lean` and `Compiler/Iface.lean` compile unchanged under 4.34.0 next to `import Arm64` (only these two of our
files were tried under 4.34.0). Chosen instance data: `S := Arm64.State`, program `Program.ofSvc noSyscalls` (no hooks),
`runsTo s Q := ∃ s', Steps P s s' ∧ Q s'`, `ok s := s.status = .Running`, `get s r := s.regs.read (xr r)` with the
register map of `Arm/CompilerArm.lean`, `instrAt s pc w := s.mem.canExec pc 4 ∧ s.mem.read32 pc = w`,
`keep := x30 and sp unchanged`, `ra := x30`, `mem` unchanged stated as `s'.mem = s.mem`.

PROVED (no `sorry`; axioms `propext`, `Quot.sound` only; whole file builds in 7 s):
| law | words | decode lemma | law proof | edit-build rounds |
|---|---|---|---|---|
| `law_mov` (all 15 x 15 register pairs) | `orr xd, xzr, xa` | `decide` over 225 pairs | 12 lines | 3 |
| `law_bin_add` (d < 10, a = d, b = d+1 as in the interface) | `add xd, xa, xb` | `decide` over 10 | 13 lines | 2 |
| `law_ret` | `ret` (x30) | `decide` | 4 lines | 2 |
Generic part: `step_of` (aligned PC + `instrAt` + decode => one `Step`), 8 lines.
I did not time myself with a clock (this box's clock is unreliable across suspends); the three laws plus set-up took
7 build rounds in total. The laws are stated with the instance's own predicates, not yet packaged as a `Machine`
value (that needs all 9 laws and `Core`).

What blocks or needs a decision:
1. `law_sb` vs W^X. Our interface has ONE RAM range holding code and data and `law_sb` writes anywhere `inRAM`. Their
   `canWrite` requires `!x`, and code must be `x`. So `law_sb` as stated is FALSE on their semantics for an address inside
   the code. Needs an interface change: a separate data range (or a writability hypothesis) in `Base`.
2. `instrAt_frame` (Core): hypothesis is "our `mem` agrees on the 4 bytes". On their semantics an instruction also needs
   the `x` permission, which `mem : Nat → Option (BitVec 8)` does not carry. Either `mem` is defined to be `some` only on
   non-executable bytes and `instrAt_frame` is replaced by "code is frozen" (their `Memory.KeepsFrozen` gives exactly
   this for every step), or the law is weakened. Small change, but a change.
3. Our `mem : Nat → Option (BitVec 8)` vs their total `read8` + permissions: natural definition
   `mem s a = if canRead/canWrite at a then some (read8 a) else none`; not exercised by the three laws proved.
4. PC / branches: PC is a `BitVec 64`, branch offsets are decoded sign-extended 64-bit values added to the PC. `bz n`
   = `cbz` (imm19, so `bzOK n := n < 2^18`), `jmp n` = `b` backwards (imm26). No PC bound like `pc < 2^29` (Sail route).
5. Flags: `bin ult/slt/eq` and `sel` change NZCV; the interface frame `keep` must not mention flags (ours does not).
6. Lean version: theirs 4.34.0; our middle layer is known on 4.29 and 4.34.1. Not tried: the rest of `Compiler/*` on
   4.34.0, and their `arm64` package on 4.34.1 (needed to put it in one environment with the Sail model).
7. No control-state pins are needed (compare `ArmFull`: EL3, MMU off, SPE, branch-type registers ... on the Sail route).
Not blockers: state type (plain record, `simp` unfolds one instruction in < 1 s), `ret` convention (x30).

## 4. Comparison with the Sail route (`apc/Apc/Agree.lean`, `AgreeAll.lean`)
Same shape: yes. Their per-instruction semantics is a pure function on (regs, flags, pc, mem), as is our `armStep`.
PROVED here (`agree_emitted`, 216 words = the list `emitted` that `armStep_ok` / `full_word` on main range over):

    def abs (s : Arm64.State) : AState := { x := fun i => if i < 31 then s.regs.read (BitVec.ofNat 5 i) else 0, n z c v := s.pstate.* }
    def Agree (w : BitVec 32) : Prop := ∃ i, Arm64.decode w = some i ∧ ∀ s : Arm64.State,
      abs (Pg.evalInst i s) = armStep w (abs s) ∧ (Pg.evalInst i s).pc = s.pc + 4 ∧
      (Pg.evalInst i s).mem = s.mem ∧ (Pg.evalInst i s).sp = s.sp ∧ (Pg.evalInst i s).status = s.status
    theorem agree_emitted : ∀ w ∈ emitted, Agree w

One tactic (`agree`, 15 lines) does all 14 instruction classes (add sub subs and orr eor lslv lsrv asrv csel csinc movz
add-imm subs-imm); 216 words check in 3 min. CAVEAT: the NZCV goals of the `subs` words are closed by `bv_decide`, so
`#print axioms agree_emitted` lists 49 `bv_decide` native-evaluation axioms besides propext / Classical.choice /
Quot.sound; the other classes use no such axiom. A hand proof of the three flag identities would remove them.
`armStep`, `AState`, `emitted` are a verbatim copy (`Apc/Small.lean`), not an import, because `Arm/proofs/Arm/Small.lean`
imports the Sail model, which is not built in this 4.34.0 environment.

Can agreement with the Sail model be PROVED by composition: yes, the two halves exist. The theorem would be

    theorem apc_eq_sail {w} (hw : w ∈ emitted) {s : St} {t : Arm64.State} (hf : ArmFull s) (ha : Abs s (abs t))
        (hpc : s.regs.get? ._PC = some t.pc) (hlt : t.pc.toNat < 2^29) (hal : t.pc.toNat % 4 = 0)
        (hm : MemWord s.mem t.pc.toNat w) (hi : instrAt t t.pc w) (hrun : t.status = .Running) :
        ∃ s' t', stepModel s = .ok () s' ∧ Arm64.Step P t t' ∧ Abs s' (abs t') ∧ ArmFull s' ∧
          s'.regs.get? ._PC = some t'.pc ∧ s'.mem = s.mem ∧ t'.mem = t.mem

proof = `full_word` (main, `Arm/proofs/Arm/Full.lean`) for the Sail side, `agree_emitted` + `step_of` (here) for theirs,
glued through `armStep w (abs t)`. Missing:
(a) one Lean environment holding both: the Sail model is built with 4.34.1, their package pins 4.34.0 (untested either way);
(b) `ret` is not in `armStep`/`emitted` (needs its own Sail lemma; `Arm/proofs/Arm/Ret.lean` exists on main, not looked at);
(c) a stated relation between the two memories beyond the instruction bytes (Sail `mem` vs their `Memory` + permissions),
    needed as soon as loads/stores are in the subset; and the Sail model's alignment fault on unaligned 8-byte accesses
    with the MMU off (found in the heavy-testing round) has no counterpart in their semantics, so the memory subset
    must be restricted to byte or aligned accesses for agreement to hold;
(d) the `bv_decide` axioms above, if axiom-free is required.
This would be a theorem about 216 enumerated words; for arbitrary registers their side is already generic
(`law_mov`, `law_bin_add`), the Sail side is the enumerated one.

## 5. Recommendation (estimates are mine; evidence is the prototype above)
- Their semantics as an additional target is cheap: 3 laws in 113 lines and 7 build rounds, each law 4-13 lines after a
  `decide` decode lemma, no configuration pins, generic in registers, 7 s to check. The remaining six laws are the same
  pattern: `li` (movz + 3 movk or the `genConst` chain; one induction), `bin` x 10 more ops (two need `cmp` + `cset`,
  i.e. the flag identities already proved inside `agree`), `sel` (2 words), `bz` / `jmp` (one word each, offset
  arithmetic), `lbu` / `sb` (need the interface changes 1-3 above). Estimate: 1-2 working days for a full `Machine`
  instance including the interface adjustment; after that expressions, loops, arrays and sort follow from the existing
  middle layer with no further target work, exactly as for RISC-V.
- On Sail full steps the same instance needs, per law, the full `stepModel` path under `ArmFull` (proved for the 216
  expression words only), new decode+execute lemmas for `cbz`, `b`, `ldrb`, `strb`, `movk`, the memory path through
  address translation (Device memory, alignment), and words enumerated rather than generic. That is the larger effort by
  a wide margin; I cannot put a number on it from this box.
- What their target does NOT give: it is a hand-written user-mode semantics (their own lockstep tests against Unicorn and
  the Sail model are tests, not proofs). A result on it is relative to it. `agree_emitted` + `full_word` would make the
  expression subset a proved consequence of the Sail result; for memory and branches that bridge does not exist yet.
- Suggested order: (1) decide the interface change for W^X / `instrAt_frame`; (2) finish the 9 laws on their semantics;
  (3) keep Sail as reference by extending the bridge theorem form of section 4 class by class.
