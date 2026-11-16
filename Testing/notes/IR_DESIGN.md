# One shared IR: design (draft, 2026-11-16)

Status: design only. No compiler source is changed by this note. `Spec/` is the owner's and stays as it is.
The standing decisions in `ROADMAP.md` hold: one pure `compile`, a proof per back end, no `sorry`/axioms/`native_decide`.
Names below are `file:line` on `main` at 7c460cf.

## 1. Today: IRs, routes, theorems

### 1.1 Languages

| level | IR | file | semantics | state |
|---|---|---|---|---|
| source | `Exp` (`Fin 4` vars) | `Spec/Code.lean:27` | `denote` | `Fin 4 → BitVec 64` |
| source | `AExp`/`AStmt` (`Fin 8`) | `Spec/ArrCode.lean:13,60` | `AExec` big-step | env + byte `Heap` |
| middle | `Mach.Stmt` (copy of `Proven.Stmt`) | `Compiler/Stmt.lean:16` | `Exec` | env |
| middle | `Mach.BExp`/`Mach.BStmt` (copy of `Proven.BStmt` + words + `mop`) | `Compiler/BLang.lean:15,52` | `BExec` big-step; out of bounds = no derivation | `env`, `heap`, `wheap` (lists) |
| middle | `CStmt`/`Fn`/`Prog` (calls) | `Compiler/CLang.lean:24` | `CExec P k` (stack budget `k`) | BState + frames |
| middle | `TExecB`/`TExec` (traced, growing heap) | `Compiler/MemRun.lean:165,186` | `CExec` + `MemEvent` list | as above |
| optimiser | `IR.Code ρ` (structured: `seq/when/loop/loop2`) | `Compiler/Opt/IR.lean:45` | big-step `Exec ram fp` | regs + byte map `Mem` |
| front | Ind `E rk k`/`Pg` (cells `C`) | `Compiler/Ind.lean:146,174` | `ev`, `Pg.sem`, `Pg.al` | Lean values |
| front | Wa `E/A/F/T/Pg` (typed, de Bruijn) | `Riscv/Frontx/WaLang.lean:165-224` | `den`, `Runs` | Lean values |
| front | list `Tree` over `Proven.BExp` | `Riscv/Frontx/Tree.lean` | `Tree.comp_ok` | `Proven.BStmt` |
| front | `Pipe`/`XPipe` | `Compiler/Front/Pipe*.lean` | `prog_exec`, `progI_exec` | `AStmt`/`BStmt` |

### 1.2 Machine interfaces (one law per abstract op, instantiated per target)

`Machine` (`Compiler/Iface.lean:153`, `AOp`, register-restricted laws) ⊂ `MachineF` (`Frame.lean:44`, slots, `ld/sd`)
⊂ `MachineC` (`Call.lean:32`, `call/enterC/leaveC/stA`) ⊂ `MachineM` (`MemCode.lean:39`, `bltu`, OOM exit).
Parallel: `Wide` (`Compiler/Wide.lean:73`, `WOp`, any registers, `br Cond`) ⊂ `WideF` (`Opt/BFn.lean:14`). No `WideC`/`WideM`.
RISC-V: `rv`, `rvF`, `rvC`, `rvM`, `rvw`, `rvwF`. ARM (`Arm/apc`, DeepMind `Arm64.Step`): `apc`, `apcF`, `apcC`, `apcw`,
`apcwF`; Sail-ARM bridge only for gcd and sort (`Arm/apc/BridgeRun.lean`); no `MachineM` on ARM.

### 1.3 Routes to words

| front end | → middle | → back end | top theorem |
|---|---|---|---|
| `XPipe` (`compile%`) | `progI : BStmt` (`PipeI.lean:304`) | `compileBFO` (OptB) | `Proven.Top.compile_correct` (`Riscv/Back/Top.lean:227`) |
| list `frontx_compile` | `Tree` → `Proven.BStmt` → `toMS` → `Mach.BStmt` | `compBFO` / `compBFC` | `implements1_listW/_resW/_resC` (`Impl1.lean`, `Checked.lean`) |
| Wa `wa_compile` | `Pg.comp` → `Mach.BStmt` (`WaPg.lean:430`) | `compBFO` / `compBFC` | `implements1_wa/_waA/_waC/_waAC` (`WaImpl.lean:88..339`) |
| Rec `frontx_rec` | `recFn : CStmt` (`Compiler/Rec.lean:44`) | plain `compP` | `implements1_rec` |
| Ind `frontx_ind` | `indProgM : Prog` (`Ind.lean:505`) | plain `compP` | `implements1_indM/S/L` (`Riscv/Frontx/Ind.lean`) |
| Ind with run-time memory | same `indProgM` | `compPM` (`MemCode.lean:1824`) | `IndMem.compile_runs`, `compile_correct` (`IndMem.lean:224,237`) |

Proof shapes: every source→middle and middle→machine step is a forward simulation of a big-step run into
`runsTo` (`execB_ok`, `execC_ok`, `execCM_ok`, `low_ok`); the optimiser is partial and mixes proved passes
(`flow_ok`, `sr_ok`, `hoist_ok`, `peep_ok`, `irB_ok`) with translation validation of the register choice
(`injOn`, `Live.chk_ok`; `Color`, `pickB`, `pickC` untrusted).

### 1.4 Duplicated work (what one IR removes)

1. Five expression languages of one shape (`Exp`, `AExp`, `Proven.BExp`, `Mach.BExp`, `Sel.SExp`) and two statement
   copies (`Proven.BStmt`/`Mach.BStmt`, `Proven.Stmt`/`Mach.Stmt`) with converters `toM`, `toMB`, `toMS`.
2. Six expression/statement code generators: `mgen8`, `mgenB`, `Sel`/`BSel`, Wa `E.comp`, Ind `comp`, Tree `comp`,
   plus `Arm/CompilerArm.lean`.
3. `compBM`/`compCM`/`compPM` re-implement `compB`/`compC`/`compP` control flow to insert checks.
4. Two interface hierarchies (`Machine…MachineM` vs `Wide…WideF`): calls and memory checks are only on the plain one,
   so Ind and Rec code is unoptimised (700–2000 words, every local in a slot; `NOTES.md` §17, §24).
5. Five space bounds: `space`/`spaceA`/`cellsSup` (Ind), `8·wholeW + 8(N+1) + 7` (Wa), `need + 24/32` (Rec, calls),
   `memoryNeeded` (only Ind). Five layout relations (`RelB`, `HeapB`, `RelBI`, `RelA`, `Lay`/`Frm`) say the same thing.
6. Four `if` encodings (two at-most-once loops in `Tree`/`WaStmt`, `CStmt.ite`, `IR.when`, `Exp.ite`).
7. Branch reach handled ad hoc: `bzOK n := 2n < 2048` makes `compile` return `none` for 4 of 29 Ind entries (§24);
   `tinyCompile` needed `compBFC` because the plain fallback overflowed `beqz`.

## 2. Proposal: `Proven.Ir`, one IR at three levels

Model: CompCert's RTL → LTL → Linear/Mach (each with a semantics, a simulation per pass, validation for register
allocation), with the shape of LLVM/Cranelift functions (basic blocks, block parameters instead of phi, 64-bit
values, explicit `alloc/load/store/call`). One datatype parametrised by the location type `ρ`, as `IR.Code ρ` today:

| level | `ρ` | memory | made by |
|---|---|---|---|
| **RTL** | `VReg := Nat` | abstract blocks, no addresses | front ends |
| **LTL** | `Loc := reg Reg | slot Nat` | abstract blocks + frame slots | register allocation (validated) |
| **Lin** | `Loc`, blocks in a list with fall-through | same | linearisation, branch relaxation |
| words | `WOp` (`Wide` + extensions) → `List (BitVec 32)` | concrete addresses | placement + emission, per target laws |

### 2.1 Syntax (`Compiler/Ir/Syntax.lean`)

```lean
namespace Proven.Ir
abbrev Lbl := Nat
abbrev FId := Nat
inductive Val | w (x : BitVec 64) | p (blk : Nat) (off : Nat)    -- a pointer is (block, cell offset)
inductive Arg (ρ) | r (x : ρ) | i (c : BitVec 64)
inductive Rhs (ρ) | arg (a : Arg ρ) | op (o : Op) (a b : Arg ρ) | mop (m : MOp) (a b : Arg ρ)
  | padd (p : ρ) (i : Arg ρ)                                       -- pointer + cells
inductive Inst (ρ)
  | let_ (d : ρ) (e : Rhs ρ)
  | ldb (d : ρ) (p : ρ) (i : Arg ρ) | stb (v : Arg ρ) (p : ρ) (i : Arg ρ)   -- byte blocks (input, output)
  | ld (d : ρ) (p : ρ) | st (v : Arg ρ) (p : ρ)                            -- one 64-bit cell
  | alloc (d : ρ) (cells : Arg ρ) | free (p : ρ)                           -- zeroed fresh block
  | call (ds : List ρ) (f : FId) (args : List (Arg ρ))
inductive Term (ρ)
  | jmp (l : Lbl) (as : List (Arg ρ))
  | br (t : Tst ρ) (l₁ : Lbl) (a₁ : List (Arg ρ)) (l₂ : Lbl) (a₂ : List (Arg ρ))  -- Tst = Cond × Arg × Arg
  | switch (x : ρ) (ls : List Lbl) (dflt : Lbl)                                 -- tag dispatch
  | ret (vs : List (Arg ρ))
structure Block (ρ) where params : List ρ; body : List (Inst ρ); term : Term ρ
structure Func (ρ) where params : List ρ; entry : Lbl; blocks : List (Lbl × Block ρ); slots : Nat := 0
structure Prog (ρ) where funcs : List (Func ρ); main : FId
```

Decisions:
- Values are 64-bit words or pointers (CompCert's `Vint`/`Vptr`, without `Vundef`: registers start at `.w 0`).
  `op` on a pointer, a load through a word, an index outside the block: **stuck** (no step). Lean's `x / 0 = 0`
  stays in the front ends (select after `divu`, as `mopS`); `MOp` keeps the hardware meaning.
- Only integer types, all 64-bit in registers; byte width only at `ldb/stb`. `UInt8/16/32` masking is the front end's.
- Block parameters replace phi; there is no SSA requirement (a `VReg` may be assigned twice), so front ends need no
  SSA construction; passes that want SSA facts get them from a checked analysis (2.4).
- `switch` exists so that Ind tag dispatch and `match` are one terminator; its lowering chooses a branch tree or a
  jump table (2.4).

### 2.2 Memory model, tied to `AllocSpec` / `memoryNeeded`

```lean
inductive BlkKind | input | output | cells
structure Blk where kind : BlkKind; bytes : List UInt8 := []; cells : List Val := []; live : Bool := true
structure Mem where blks : List Blk           -- block 0 input, 1 output, then allocations in order
def Mem.alloc (m : Mem) (n : Nat) : Mem × Val := (⟨m.blks ++ [⟨.cells, [], List.replicate n (.w 0), true⟩]⟩, .p m.blks.length 0)
```
- Address-free and unbounded: `alloc` always succeeds at RTL/LTL/Lin and appends `MemEvent.alloc n`; `free` appends
  `MemEvent.free n` and marks the block dead (later access stuck). A call appends `alloc (slots f + 1)` and its
  return `free (slots f + 1)` (owner default (3)); frame sizes exist from LTL on, so the events of `CompiledA` are
  the events of the **Lin run**, which is still address-free. Then
  `memoryNeeded compiled input = 8 * peak (events of the Lin run)` literally, `AllocSpec.lean:51`, unchanged.
- Placement (one theorem, once, per interface not per target): `place_ok`: a Lin run plus an injective layout
  `L : blk → address` satisfying `AllocSpec 8 work inUse` at every `alloc` gives the machine run with
  `base(.p b o) = L b + 8 o`. This is CompCert's memory injection collapsed to one step, and it replaces
  `RelB`/`HeapB`/`RelBI`/`RelA`/`Lay`.
- The emitted allocator implements the spec: frames from the top of the work block (stack), cells from the bottom
  (bump), **plus a free list for one-cell-size blocks**; out of memory = the two ends meet → `oomFlag` exit. With
  fixed-size cells (owner default (1)), heap never freed (default (2)) or freed one cell size at a time, the code
  fails exactly when `peak > W`, which is `CompileRuns`'s iff. Variable-size blocks that are freed in non-LIFO order
  break exactness (fragmentation); the compiler rejects them (`compile = none`) until the owner fixes a rule.
- Bounds checks: a source-level guarded access (`a[i]!`, `getElem?`) is an explicit `br (i <u size)` in RTL, so the
  front end's proof covers it; an unguarded access (`a[i]'h`, Wa `chk = false`, Ind field reads) is a plain `ld`
  whose in-bounds fact the **front end** owes from source facts (the `h`, `E.ok`, `Rp`). The machine code then
  needs no check on loads/stores at all: `place_ok` turns "in bounds of an abstract block" into "inside the work
  block, apart from the other live blocks". Run-time cost of memory safety: one compare per `alloc` and per call,
  instead of per heap access (today +15..87 %, §24).
- Range-check elimination is ordinary branch folding with checked range facts (2.4), so `a[i]!` inside a loop with
  `i < a.size` from the loop test loses its check without a front-end change.

### 2.3 Semantics (`Compiler/Ir/Sem.lean`)

```lean
structure Frame (ρ) where f : FId; l : Lbl; pc : Nat; regs : ρ → Val; dst : List ρ
structure State (ρ) where stack : List (Frame ρ); mem : Mem; ev : List MemEvent
inductive Out (ρ) | next (s : State ρ) | done (vs : List Val) (m : Mem) (ev : List MemEvent) | stuck
def step (P : Prog ρ) : State ρ → Out ρ                  -- executable, deterministic
def run (P : Prog ρ) : Nat → State ρ → Option (List Val × Mem × List MemEvent)   -- fuel; structural
def Runs (P : Prog ρ) (s : State ρ) (r) : Prop := ∃ n, run P n s = some r
theorem run_det : run P n s = some r → run P n' s = some r' → r = r'
```
- Small-step, as CompCert, because calls, tail calls (a `jmp` to the entry with new parameters) and the CFG need a
  program counter; `step` is a function, so `#eval` runs RTL/LTL/Lin programs directly (tests, `memoryNeeded` per
  case: replaces the interpreter in `Testing/asm/emit_mem.lean`) and `run_det` replaces `texec_det`.
- `Computes`-side: only terminating runs are claimed, as today (`Computes` gives termination; fuel is existential).

### 2.4 Passes and their proofs

Common statement (`Compiler/Ir/Sim.lean`): `Sim P Q` = forward simulation with a measure (one source step ↦ zero
or more target steps, the measure decreases on zero), initial and final states related, `ev` equal (or for
regalloc: target `ev` = source `ev` with frame events added). `sim_runs : Sim P Q → Runs P s r → ∃ r', Runs Q s' r'
∧ out r = out r' ∧ ev r' = …`. Both sides deterministic, so forward simulation is enough (CompCert's argument).
Two proof patterns only:
- **(P) proved transformation**: `pass_ok : Sim P (pass P)`.
- **(V) validated**: untrusted `pass` (any algorithm, `#eval`-fast, may use `HashMap`/WF recursion), proved checker
  `check : Prog → Prog → Bool`, `check_ok : check P Q = true → Sim P Q`; `compile` returns `none` when the check
  fails. Analyses are (V) too: untrusted fixpoint, proved check that the facts are a post-fixpoint (as `Live.chk`).

| # | pass | level | pattern | proof obligation | from today | est. (agent-days) |
|---|---|---|---|---|---|---|
| 1 | inlining (size/leaf heuristic untrusted) | RTL | P | frames merged: callee regs renamed into fresh caller regs, `ev` loses the callee's frame pair (allowed: `peak` only decreases; state `memoryNeeded` on the final program, so nothing to show) | `Sub.lean` renaming | 4 |
| 2 | const fold + copy prop + branch folding | RTL | V-facts + P-rewrite | facts `regs x = c` / `lo ≤ x < hi` checked per block entry; rewrite correct under facts | `SR.cp`, `Sel.simpS` | 4 |
| 3 | range-check elimination | RTL | same as 2 (interval domain) | `br` with a fact-decided test → `jmp` | – | 2 |
| 4 | CSE / value numbering (per block, then along dominators) | RTL | V-facts (available `x = e`) + P | loads only between stores to other blocks (abstract blocks make aliasing trivial: different block ids never alias) | – | 4 |
| 5 | DCE | RTL | V (liveness) + P | `Live.chk`, `SR.dce` generalised to CFG + block params | `Live`, `SR.dce` | 2 |
| 6 | LICM (needs a preheader block) | RTL | P under facts | hoist only `let_` (total ops; `divu/remu` are total) and `ld` with an in-bounds fact | `Hoist.lean` | 3 |
| 7 | strength reduction of indices | RTL | P | `padd` chains | `SR.lean` | 3 |
| 8 | register allocation + spilling (linear scan or `Color`, coalescing) | RTL→LTL | **V** (Rideau–Leroy dataflow validator: per program point an equation set `vreg = loc`, moves at edges for block params) | `regalloc_check_ok` | `Live.chk`, `Color`, `pickB` | 8 |
| 9 | callee-saved registers, frame layout | LTL | P | save/restore in prologue/epilogue; needs `Reg` beyond `Fin 15` (2.5) | – | 4 |
| 10 | linearise (block order untrusted), fall-through, `loop2`-style rotation | LTL→Lin | P | trivial CFG simulation | `Flow.rot`, `Flow.fuse` | 2 |
| 11 | long branches | Lin | P + decided reach | each `br` emitted short when `brOK d`, else `br ¬c +2; jmp far`; distances from an untrusted fixpoint, then **re-decided** at emission (`Wide.brOK`) | fixes §24 gap | 2 |
| 12 | `switch` lowering: branch tree, or jump table | Lin | P | jump table needs one new law (`w_jtab`: `jalr` through a table in code) per target; tree needs none | Ind `disp` | 2 + 1/target |
| 13 | scheduling within a block | Lin | **V** (symbolic execution of both blocks, Tristan–Leroy) | `sched_check_ok` | – | 4 |
| 14 | peephole | words list | P | per pattern, from the laws | `Peep.lean` | 1 |
| 15 | emission + placement | Lin→`WOp`→words | P, **per target only the laws** | `emit_ok` from the interface laws; `place_ok`; allocator code with OOM exit | `Lower.low_ok`, `MemCode` | 8 |

Order inside `compile`: 1 → (2,3,4,5 iterated a fixed number of times) → 6 → 7 → 5 → 8 → 9 → 10 → 11/12 → 13 → 15 → 14.
Every pass may be the identity at first; the pipeline is correct from day one with passes 8 (trivial validated
allocation: every vreg in a slot), 10, 11, 15 only.

### 2.5 The target interface

One structure `Target extends WideF` with the missing ops added as laws on ANY registers:
`call d`/`ret` (link register, callee-saved set as a field: `keep` becomes "callee-saved registers equal", so `s1..s11`
can be used after a save), `exitOOM` (`a0 := oomFlag; ret` via the stub cell, as `MemRv` today), `bltu`/`bgeu` already in
`Cond`, optional `jtab`. RISC-V instance: assembled from `rvwF`, `rvC`, `rvM` step lemmas (no new Sail work except
`jalr` for tables). ARM: `apcwF` already exists; add `call`/`exitOOM` from `apcC`. `Reg` becomes a field
(`Reg : Type`, `DecidableEq`, finite) instead of `Fin 15`, so callee-saved and the ARM's 31 registers are usable.
`emit_ok` is proved once against `Target`; a new target is the laws only (standing decision: proofs per back end).

## 3. Front ends: lowering and what each owes

Every front end produces `Ir.Prog VReg` plus a representation relation, and owes exactly one theorem:
`fe_ok : Computes-style source fact → Runs (lower src) (init input) r ∧ output r = enc (f a)` (RTL level), with all
plain loads in bounds (that is part of `Runs`: a stuck run has no result). Everything below RTL is generic.

| front end | lowering | owed proof | gets for free |
|---|---|---|---|
| **Ind** (`E`, `Pg`, `indProgM`) | cell = `alloc 4` (`[tag,x,l,r]`, `z` = a shared `.p 0 0` block made by `main`), `fw/ft` = `ld (padd p k)`, `mk` = `alloc` + 4 `st`, arm dispatch = `switch tag`, tail call = `jmp entry args`, real call = `call`, `bind` = `let_`; `dec`/`enc` are RTL library functions proved once (`dec_ok`/`enc_ok` restated) | `ind_rtl_ok` by the same induction as `loop_ok`/`chain_ok` (`IndOk.lean:664,887`) with `Rp` over pointers instead of word indices (simpler: no address arithmetic, no `Agree` on indices, children-below-parents not needed for safety) | optimised code with calls; per-alloc OOM check; `memoryNeeded` from its own events; branch reach (no `WfMem` failures) |
| **Wa** (`Pg`) | array = block (`alloc cap` at `F.rep/const/empty`; input bytes = block 0), `getA chk=false` = `ld`, `chk=true` = `br` + `ld`, `set!` = `br` + `st`, loops = blocks with parameters (state variables as block params: no copies of call temporaries), `push` = capacity check + `alloc 2cap` + copy loop | `wa_rtl_ok` from `T.comp_ok`/`Pg.comp_ok` structure; in-bounds from `E.ok` | `push`/`extract` (alloc is now dynamic), no static `wholeW`, table stores can become a constant block later |
| **list** (`Tree`, `Translate`) | `Tree` node = block, leaf call = `jmp` with params, `sub` = `call` or inlined | `tree_rtl_ok` from `Tree.comp_ok` | fast loops without `Fast.lean` (passes 2,6,7) |
| **Rec** | `recFn` pieces = RTL functions, `call` | from `rec_ok` | optimised calls |
| **Pipe/XPipe** | keep `progI : BStmt` and go through the bridge below | none | – |
| **bridge** | `ofCStmt : Mach.Prog → Ir.Prog` (heap blocks ↦ blocks, `loop` ↦ cycle, `load64` ↦ `ld (padd)`) | `ofCStmt_ok : CExec … → Runs …` once (~1 file) | every existing front end gets the new back end without its own proof |

The bridge `ofCStmt` is what makes the migration cheap: it is one proof, after which each front end can be switched
to the new back end by a name change, and rewritten to lower directly only when the direct lowering buys something
(Ind: dynamic allocation and pointers; Wa: dynamic arrays). For Ind the bridge alone does not suffice for
`memoryNeeded`: `TExec`'s heap grows on access, which has no `alloc` event; so Ind lowers directly (stage 2).

## 4. Migration (main never breaks)

Rules: new files only under `Compiler/Ir/`, `Riscv/Back/Ir*.lean`, `Riscv/Frontx/*Ir.lean`; the old route stays
built and tested until a front end is switched; a switch is one commit that changes which `code`/theorem an entry
uses, after the full `check.sh` plus the front end's QEMU+Sail tests pass on BOTH routes (words may differ, outputs
must not). Statement fingerprints of `Spec/` theorems must not change. Old routes are deleted only at the end.

| stage | content | done when | est. |
|---|---|---|---|
| S0 | `Ir/Syntax`, `Ir/Sem` (`step`, `run`, `run_det`), `Ir/Sim` (`Sim`, `sim_runs`, composition), `#eval` interpreter tests | small hand-written programs run; `run_det` proved | 3 |
| S1 | minimal back end: trivial allocation (all slots) as a validated pass, linearise, long branches, `Target` (RISC-V instance from existing lemmas), `emit_ok`, `place_ok`, allocator with OOM exit; `Ir.compile : Ir.Prog VReg → Option CompiledA`, `ir_compile_runs`, `ir_compile_correct` (shapes of `AllocSpec.CompileRuns/Correct`) | a hand-written RTL list `reverse` passes QEMU+Sail at `memoryNeeded` and `memoryNeeded - 1` | 10 |
| S2 | **Ind first**: direct `E → RTL`, `dec`/`enc` library, `ind_rtl_ok`; `IndMem.compile` gets a twin `IndIr.compile` with the same two theorems | all 29 Ind entries (incl. the 4 that fail `WfMem` today) pass `mem_test.py check 50`; then switch `frontx_ind` | 8 |
| S3 | bridge `ofCStmt` + `ofCStmt_ok`; switch Rec, list, Wa, Pipe one at a time behind it | each front end's test suite passes on the new words; `Top.compile` moved last | 5 |
| S4 | passes 8 (real allocator + validator), 2/3/5, 6, 7, 4, 1, 9, 13, 12 in that order (by expected speed gain per day: `NOTES.md` §15/§17 show slot traffic and call overhead dominate) | bench rows of `OPT.md` no worse than `compBFO` before deleting it | 30–40 |
| S5 | ARM `Target` instance from `apcwF`/`apcC`; Sail-ARM bridge for `call`/`ld`/`st` | Ind and Wa entries run on AArch64 QEMU and Sail ARM | 6 |
| S6 | direct Wa lowering (dynamic arrays, `push`), delete `MemCode`, `compBM/CM/PM`, `Machine…MachineM`, `Proven.BStmt` copies, plain back ends | `check.sh` green with old files removed | 5 |

Critical path S0 → S1 → S2: about 3–4 weeks of one agent; S3 and S5 can run in parallel with S2 once S1's
interfaces are frozen; S4 passes are independent of each other (one agent per pass).

## 5. Risks, and how the design keeps waiting low

**Proof size.** CompCert's back end is ~50k lines of Coq; we take a subset (no floats, no 32-bit, no volatile, no
`Vundef`, one value type, abstract blocks without permissions) and validate the hard algorithms instead of proving
them. Estimate: 12–18k lines for S0–S4. Mitigation: two proof patterns only (P, V); checkers are small Boolean
functions whose `_ok` proofs do not grow with the algorithm.

**Kernel evaluation cost.** The general theorems quantify over the program (`compile p = some c → …`), so the
kernel evaluates nothing for them. Evaluation happens only for concrete entries (`decide +kernel` that
`compile p = some c`, ~30 s for `optB` today; `boot_revinc5` cannot evaluate `List.mergeSort`). Rules: (1) everything
inside `compile` is structural recursion or fuel (no WF recursion, no `HashMap`, no `Array.qsort`), checked by a CI
file that `decide +kernel`s `compile` on 3 small programs; (2) untrusted searches run at elaboration (`#eval`/meta)
and pass their result as a HINT argument (`compile hints p`), so the kernel only runs the checker (linear in the
program), never the search; (3) checkers use sorted association lists keyed by `Nat`, binary `Nat` arithmetic;
(4) per-function checking, so a con-leche-sized program is a sum of small checks; (5) concrete entries live in leaf
files that nothing imports.

**Build time.** (1) The stable interface files (`Ir/Syntax`, `Ir/Sem`, `Ir/Sim`, `Target`) are frozen early (S0/S1)
and small; each pass is one file importing only them, with its theorem stated against `Sim`, so editing a pass
rebuilds that file and `Ir/Compile.lean` only. (2) Proof files split by lemma group so lake builds them in parallel
(as `BUILD_PROFILE.md` plans); no file over ~800 lines. (3) No `simp` over concrete programs inside general proofs.
(4) Front-end commands generate `fe_ok` instances by term-mode application of one generic lemma (as `implements1_wa`
does), not by re-running tactics over the program. (5) Old and new routes build side by side only for the front end
being switched; the rest of the tree does not import `Ir`.

**Test waiting.** The `step` function makes RTL, LTL and Lin runnable in `#eval`: differential tests (Lean function
vs RTL run vs Lin run, and `memoryNeeded` per case) run in seconds on the agent's own box; QEMU/Sail runs only at the
end of a round and go to other boxes (ROADMAP "Pipelining"). Each pass gets a fuzz harness on random RTL programs
(generator + `run` before/after), which finds wrong passes before any proof is written.

**Other risks.**
- Exactness of out of memory with `free` of variable-size blocks (2.2): rejected until the owner decides.
- `Reg` as a field touches every `Wide` law statement (S1); doing it once in `Target` and leaving `Wide` alone avoids
  re-proving the old route.
- Pointer values make `Ind` hashing by address impossible (no `ptr → word`); nothing needs it today (`mixHash` is on
  values).
- Validated passes can fail on real programs (`compile = none`): every failure is visible (`none`), tests count it,
  and S1's trivial allocator is always a valid fallback candidate inside `compile` (the first hint that checks wins).
