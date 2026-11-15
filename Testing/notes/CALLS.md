# Function calls, a stack, recursion

Status: kernel-checked, no `sorry` / `axiom` / `native_decide` / `bv_decide`. Middle-layer theorems depend on
`propext`, `Classical.choice`, `Quot.sound` only.

| file | what |
|---|---|
| `Compiler/CLang.lean` | source language `CStmt` / `Fn` / `Prog`, semantics `CExec` (index = stack need) |
| `Compiler/Call.lean` | interface extension `MachineC` (4 operations, 4 laws), `keepC` |
| `Compiler/CStmt.lean` | compiler `compC` / `fnC`, `execC_ok` (induction on the source run) |
| `Compiler/CProg.lean` | program layout (stub + function table), `compP_ok` |
| `Riscv/Back/Call.lean` | `rvC : MachineC` (laws from `Riscv/Steps/Gen*.lean`) |
| `Riscv/Back/Calls.lean` | `ImplementsW`, `Computes`, `WfProg`, `callsCode_implements`, tactic `wf_calls` |
| `Riscv/Examples/CallExamples.lean` | `sumTo_implements`, `fib_implements`, `isEven_implements` |
| `Spec/Tree.lean`, `Riscv/Examples/TreeEval.lean` | `Tree`, `Bytes Tree` (round trip), `treeEval_implements` |
| `Testing/asm/calls_test.py`, `emit_calls.lean`, `calls-words/` | QEMU + Sail emulator tests |

## Language (`CLang.lean`)

```lean
inductive CStmt | base (p : BStmt) | seq (p q) | ite (c : BExp) (p q) | loop (c : BExp) (body) | call (res f : Nat) (args : List BExp)
structure Fn where nparams nlocals : Nat; body : CStmt; ret : BExp
abbrev Prog := List Fn                 -- a function's name is its index
```

- `base p`: any call-free `BStmt` (assign, byte/word block load/store, loops), proved by `execB_ok` unchanged.
- Variables `0 .. 7` are GLOBALS: one copy for the whole program, shared by all functions (block base addresses
  live here and are never assigned). Variable `8 + j` is LOCAL `j` of the running function.
- `call res f args`: evaluate `args` in the caller; run `f`'s body with locals = arguments then zeros and the
  current globals/blocks; then `res := f.ret` evaluated in the callee's final state. The callee's globals and
  blocks flow back (`retEnv`). Recursion of any kind, including mutual, is allowed.
- `return e` is the field `ret` (one result expression after the body). There is no early return.
- `CExec P k p σ σ'`: fuel-free big-step relation; `k` is an upper bound on the stack bytes the run needs below
  the current frame. `base`: any `k`. `call`: `8 * (nlocals + 1) + k' ≤ k` where the body runs in `k'`.
  `CExec.mono`: a larger `k` is fine. `CRuns := ∃ k, CExec ..`.

## Calling convention (abstract; RISC-V in brackets)

| item | where |
|---|---|
| globals `0..7` | `avar 0..7` [`a0..a7`], shared, never saved |
| local `j` | slot `j` = 8 bytes at `fr + 8 (j + 1)` (`fr` [`gp`] = frame register) |
| saved return address | cell 0 of the frame (`fr`) |
| argument `j` | stored by the CALLER at `fr - 8 (n - j)` = slot `j` of the callee (`n` = callee's `nlocals`); the callee's other locals are stored as `0` the same way |
| result | `r0` [`t0`] |
| caller-saved | temporaries `r0..r6` [`t0..t6`] (dead across statements), link register [`ra`] |
| callee-saved | frame register, the caller's frame memory, everything in `keepC` (all non-abstract registers except `gp`, `ra`) |

Frame of a function with `n` locals: `8 (n + 1)` bytes; a callee's frame is directly below the caller's
(`[fr - 8 (n + 1), fr)`). Code of a call: `argsC` (per argument: expression into `r0`, `stA`), `call d`, `setV res`.
Code of a function: `enterC n`, body, `ret` expression into `r0`, `leaveC n`, `ret`.
Program: `stub ++ fn 0 ++ fn 1 ++ ..`; stub = `enter 0; enterC 0; res := main(); leaveC 0; leave; ret`.

## Interface (`MachineC extends MachineF`): what a target proves

| op | RISC-V | law (from `At s pc (encC o)`) |
|---|---|---|
| `call d` | `jal ra, 4d` | `callOK d` → pc `:= pc + 4d`, `ra := next pc lenCall`, `fr`, registers, memory same |
| `enterC n` | `addi gp,gp,-8(n+1); sd ra,0(gp)` | `n ≤ maxSlots`, new cell in RAM, `fr` 8-aligned → `fr := fr - 8(n+1)`, memory `:= wr (fr - 8(n+1)) (le8 ra)`, registers same |
| `leaveC n` | `ld ra,0(gp); addi gp,gp,8(n+1)` | frame in RAM, cell 0 holds `le8 w` → `ra := w`, `fr := fr + 8(n+1)`, registers, memory same |
| `stA m v` | `sd t0,-8m(gp)` | `v = r0`, `1 ≤ m ≤ maxSlots`, cell in RAM → memory `:= wr (fr - 8m) (le8 v)`, `Done` (full `keep`) |

Plus: `keepC` (`keepC_of_keepF`, `keepC_trans`, `keepF_of_keepC : keepC s s' → ra s' = ra s → keepF s s'`),
`len_call`, `retOK_al : v % 4 = 0 → retOK v`. `ret` is the existing `law_ret`.
RISC-V: `callOK d := -2^18 ≤ d < 2^18`, `maxSlots = 16`, `lenCall = 1`.

**ARM to-do**: `call d` = `bl #4d` (link `x30`), `enterC` = `sub fr,fr,#8(n+1); str x30,[fr]`, `leaveC` =
`ldr x30,[fr]; add fr,fr,#8(n+1)`, `stA m` = `stur x_r0,[fr,#-8m]`, with `fr` the register chosen for
`MachineF` (not `sp`: unaligned intermediate values are never produced, but the slot ops address `fr`).
`keepC` = `keepF` minus `x30`. Nothing else: the middle proofs are target-independent.

## Theorems

`MachineC.execC_ok` (`CStmt.lean`). Context `Ctx` = program words `W` at `cb` with function `f` at word
`off f`, byte blocks `R`, word blocks `Wr`, stack area `[lo, hi)`, all in RAM and pairwise disjoint, every
function well-formed. Then

```lean
CExec P k p σ σ' → wfC N pos p → Sub W pos (code of p) → Frm N fp → lo + k ≤ fp → fp + 8 (N + 1) ≤ hi →
codeAt s cb W → ok s → pcIs s (next cb pos) → RelB N fp bv wv R Wr σ s →
runsTo s fun s' => ok s' ∧ keepC s s' ∧ pcIs s' (next cb (pos + lenC p)) ∧
  Out (R ++ Wr ++ slots N fp ++ [⟨lo, fp - lo⟩]) (mem s) (mem s') ∧ RelB N fp bv wv R Wr σ' s'
```

Proof: induction on the `CExec` derivation. The `call` case runs the argument code, `call`, the callee's
`enterC`, the induction hypothesis for the callee's body in the frame `fp - 8 (n + 1)` with budget `k'`, the
result expression, `leaveC` (the saved return address is intact because the body writes only blocks, its
slots and the stack below its frame), `ret` to the word after the call, and `setV res`. The caller's slots
are intact for the same reason (`slot_low`).

`MachineC.compP_ok` (`CProg.lean`): for the whole program entered at word 0 with `CExec P k (.call res main [])`,
`enterOK s 0`, `lo + k + 8 ≤ frameAt s 0`, layout `PLay`: returns to `ra s` with the globals and blocks of `σ'`,
writes only `R ++ Wr ++ [⟨lo, frameAt s 0 + 8 - lo⟩]`, full `keep` (frame register and link register restored).

`callsCode_implements` (`Riscv/Back/Calls.lean`): `WfProg P main → Computes P main f pre need →
ImplementsW (callsCode P main) f pre (fun n => need n + 24)`.

## The stack bound (spec decision, for owner review)

1. General form: the hypothesis is `lo + k ≤ fp` where `k` is the index of the source run `CExec P k ..`,
   i.e. (frames along the deepest call chain) in bytes. Nothing else about the stack is assumed.
2. Single-bound form: `ImplementsW code f pre space` has one resource hypothesis, `space |x| ≤ stack.len`,
   on the block below `sp`. `space n = need n + 24` (16 bytes for the stub's two cells, up to 7 for aligning
   `sp`). `need` is discharged per program by induction on the input:
   - `sumTo`, `isEven`: `24 n` for argument `n` (`sum_spec`, `even_spec`), `n ≤ 255` (one input byte) → constant `space = 6184`.
   - `fib`: `32 n` → `space = 8232`.
   - tree evaluator: body need `32 * depth t` (`ev_spec`, structural induction on `t`), and
     `Tree.depth_le : depth t + 2 ≤ |enc t|`, so `space n = 32 n + 72`.
3. Proposed, NOT the same as `Spec/Implements1.lean` (which landed on `main` meanwhile). Differences of `ImplementsW`:
   the stack block is the region named `stack` (top in `sp`; `a2`/scratch unused) rather than `work`; the output
   must be 8 bytes, 8-ALIGNED and present (the result is written by one `store64`); a precondition `pre` on the
   raw input bytes instead of a typed argument; conclusion `calleeSavedKept` and `unchangedOutside [input, scratch, output, stack]`.
   Restating the clients as `Implements1` needs a byte-wise result store (or an alignment hypothesis) and
   `Mapped work`-free stack writes (already true: every frame cell is written before it is read).

## Clients (each: Lean reference → `Computes` → `ImplementsW`)

| theorem | reference | input | space |
|---|---|---|---|
| `sumTo_implements` | `sumTo : Nat → BitVec 64` (`n + sumTo (n-1)`) | 1 byte `n` | 6184 |
| `fib_implements` | `fibW` (two non-tail calls) | 1 byte | 8232 |
| `isEven_implements` | mutual `isEven` / `isOdd` | 1 byte | 6184 |
| `treeEval_implements` | `treeF = Tree.eval ∘ decAll` | `enc t` (prefix bytes) | `32 n + 72` |

Tree format (`Spec/Tree.lean`): leaf = `0, v` (value byte, zero-extended); node = tag (`1` add, `2` sub, `3` xor),
left, right. `Bytes Tree` with `dec_enc` proved. `ev()` keeps the read cursor in global 5.

Well-formedness of a concrete program (`WfProg`: expression depths, variable ranges, branch and call distances)
is proved by `wf_calls [defs]` (`simp` evaluation; `genConst` lengths through `gcLen`, since `genConst` is
defined by well-founded recursion and does not reduce in the kernel).

## Tests (`python3 Testing/asm/calls_test.py [sumto|fib|even|tree]`)

QEMU and Sail C emulator, per case: output word = reference, input and guard bytes unchanged, `gp`/`sp`
restored, every Sail data write inside the output word or the case's stack block.

| program | cases | stack block | deepest use |
|---|---|---|---|
| sumto | 256 (all inputs) | 6184 (= `space`) | 6178 |
| fib | 25 (`n ≤ 24`) | 8232 (= `space`) | 807 |
| even | 256 | 6184 | 6178 |
| tree | 292 (random, left/right/zigzag chains to depth 700) | `32 n + 72` | 22471 of 67336 |
| tree, block = `32 depth + 71` (hypothesis of `compP_ok`) | 292 | tight | 22470 of 22471 |

## Limits

- At most 16 locals per function (`maxSlots`); arguments are padded to all locals at each call site (code size
  per call grows with the callee's `nlocals`; a callee-side zeroing prologue would be smaller).
- Arguments go through memory, not registers; one result word; no early return; no function pointers.
- Calls are statements (`res := f(args)`), not expressions; argument expressions use the 7 temporaries.
- `ite` skips the else-branch with `li r0, 0; bz r0` (no forward unconditional jump in the interface).
- Globals are shared mutable state: a function's effect on them must be stated in its source-level spec
  (`Spec1` covers the pure case; the tree evaluator's cursor is handled by hand in `ev_spec`).
- Not yet re-based on the optimising back end (`Compiler/Opt`). Used by the frontx front end for non-tail
  recursion (`frontx_rec`, `Testing/notes/frontx/NOTES.md` section 15), with an `Implements1` bridge
  (`Riscv/Back/CallsImpl1.lean`, `implements1_of_cexec`).
- `calls_test.py` fib inputs stop at 24 (running time), so its stack use stays far below the bound.
