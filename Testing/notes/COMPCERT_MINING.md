# What to take from CompCert (ideas only)

Status: reading/design note, 2026-11-16. No compiler change. Read: CompCert master (Coq, `/tmp/compcert`) and Certora/clean
`feat/c-to-lean` (`export/CCLib/*.lean`). Line counts are `wc -l` of the `.v` files. Our side: `Compiler/Ir/*`, `Riscv/Back/Ir*.lean`,
`Testing/notes/IR_DESIGN.md` (branch `ir-design`), `frontx/NOTES.md` §24-§29 (run-time memory, Expr, Int, HOF, monads, strings), ROADMAP.

## 0. Ground rules

- **Licence.** CompCert: INRIA Non-Commercial (some files LGPL 2.1+). clean is a CompCert fork under the same terms. We take designs
  and proof strategies and write our own Lean. No transliterated Coq proofs, lemma statements or file structure (clean does exactly
  that, so it is itself non-commercial). A file that ever copies says so (NOTICE.md).
- **Trust.** Only the Sail models. CompCert's theorems and models are not trusted; no `Mem.inject` import, no Coq link.
- **Why most CompCert cost does not apply to us:**
  1. one value type (`Val.w | Val.p blk off`), no floats, no 32-bit, no `Vundef`, no volatile, no permissions;
  2. memory is address-free (`Mem` in `Sem.lean`); one placement step, not an injection per pass;
  3. basic blocks with block parameters, not node-per-instruction + phi-free registers;
  4. only terminating runs are claimed (`Runs`, `Refines`; stuck = no run), no divergence/traces;
  5. targets are Sail words reached through `Target` laws, no trusted assembler/expander;
  6. the spec has an exact cost, `memoryNeeded` = peak of the event list (`AllocSpec`); CompCert has no cost theorem.

## 1. Ranked recommendations

| # | recommendation | gain | effort (CompCert → us, estimate) | source |
|---|---|---|---|---|
| 1 | Validate, never verify, heavy algorithms: untrusted function (any algorithm, run at elaboration, passed as a hint) + small proved Bool checker | all speed work | CompCert: allocator 1218 lines untrusted OCaml vs 3.9k checker+proof | Allocation.v, Linearize.v |
| 2 | Register allocation by an equation-set validator (backward dataflow of `vreg = loc`; edge moves for block params untrusted, checked) | largest speedup: slots→registers (§15/§17 of frontx notes: slot traffic dominates) | 3.9k Coq → est. 1.5-2.5k Lean | Allocation.v, Allocproof.v |
| 3 | One generic "facts" checker (per-block-entry abstract values form a post-fixpoint) shared by const/copy prop, branch folding, range-check elimination, DCE guards | speed + removes bounds checks | CompCert: Kildall 1645 + ValueAnalysis 2028 + ValueDomain 5347 + passes; we skip the solver proof and use a small domain: est. 0.5-1k | Kildall.v, ValueAnalysis.v, Constprop.v |
| 4 | Keep `Sim` fuel-based (no measure). Add `Sim.comp`, `Sim.refl`, `Sim.of_per_function`, and "checker ⇒ `Refines`" directly | proof effort | CompCert pays 100-250 lines of measure per pass (Tunneling, Linearize, Inlining, RTLgen) | Smallstep.v |
| 5 | Liveness-based slot sharing (validated) before real registers: smaller frames ⇒ smaller `memoryNeeded` | spec-visible memory, safe first step | tiny: reuses `Live.chk` | Allocation.v idea |
| 6 | Inlining at RTL = register/label renaming into the caller, heuristic untrusted, `ret` ↦ `jmp cont` | call overhead | Coq 2.45k (mostly stack-block merging via `Mem.inject`); ours has no memory part | Inlining*.v |
| 7 | Local value numbering (CSE) per block; loads killed by `st` using block id + cell index | array code | Coq 2.5k mostly alias reasoning; abstract blocks make it definitional | CSE*.v |
| 8 | Unreachable-function removal first in the pipeline | big programs (con-leche, lean-svg) | Coq 1.6k (global injection); ours ~200 (renumber `FId`) | Unusedglob*.v |
| 9 | Tunneling = forwarding-block removal; linearisation = untrusted block order + trivial CFG simulation; long branches decided at emission | size/speed small | Coq ~900 + ~950; ours ~200-400 | Tunneling.v, Linearize.v |
| 10 | Asmgen shape: per-op template + "runs from pc to pc+len" lemma; constants `li` / `lui+addiw` / chain | already how `Target`/`Wide` work | keep | Asmgen*.v |
| 11 | Memory: take the proof-obligation list of `inject` (load/store/alloc/free preserve the relation) for `Placed` and `Paged`, nothing else | paging proof shape | avoids 4665+1245 | Memory.v |
| 12 | Semantic Hoare/sep triples (defined over the step relation, soundness definitional, frame as a disjoint heap fragment) for the middle logic | Hoare logic cost | clean: Hoare 437 + SepHoare 1233 + SepLogic 647 | clean CCLib |

Skip: CminorSel/Selection level, Linking framework, RTLgen, RTLtyping, Stacking's separation-logic frames, bit-level neededness (Deadcode `nval`), CSE of partially redundant cheap ops.

Order (IR_DESIGN S4): 4 → 8 → 3 → 5 → 2 → 9 → 6 → 7.

## 2. Item by item

### 2.1 RTL.v (610), RTLgen (697 + spec 1355 + proof 1600), RTLtyping (1004)

1. CFG of single instructions keyed by `node` (`Inop/Iop/Iload/Istore/Icall/Itailcall/Icond/Ijumptable/Ireturn`), registers untyped but
   typed by inference. RTLgen translates CminorSel to RTL with a state monad of fresh nodes/registers, building code backwards (continuation node passed in).
2. RTLgenspec: a relational spec of the monadic generator (`tr_expr`, `tr_stmt`), proved sound for the monad; RTLgenproof: `star`+measure simulation (`lt_state`) because a source `Sskip`/`Sseq` step costs 0 target steps. ~3.6k.
3. Our `Func/Block` is RTL with blocks, parameters and `switch`. RTLgen itself is not needed: front ends build `Ir.Prog` directly and each owes one `fe_ok`.
4. Take: state a generator that uses fresh labels/registers (Wa loops, `push`, inlining) as a total function + an inductive "this code implements that" spec
   (`Tr`), so the proof does not follow the fresh-name bookkeeping. For straight-line Ind arms a structural induction is shorter.
5. Pitfalls: `Inop` ladders and per-node measures (blocks avoid both); typing exists for int/float/long classes (we have one class); `Vundef` rules on `Iop`
   spawn side conditions in every later pass (ours: pointer/word stuck rules, explicit).

### 2.2 Allocation.v (1374) + Allocproof.v (2545) + Regalloc.ml (1218, untrusted) + Locations (586), LTL (322), Conventions

1. `Regalloc.ml` (liveness, interference graph, iterated register coalescing, spilling, splitting) emits an LTL function (`Lop Omove`, `Lgetstack/Lsetstack`,
   `loc = R mreg | S slot`). Coq only runs `check_function`: `pair_codes` pairs each RTL node with the LTL block shape (`BSop`, `BSmove`, `BScall`...: "reload args, op, spill result");
   a **backward** dataflow (`DS` = `Backward_Dataflow_Solver(LEq)`) over sets of equations `Eq(kind, vreg, loc)` computes what must hold before each node (`transfer`,
   `transfer_use_def`); entry check: the parameter equations imply it. Equation kinds `Full/Low/High` exist only for 32-bit pairs.
2. `match_states` has `satisf rs ls e` (every equation holds), moves are shown to realise the parallel assignment, calls kill caller-saved registers (`Extended`).
   `forward_simulation_plus`. Half of the 2.5k is calls/builtins/pairs/register kinds.
3. Mapping: best fit of the whole list. (a) Block params: an edge `jmp l as` becomes a parallel move into `l`'s param locations; the checker verifies the equation set
   at `l`'s entry follows. No phi translation. (b) One register class, no kinds. (c) `Func.slots` is the spill area, `ρ := Loc` already.
   (d) A `call` kills the caller-saved set, a `Target` field (IR_DESIGN 2.5). Our current `Rename.alloc` (`injOn`, one slot per vreg) is the degenerate validator.
4. Recommend: step A slot sharing by liveness (validator = liveness is a post-fixpoint + `injOn` on simultaneously-live pairs); step B registers: equations as a sorted
   `List (Nat × Loc)` per block entry, `check_ok : check P Q = true → Sim P Q`; untrusted allocator = linear scan over block order (regalloc2/Cranelift is the model;
   IRC is overkill); step C coalescing of param moves is a choice of locations only, the checker already accepts it.
5. Pitfalls: (i) fix the shape of spill/reload code (CompCert fixes it, which makes the checker a case analysis, not a search); (ii) the allocator may not introduce reads of
   uninitialised locations (ours: registers start `.w 0`, so equality is exact, simpler than `lessdef`); (iii) frame bounds (`Bounds.v` 475) must be computed from the
   code: derive `slots = 1 + max slot` or check `all slot < slots`; (iv) no `PTree`/`HashMap`/WF recursion in the checker (kernel evaluation, IR_DESIGN §5).

### 2.3 Tunneling.v (192 + 714)

1. Redirects branches whose target is a pure `Lbranch` to the end of the chain, with union-find; chain cycles handled by the representative.
2. 714 lines: the target may do one extra step before reaching the collapsed target, so `forward_simulation_opt` + `measure_branch`/`measure_cond`.
3. For us: a block `params = ps, body = [], term = jmp l ps` (identity forwarding) is bypassed; with arguments, substitute (a two-line `Arg.map` lemma).
4. Do it with a fuel-bounded chain follow (structural recursion on fuel), as a P pass or inside the linearisation order. ~100-200 lines, no measure.
5. Pitfall: a forwarding cycle (`L1: jmp L1`) must stay; bound the chain by the block count. Run it after allocation (allocation deletes moves and creates more forwarding blocks, as CompCert notes).

### 2.4 Linearize.v (217 + 738), Linear.v (267), CleanupLabels (71), Renumber (80)

1. LTL graph → list with labels. The block order is an untrusted function (`enumerate`, "untrusted Caml code", validated a posteriori: only completeness of the list is needed);
   fall-through replaces a `goto` when the successor is next; a conditional picks which edge falls through (negating the condition).
2. 738 lines, `forward_simulation_star` with a measure counting goto-only steps; the bulk is label lookup (`find_label`) and "the pc is inside the block just entered" invariants.
3. `Compiler/Ir/Lin.lean` + `EmitLayout` already are this; labels are block indices into a layout table. Keep that, it avoids `find_label`.
4. Recommend: untrusted order (loop-aware, hot path first, loop rotation: put the test at the bottom; `Flow.rot` of the old route is the statement to port); proof needs only
   "every reachable block appears once".
5. Pitfall: CompCert cannot relax branches (RISC-V 12-bit reach); the trusted OCaml assembler does it. We prove it (pass 11) and must decide reach at emission with final addresses,
   never in the order pass.

### 2.5 Stacking.v (220 + 2218), Bounds (475), Stacklayout (147), Mach.v (504), Separation.v (914)

1. Linear → Mach: frame layout (back link, return address, callee-saves, locals/spills, outgoing args), `Lgetstack` → `Mgetstack sp+ofs`, prologue/epilogue.
2. Second most expensive pass. Frame content is a separation-logic assertion (`frame_contents`, `contains_locations`, `range`, `**`), memory relation is `Mem.inject` with the stack
   block injected into the caller's; every store is an `assign_rule` on a footprint.
3. Our equivalent is `EmitCtx` `MR` + placement: frames are `alloc (slots+1)` events at Lin, placed once; `S slot` ↦ `fp - 8(1+slot)` (`frameAt_top`).
4. Recommend: do not build a separation-logic layer for frames. Take two ideas: (a) disjointness of frame ranges is an *interval* lemma proved once (`range_disjoint`); (b) callee-saved
   registers (ROADMAP "later") are saved at fixed frame offsets in the prologue and restored in the epilogue: state the epilogue lemma as "registers in `calleeSaved` equal their value at entry".
5. Pitfalls: frame size computed from the code (see 2.2 iii); `ra` must be saved before a nested call (CompCert does it in Stacking, not in Asmgen): put it in frame cell 0; stack overflow
   is outside CompCert's model; ours is handled by the frame-fit check before `enter` + OOM flag (keep, it is the better design).

### 2.6 Inlining.v (465 + spec 725 + proof 1263)

1. Whole-function RTL inlining. `should_inline` is a `Parameter` (any choice is correct). Context `ctx` shifts registers (`dreg`), nodes (`dpc`), stack offset (`dstk`) and holds the return
   continuation; callee code is copied with renaming; tail calls inlined with another context; node numbering by a state monad.
2. `Inliningspec`: relational spec of the output; proof: `match_stacks_inside` (callee frame inside the caller's by `Mem.inject` + delta), `star` + `measure`. ~60% is stack-block merging.
3. Ours is simpler: (a) callee frames are events only; an inlined call loses its `alloc/free` pair, `peak` only decreases, and the spec is stated on the final program's events;
   (b) renaming is `Func.rename` (`Rename.lean`); (c) `ret vs` ↦ `jmp cont vs`, `cont`'s params are the call's `ds` (no move glue); (d) tail calls are already `jmp`.
4. Recommend: the relation is "caller registers extended by `regs'(shift r) = callee regs r`"; call step ↦ one `jmp` into the copy (`plus`). Heuristic untrusted (size, leaf, called once, loop depth).
   Order: inlining → facts passes → DCE (they harvest the gain).
5. Pitfalls: bound recursion by fuel, never inline a recursive function into itself; choose `shift = 1 + max reg` and recompute per site (collision of renamed registers is the classic bug);
   inlining a callee that `free`s a block it did not allocate must keep the `free`.

### 2.7 Constprop.v (257 + 625), ConstpropOp, CombineOp (148), ValueAnalysis (2028), ValueDomain (5347), Kildall (1645), Liveness (148)

1. `ValueAnalysis`: forward dataflow with abstract values (`I n`, `Uns/Sgn bits`, `Ptr`, `Ifptr`, `F`, `Vtop/Vbot`) and an abstract memory (`ablock`: contents + summary per block, `bc` block classification).
   `Constprop` rewrites ops to constants (`const_for_result`), folds `Icond` with a known outcome, folds addressing; `CombineOp` merges `add (add x c1) c2`.
2. ValueDomain is per-operator soundness (`add_sound`, `shl_sound`...) plus the `vmatch/mmatch` relations; ValueAnalysis: transfer soundness; Constprop: 1-1 steps. The cost is the domain, not the rewrite.
3. Our domain: `⊤ | const c | [lo,hi] unsigned | ptr blk + offset range (+ size if known from a constant alloc) | ⊥`; operators are `Op/MOp` (finite, enumerable). Est. 400-700 lines vs 7.4k.
4. Recommend: facts map `Lbl → (ρ → AVal)` at block entry is an untrusted result. Checker: interpret the block body abstractly from the entry facts; the exit state, instantiated through
   each edge's args, is ⊑ the successor's entry facts. One theorem `facts_sound` (current registers ∈ γ(facts at pc)). Consumers (each a small P pass under the facts): constant/copy propagation,
   `br` with decided test → `jmp` (this is range-check elimination: `i <u size` known from the loop test and `alloc n`), algebraic simplification (`simp_rhs`: `add (add x c1) c2`, `shl`↦`mul`, byte masks),
   in-bounds facts for LICM of loads. The solver may widen at will; nothing about it is proved.
5. Pitfalls: start with exactly what the benchmarks need (`i+1 < n`, `x &&& 0xff`, constant folds), grow on demand; intervals must say "no wrap" (`hi + c < 2^64` as part of the fact);
   no `bv_decide` (ROADMAP), per-op soundness by `bv_omega`/`simp`; abstract-interpreting `call` kills all heap-derived facts, keeps only register facts.

### 2.8 CSE.v (685 + CSEdomain 273 + proof 1593)

1. Forward dataflow of a `numbering` (`num_eqs`: equations `rhs = Op | Load | Builtin`, `num_reg: reg → vn`, `num_val: vn → list reg`). A recomputed `rhs` becomes `Iop move`. `kill_loads_after_store`,
   calls `kill_all_loads`, `kill_cheap_computations` (a register-pressure heuristic inside the transfer).
2. `numbering_satisfiable` (some valuation makes all equations true) preserved by transfer; loads need `Mem.load_store_other` + addressing separation; `forward_simulation_eventually_plus`.
3. For us: abstract blocks ⇒ a `st p k` only kills load equations of `ld p' k'` with `may_alias p p' ∧ k = k'` (block ids of distinct `alloc`s never alias; the cell index is in the instruction).
4. Recommend: per-block value numbering first (no dataflow, straight-line simulation, ~300 lines). Then extended basic blocks (carry the numbering into a single-predecessor successor, no fixpoint).
   Equations are over block-parameter-renamed registers: reset at join points.
5. Pitfall: CompCert needs `eventually_plus` because CSE/DCE can remove an instruction that would have gone wrong. Our `Refines` quantifies over source runs that exist, so removing or merging
   stuck-capable instructions is free; the dangerous direction is *adding* them (speculative loads, LICM) which needs an in-bounds fact.

### 2.9 Deadcode.v (255 + 1286)

1. Backward neededness: `nval` (which bits matter) per register, `nmem` (which stack/global ranges are read later); pure instructions with unneeded results become `Inop`; unread stack stores removed; ops narrowed.
2. `eventually_plus`, `vagree` (agree on needed bits), `magree`; bulk is bit-level reasoning for ~60 ops.
3. For us only plain liveness: validated pass #5 (`Live.chk`, `SR.dce` generalised to CFG with params). Bit-level neededness skipped (we mask bytes only at `ldb/stb`).
4. Recommend: remove `let_ d rhs` if `d` dead and `rhs` total (`op/mop`; `padd` and `ld` only with an in-bounds fact); also *dead block parameters* (drop param `p` of `l` and the matching arg on every
   `jmp l`/`br`; CompCert has no analogue; renaming-style proof); unreachable blocks fall out of reachability.
5. Pitfalls: removing a dead `alloc` shrinks events (allowed, `memoryNeeded` is read from the final program); removing a `free` raises the peak (not allowed); never remove `st` to a live block or a call.

### 2.10 Unusedglob.v (142 + 1442)

1. Reachability of globals from `main` over code and initialisers, deletion of the rest.
2. 1442 lines, nearly all memory injection of the global environment; reachability is ~150.
3. For us: reachability over `call f`, remove and renumber `FId`; the proof is `call` renaming through a map.
4. Do it first (con-leche, lean-svg and `Init` carry much dead code; every later check scales with function count). ~200 lines.
5. Pitfall: renumber only here; all other passes keep `FId` stable so per-function lifting stays `funcs.map`.

### 2.11 Selection.v (553 + 1508), Cminor (1250), CminorSel (669), SelectOp.vp (491) + SelectOpproof (946)

1. Cminor (structured, expression trees) → CminorSel (machine operators, addressing modes, conditions); smart constructors (`addimm`, `mulimm`, `shlimm`, compare with immediate), each with an `eval_*` lemma.
2. ~30 lemmas of 15-40 lines of `Int` algebra under `lessdef`.
3. We have no expression-tree level. The smart-constructor idea survives as the algebraic simplifier inside the facts pass (2.7) and a words-level peephole (pass 14).
4. Do not add a CminorSel-like level; extend `Target` only after profiling (e.g. fused `addi`+`ld` when the offset fits 12 bits).
5. Pitfall: CompCert needs `.vp` preprocessing to avoid per-target duplication; ours is `Target` laws, so a selection decision never enters the IR.

### 2.12 Memory model: Memory.v (4665), Memtype (1245), Values (2747), Events (1808), Globalenvs (2024)

1. Blocks with bounds, `ZMap` of `memval` (`Byte | Fragment | Undef`), per-byte permissions (`Freeable ⊃ Writable ⊃ Readable ⊃ Nonempty`); `alloc/free/load/store/loadbytes/storebytes/drop_perm`;
   relations `extends`, `inject f` (affine per-block renaming `b ↦ (b', delta)`), `unchanged_on`. `Events` fixes the external-call axioms.
2. ~300 lemmas; the inject family (`store_mapped_inject`, `alloc_parallel_inject`, `free_parallel_inject`) is the heavy part.
3. Our `Mem` (`inp`, `out`, `cells : List (Option Val)`, `blks`) is related by equality across Rename/Lin. Two relations remain:
   **placement** (block ↦ address range inside the work block, injective, disjoint) and **paging** (ROADMAP: block = page list + page table).
4. Recommend: state `Placed L m mc` and `Paged m m'` each with CompCert-style preservation obligations (load/store/alloc/free). Note `inject`'s mapping is affine per block, so paging
   (`(b, o) ↦ table b (o / P) * P + o % P`) is not an instance; copy the obligation list, not the definition. Keep `free`/`alloc` events in the state (CompCert has none; we need `memoryNeeded`).
5. Pitfalls: permissions and `Vundef` fragments cause most of Memory.v; we use `Option Val` for uninitialised cells. Byte access stays on input/output blocks only (IR_DESIGN), so pointers are never split into bytes
   (CompCert's `Fragment` machinery would otherwise be needed). Variable-size frees without paging make `memoryNeeded` inexact (fragmentation); keep the compiler rejecting them until paging lands.

### 2.13 Smallstep.v (2185): simulation framework

1. `semantics` (`state, step, initial_state, final_state, globalenv`), `forward_simulation` (well-founded `fsim_order`; one step ↦ `plus`, or `star` with a decreasing index), `backward_simulation`,
   `forward_to_backward` (source receptive, target determinate, `safe` states), `Behaviors` (`Terminates/Diverges/Reacts/Goes_wrong`).
2. The core (forward ⇒ behaviours of a safe source) is ~200 lines; forward ⇒ backward 700+.
3. `Compiler/Ir/Sim.lean` (93 lines) is the terminating-run version: `Sim` with `next/done`, `Sim.run_ok`, `Refines`. Both sides are deterministic (`run_det`, `step` is a function), so forward is enough
   and the order/measure is dropped (one source step costs one unit of fuel; the target takes `k ≥ 0` steps).
4. Recommend adding: `Sim.refl`, `Sim.comp` (pipelines), `Sim.of_per_function` (2.15), `Refines`-from-checker (validated passes with no stepwise relation), and only if divergence ever enters a spec, an order-based variant.
5. Pitfall: a pass that adds a stuck-capable instruction can turn a stuck source (no claim) into... nothing wrong, but it can also break a *target-side* simulation obligation; keep the only top-level claim
   `Computes` (source terminates with the output), so stuck sources never matter.

### 2.14 RISC-V Asmgen.v (942), Asmgenproof.v (1031), Asmgenproof1.v (1404), Asm.v (1197), Asmexpand.ml (832, trusted)

1. Mach → Asm, one instruction ↦ short straight-line sequence (`loadimm32/64`, `addptrofs`, `transl_cond_branch`, `transl_load`); pseudo-instructions expanded by trusted OCaml, assembled by the system assembler.
2. `exec_straight` (straight-line steps from pc to pc+n), `transl_code_at_pc`, one correctness lemma per op and per addressing/immediate case (1404 lines: register algebra and immediates under `lessdef`).
3. `Target`/`WideF`/`runsTo`/`At s pc enc` is `exec_straight` over Sail; no pseudo-instruction level exists, so the expander is not in the trusted base.
4. Take the decomposition when `Target` grows: constants `li` (12-bit) / `lui+addiw` (32) / chain or `auipc`+pool (64); fold `padd p (i + c)` into the load offset when it fits 12 bits; compare-and-branch both polarities
   (already in `WideF`); `Reg` as a field excluding `x0` as a destination (IR_DESIGN 2.5). ARM `apcwF` has the same shape.
5. Pitfalls: CompCert RISC-V bugs sat in the trusted expander and float conversions; we have neither. `ra` handling (2.5). Large frames: `enterOK` must check `n ≤ maxSlots`, offsets beyond 12 bits need a scratch register (already `encE` n).

### 2.15 Linking.v (936) and the per-pass `match_program`

1. `linkorder`, `Linker` class, `match_program_gen`, "match is preserved by linking"; every pass is stated as `match_prog p tp` over whole programs with `genv` agreement (`symbols_preserved`, `funct_ptr_translated`).
2. 936 lines of unique-definition algebra on `PTree`.
3. Not needed (one `Prog` per `compile`). Take the shape: a pass is `transf_function` and `transf_prog = ⟨funcs.map f, main⟩`; one generic lemma `Sim.of_per_function` (per-function simulation +
   the same table ⇒ whole-program `Sim`) is proved once. ROADMAP's tier 2 (hand-optimised function interchangeable with the compiled one) is a function-level `FuncRefines` replaced inside `funcs`.
4. Recommend: skip Linking and `genv`. `symbols_preserved` is `rfl`/`List.getElem_map` for us (same indices).
5. Pitfall: a cross-function call relation must not assume the callee is unchanged (inlining and per-function allocation change callees): relate `call` through the callee's own `Sim`, i.e. use a
   `Sim` that quantifies over the simulation of callees, not a syntactic equality.

### 2.16 Certora/clean (CCLib 15.2k lines Lean: ClightExec 488, ClightExecSound 576, Determinism 738, Hoare 437, SepLogic 647, SepHoare 1233, Linking 405, Memory 407, Values 570, Cop 865)

1. Lean 4 port of CompCert's Clight syntax, memory, values, step relation; an executable interpreter proved sound against the relation (the interpreter exists because CompCert's `Step` is a relation and has no
   executable Clight); determinism of `Step`; a Hoare logic *defined* as a statement about `Step` (soundness definitional, only rules proved); a separation logic with frame (`Triple` quantifies over a frame heap `hf`
   disjoint from the fragment `hp`, `triple_frame` from union associativity). Trusted OCaml C→Clight front end.
2. Everything is a 1:1 port; the cost sits in Memory/Values/Cop (stubs with fewer lemmas than CompCert's). Their `Linking.lean` and floats are irrelevant here.
3. Not a dependency (non-commercial, experimental, CompCert memory model). Possible later as a SOURCE (ROADMAP plan 2: Clight → IR proved in Lean against their semantics). Style to adopt:
   (a) semantic triples over `Runs` for the middle Hoare logic: define `{P} code {Q}` by unfolding the run, prove the rules, no separate soundness theorem;
   (b) the frame as a disjoint heap fragment fits block-based memory: a triple names the blocks it touches, the frame is the rest (this is also the shape of our separation theorem for multi-core in ROADMAP);
   (c) interpreter-soundness is unnecessary for us because `step` is already a function.
4. Recommend: C stays a differential-testing oracle (ROADMAP item 1); do not port anything now.
5. Pitfall: C undefined behaviour is "stuck" in their `Step`; a Clight → IR `fe_ok` must carry the no-UB facts of the source run, and block/pointer comparison rules must match ours (`nullTest`: pointers only compare to null).

## 3. Pitfalls CompCert hit (collected)

1. Measures and stuttering in four passes (Tunneling, Linearize, Inlining, RTLgen). Avoid with fuel-based `Sim` and `plus`-style steps.
2. `Vundef`/`lessdef` threaded through Deadcode, CSE, Allocation, Asmgen. Avoid with exact `Val` equality and registers starting at `.w 0`.
3. Analysis infrastructure dominates proofs (ValueDomain 5347, Kildall 1645, PTree lemmas). Avoid with sorted lists, small domain, checkers only.
4. Frames as injected memory (Stacking 2218 + Separation 914). Avoid with events + one placement theorem.
5. Trusted pieces beside the proofs: parser, `Asmexpand.ml`, assembler, linker. We have none; keep it so (no `extern`).
6. `Qed` evaluation: CompCert extracts to OCaml and never kernel-evaluates the compiler. We do (`decide +kernel`): no WF recursion or `HashMap` in `compile`; searches as hints;
   one CI file kernel-evaluating `compile` on three small programs (IR_DESIGN §5).
7. Per-instruction nodes force `Renumber`, `CleanupLabels`, label-lookup lemmas. Blocks with `Nat` labels avoid them.
8. No cost theorem: passes that touch `alloc/free/call` must say what they do to the event list (inlining drops pairs, allocation fixes `slots`). Add one schema `peak_le` for passes that only shrink events.
9. Heuristics as `Parameter`s (`should_inline`): in Lean pass them as hint arguments (`compile hints P`), never `opaque`/`axiom`.
10. Pass order matters: Tunneling after allocation, CSE before Constprop, Deadcode last; facts are never reused across passes, recompute per pass (the checker is cheap).

## 4. What NOT to copy

- Coq proof scripts, lemma statement text, file layout (licence). Re-derive from the idea, state in our own types.
- `Mem.inject`, permissions, `memval` fragments, `Genv`, `ident`/`positive` maps, the `Errors` monad (use `Option`), `Vundef`, `lessdef`.
- RTLtyping, int/long/float register classes, parallel-move and register-pair handling, `Ibuiltin`, volatile, inline asm.
- Trusted assembler/expander; any C-specific part (Cop, Csem, Cshmgen, SimplLocals).
- CminorSel/Selection level, Linking framework, `Unusedglob`'s global injection, CSE's partially-redundant-cheap-op heuristic, bit-level neededness.
- Anything that makes `compile` non-structural (`Function`, `PTree` fixpoints, proof-carrying termination such as Kildall's iterations).

## 5. Next steps (cheapest first)

1. `Sim.refl`, `Sim.comp`, `Sim.of_per_function` in `Compiler/Ir/Sim.lean`.
2. Unreachable-function removal (`FId` renumbering).
3. `Compiler/Ir/Facts.lean`: `AVal`, abstract `Rhs.eval`, `Check facts P`, `facts_sound`; consumers: const/copy prop, branch folding, DCE (with dead block params).
4. Liveness validator + slot sharing (smaller `memoryNeeded`).
5. Register equation validator + linear-scan hint; generalise `Target.Reg`.
6. Forwarding-block removal inside the `Lin` order pass; leaf inlining with fuel; per-block CSE.
