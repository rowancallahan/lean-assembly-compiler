# Step 9 prototype: GenRef over an abstract emitter (branch `proto-genemit`, throwaway)

Files: `Nano/V2Self/Proof/Gen/Proto/Emit.lean` (309 lines), `Proto/Lay.lean` (99 lines). Nothing live imports them.
No sorry / axiom / native_decide. Gen's C source, GenRef and Proof/Machine are untouched.

## Finding

GenRef's item proofs (`v_*`, `t_*`) never look inside the emitted words: they use an emitter only through `PI`
(append-only), a length bound, and the opaque list `em F h`. The RISC-V content of GenRef is confined to
1. the 40 dispatch lemmas `g36_*`, `g37_t*`, `st_t*`, `g38_*` (413 lines: `unfold; extract_lets; rw [if_neg …]`);
2. the names of the emitters inside the `CG`/`CT` constructors (44 `em (…)` sites);
3. jumps: `g13`/`jw` as ONE word, `g14`/`JOk` (113 sites), hard-coded lengths (`+5`, `+1`, `+3`, `+2`, `ifHd` = 4);
4. exit/branch placeholders as ONE `0` word patched by one `bset` (`set_mid`/`bset_mid` 8 sites, `patchR`, `g28_ok`,
   and `Mt`'s `c[j]? = some 0` in NdCG);
5. the size limits (`big`/`live`: 2^24 cells, `Fx`: 65536).

The "words = `encG` of J templates" statement is a second, already separate layer (NdCG*: `CG → Mt c (tm S e h) …`,
via the `*_exact` lemmas). So step 9 is two independent factorings, not one.

## Design

**Layer 1 (GenRef), `Emit.lean`.**
* `Em`: what a target appends per emit call, in code-buffer cells: `const`, `jmp d a b : List cell`, its length `jl`
  (independent of the displacement), `rng a b : Bool`. Laws `Em.OK`: `PI`, length bounds, `jmp_len`.
  Full version adds: push, local (g25), pop (g26), bin (g31), prim (g32), ifHd, lpHd, lpDec, prologue, epilogue (g29),
  stubs/start (g34/g35), `hole` (= `jl` zero cells) and `patch`.
* `Src`: a Gen source = its `visit` (g36) and `item` (g37). `Src.OK S E` = the dispatch equations, stated over `E`.
  Register file, item stack and fixup helpers (g15–g18, g27) stay shared.
* `st`, `it`, `Reach`, `CG`/`CGs`, `VPost`, `VS` take `S`/`E` as parameters; `Inv`, `Stk`, `Fx`, `live`, `err`, `big`
  and all their lemmas are reused from GenRef unchanged (they do not mention g36/g37).

**Layer 2 (templates), `Lay.lean`.** J offsets stay in J-instruction units. A target is `Tgt`: `size : J → Nat` and
`enc : (native displacement) → J → cells`. A layout `pos : J index → cell index` is the prefix sum of `size`
(`GLay T pos C`); `encL T pos q l` encodes a template at J index q, each jump from `pos (q+off) − pos q`.
`lay_at` (`pos (q + |l|) = pos q + |encL …|`) replaces today's `h + c.length` arithmetic. `Exact E T` is the
per-target tie (emitter output = `encL` of the template). RISC-V: size 1, `pos = id`, `enc _ j = [encG j]`.
ARM blocks: size 4, `pos q = 4q`. x86-64: `size` per J shape, jumps always rel32 (fixed length), `pos` non-linear.

## What the prototype proves (all build, RISC-V instance closed)

* generic `v_const`, `seq`, `v_call` for any `S`, `E` with `S.OK E`, `E.OK` (CONST; CALL = operand sequence + item 7 +
  def-table jump with range check);
* `rvSrc_ok : rvSrc.OK rvEm` whose fields ARE the existing `g37_visit`, `g36_const`, `g36_call`, `g37_t7`+`g19_eq`;
* `st rvSrc = GenRef.st` (rfl), `reach_rv`, `cg_rv`/`cgs_rv` (generic CG at `rvEm` ⇒ `GenRef.CG`), `v_const_rv`
  (GenRef's theorem recovered from the generic one);
* `lay_at`, `em_const` (generic CONST matching step), `rv_exact : Exact rvEm rvT` from `const_exact` and `g13_enc`.

What changed when porting the three proofs: `bpush o (g13 …)` → `o ++ E.jmp …`, `g14 … == 1` → `E.rng …`, the
constant 21 → `E.cb`, one extra bound (`jl < 2^32`) for `big`. Two compile fixes, nothing structural.

## Not prototyped / blockers

* **Fixups (IF, tail exits, LOOP).** Not done. Needs `hole`/`patch` in `Em` and a multi-cell splice lemma in place of
  `bset_mid`; `v_if` (210 lines), `t_if` (200), `v_loop` (90), `t_val`, `g28_ok`/`patchR` and `Mt` carry the one-cell
  assumption. This is the real cost of layer 1; expected mechanical but long.
* **A native Gen is another C source.** `Src.OK` only transfers if its g36–g39 are the RV ones with emit calls
  swapped (same register file, item tags, fixup buffer). Raw emits inside g36/g37 (lines 247, 266, 270, 288, 298 of
  C/Gen.lean: loop head, IF branch, `bpush o 0` holes) must become emitter calls in that source. Its 40 dispatch
  lemmas are then re-run copies (≈400 lines per target). Untested alternative: one Lean `g36E E`/`g37E E` with
  `g36 = g36E rvE` by unfolding, so the dispatch lemmas are proved once.
* **Variable length (x86-64).** Layer 1 is indifferent (cells, list-valued `jmp`). Layer 2 needs `pos` threaded through
  `Mt`, `tm`/`lnV` (today one `h` is both J index and word index) and NdDef/NdTop. The hard blocker is downstream and
  outside step 9: `addr base pc = base + 4·blockLen·pc`, the link convention `b + w·pc` (`St.wk`, `link_div`), `SafeX`
  jalr and `Target.lay` all assume uniform blocks. Cheap way out: pad each J instruction's x86 code to a uniform block
  (`pos q = B·q`), which needs none of that. Also J uses 16 registers besides x0; x86-64 has 16 including rsp.
* Size limits (2^24 cells, ±1 MiB) are in `live`/`big`/`g14`; with `rng` abstract only the 2^24 constant remains.

## Effort estimate (full step 9)

| part | effort | risk |
|---|---|---|
| Layer 1: `Em`/`Src` parameters through GenRef + GenTop/GenAll, multi-cell holes/patch | 2–3 sessions | medium (long, mechanical; GenRef builds in ~1 min) |
| Layer 2, uniform layout (`pos q = B·q`): `Mt`, NdCG*, MachExact/ExprExact/CallExact as `Exact` fields | 1–2 sessions | medium |
| Layer 2, general `pos` (true variable length) | +2 sessions | medium-high |
| non-uniform `addr`/link values in JLay/Target/both targets | separate, L+ | high |
| per new target: `Em.OK`, `Exact`, dispatch lemmas | 1–2 sessions each | low-medium |

Recommendation: do layer 1 with list-valued `jmp`/`hole`/`patch` from the start (covers ARM blocks and x86), layer 2
with uniform `pos` first, and decide on padded x86 blocks before paying for non-uniform `addr`.
