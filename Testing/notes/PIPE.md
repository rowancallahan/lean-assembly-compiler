# Pipe: list code → proved machine code

Branch `pipe`. Files: `Compiler/Front/Pipe.lean`, `PipeSrc.lean`, `PipeMachine.lean`, `PipeOk.lean`, `PipeFront.lean`,
`PipeExamples.lean`, `PipeEncode.lean`; `Testing/asm/emit_pipe.lean`, `Testing/asm/pipe_test.py`. No existing file is changed.

## Status

Kernel-checked (`lake build Riscv.Examples.PipeExamples Compiler.Front.PipeEncode` passes; no `sorry`, no new `axiom`, no
`native_decide`, no `bv_decide` in `Compiler/Front/Pipe*.lean`; `#print axioms`):

- `Pipe.prog_exec`, `leBytes_eq_enc`: `propext`, `Classical.choice`, `Quot.sound`.
- `compileP_of_ok`, and each `compile%` example value (e.g. `PipeEx.revinc5`, `PipeEx.twosort`): `propext`, `Quot.sound`.
- `compileP_ok` (hence `Compiled.ok`, `compileP_mapped`, `compileP_view`): the same set as the existing
  `sortCode_implements` (the three above + the 7 model constants + the 67 `riscv_*` externs).

Done: P1 (DSL), P2 (`compileP`, generic theorem, `Pipe.ok`), P3 (`compile%`, 11 accepted + 6 rejected
examples), P4 (tests), P5 (this file).

Partial / deviations from the brief:
- The generic theorem is `compileP p = .ok code → ImplementsPipe code p.denote p.space`, not
  `ImplementsMapped` (difference below). `ImplementsMapped` is proved under `∀ n, p.space n ≤ p.len n`
  (`compileP_mapped`), and unconditionally for pipes without `sort`/`fold` (`compileP_view`).
- No scratch block and no ping-pong buffers: everything is done in the output block (reason below).
- `compile%` is a term elaborator returning a `Compiled` structure; the code words are the term
  `c.code = compileAF [0,3] c.pipe.prog` (evaluated by `#eval`), not a literal list.
- For `sort`-containing pipes `ImplementsMapped` is shown per example (`mapsort_mapped`), no general lemma.
- Nothing failed that is left in the tree.

## Usage

```lean
def revinc5 := compile% fun xs : List UInt8 => ((xs.take 5).map (· + 1)).reverse
-- revinc5 : Compiled encL (fun xs => ((xs.take 5).map (· + 1)).reverse)
#eval revinc5.code          -- the RV64 words
theorem revinc5_ok : ImplementsPipe revinc5.code (fun xs => ((xs.take 5).map (· + 1)).reverse)
    (Pipe.space revinc5.pipe) := revinc5.implements
```

`compile% f` elaborates `f`, reifies its body into a `Pipe` (error naming the subterm if it cannot), runs
`compileP` (error with the compiler's reason if it rejects), and builds
`Compiled.mk pipe (denote : ∀ xs, enc (f xs) = pipe.denote xs) (check : (compileP pipe).toBool = true)`.
`denote` is proved by `fun _ => rfl` (fallback `simp`), `check` by `decide +kernel`; if either fails the
elaboration fails. The reifier is untrusted: only these two kernel-checked proofs matter.
`Compiled.ok : ImplementsPipe c.code (fun xs => enc (f xs)) c.pipe.space`,
`Compiled.implements` (list results: about `f` itself), `Compiled.mapped` (`ImplementsMapped`, see below),
`Compiled.compiles : compileP c.pipe = .ok c.code`.

Result encodings (`enc`): `List UInt8` as is (`encL`); `UInt8` as the one-byte list (`enc1`); `BitVec 64` as
its 8 little-endian bytes (`enc8 w = leBytes w 8`, and `leBytes_eq_enc : leBytes w 8 = Bytes.enc w` for the
`Bytes (BitVec 64)` instance of `Spec/Encode.lean`; `enc1` is `Bytes.enc` for `UInt8` by `rfl`).

## The DSL (`Compiler/Front/Pipe.lean`)

```
Pipe  ::= List Stage                      -- applied left to right; composition is ++ (Pipe.denote_append)
Stage ::= map BExp                        -- List.map (fun x => e.denote 0 x)
        | take n | drop n                 -- List.take n, List.drop n          (n : Nat)
        | reverse                         -- List.reverse
        | sort                            -- List.mergeSort (· ≤ ·)  (leU)
        | fold BExp (init : UInt8)        -- [l.foldl (fun a x => e.denote a x) init]          (1 byte)
        | foldW WExp (init : BitVec 64)   -- leBytes (l.foldl (fun a x => w.denote a x) init) 8 (8 bytes)
BExp  ::= x | acc | lit (c : UInt8) | bin (add|sub|and|or|xor) BExp BExp
        | ite (lt|le|eq|ne) BExp BExp BExp BExp       -- if a ⋈ b then t else e      (UInt8 semantics)
WExp  ::= acc | x | const (c : BitVec 64) | bin Op WExp WExp | ite WExp WExp WExp
                                           -- Op of Spec/Code.lean (11 operators), x zero-extended
```

`Pipe.denote p xs = p.foldl (fun l st => st.denote l) xs`; every `Stage.denote` is the plain list function
named above, so `rfl` relates a user term to its pipe.

What the reifier accepts (body of `fun xs : List UInt8 => …`): `List.map f`, `List.take n`, `List.drop n`
(`n` any closed `Nat` term), `List.reverse`, `List.mergeSort` (default order), applied to the argument in any
order and number, optionally under one outer `List.foldl` with a `UInt8` or a `BitVec 64` accumulator.
Byte functions: `+ - &&& ||| ^^^`, `if a ⋈ b then t else e` with `< ≤ > ≥ = ≠` on bytes, closed `UInt8`
terms; a function given by name is unfolded once. Word fold steps: the `reify%` operator set (`+ - &&& |||
^^^`, shifts by `b.toNat % 64`, `if a < b then 1 else 0`, `if a = b then 1 else 0`, `if c = 0 then y else x`,
closed constants), the element written `x.toBitVec.setWidth 64`.

## Compilation scheme (`Pipe.prog`, `stageC`, `mat`)

Blocks: 0 = input (`a0`), 1 = output (`a3`), `bv = [0, 3]`. The scratch block (`a2`) and the stack are not
used: with 8 variables, the insertion sort (`insProg`, reused unchanged) needs 6 besides its block base, so a
third base register does not fit. `a2` is the loop counter instead.

The current list is a *view*: a window `[s, s+m)` (`s = a4`, `m = a1`) of the input or of the output block,
read forwards or backwards (compile-time flag), with a compile-time list of pending byte maps.

- `take`/`drop`: one or two assignments to `s`/`m` (branch-free `min`); `reverse`: flips the flag;
  `map e`: appends `e.tr` to the pending list. So any chain of `map`/`take`/`drop`/`reverse` is one loop.
- materialization (`mat`; at the end and before `sort`): `for i < m: a6 := block[idx i]; a6 := g₁; …;
  a6 := gₖ; out[i] := a6`, then `s := 0`. `idx i = s + i` or `s + m - 1 - i`. From the output block onto
  itself this is done in place (forwards only: `s + i ≥ i`); a backwards view of the output block is first
  reversed in place (`revC`, swap loop). Nothing is emitted if the view already is `out[0..m)`.
- `sort`: materialize, then `insProg` on `out[0..m)` (`ins_exec` + the frame lemma `AExec.frame`: a
  program run on blocks with extra bytes appended).
- `fold`/`foldW`: `a5 := init; for i < m: fetch; a5 := step`, then `m := k` (1 or 8) and a loop storing the
  `k` low bytes of `a5` to `out[0..k)`.

Byte expressions translate to word expressions computing the exact zero-extended byte (`BExp.tr_ok`):
`+`/`-` are followed by `&&& 255`, comparisons use `ult`/`eq`, `ite` is the branch-free select.

## Theorems

```lean
-- Compiler/Front/PipeSrc.lean (source level; axioms: propext, Classical.choice, Quot.sound)
theorem Pipe.prog_exec (p : Pipe) (hc : ∀ st ∈ p, st.chk = none) (xs : List UInt8) (out : List (BitVec 8))
    (env : AEnv) (h1 : env 1 = .ofNat 64 xs.length) (hx : xs.length < 2 ^ 32)
    (hsp : Pipe.space p xs.length ≤ out.length) (hL : out.length < 2 ^ 32) :
    ∃ σ' out', AExec (Pipe.prog p) ⟨env, [tbs xs, out]⟩ σ' ∧ σ'.heap = [tbs xs, out'] ∧
      out'.length = out.length ∧ out'.take (Pipe.denote p xs).length = tbs (Pipe.denote p xs)

-- Compiler/Front/PipeMachine.lean
def compileP (p : Pipe) : Except String (List (BitVec 32))
theorem compileP_ok {p code} (h : compileP p = .ok code) : ImplementsPipe code (Pipe.denote p) (Pipe.space p)
theorem compileP_mapped {p code} (h : compileP p = .ok code) (hs : ∀ n, Pipe.space p n ≤ Pipe.len p n) :
    ImplementsMapped code (Pipe.denote p)

-- Compiler/Front/PipeOk.lean
theorem compileP_of_ok {p : Pipe} (h : Pipe.ok p = true) : ∃ code, compileP p = .ok code
```

`compileP p` fails with a message in exactly these cases: a `Stage.chk` fails (`take`/`drop` count `≥ 2^64`;
`map` body mentioning `acc`), or `wfErr [0,3] p.prog` reports an `AStmt.wf` violation (an expression deeper
than the temporaries allow; a loop of more than 1023 words). `wfErr_iff : wfErr bv p = none ↔ p.wf bv`.

### `ImplementsPipe` vs `ImplementsMapped`

`ImplementsPipe code f space` is `ImplementsMapped code f` (`Riscv/Direct/SortMachine.lean`) with two changes:

1. the two output-block hypotheses are stated for `space |x|` bytes instead of `|f x|` bytes:
   `space x.length ≤ output.len` and `∀ i < space x.length, (s.mem[output.base + i]?).isSome`;
2. the hypotheses `x.length ≤ scratch.len` and `stackLen ≤ stack.len` are dropped (neither block is used).

Conclusion and all other hypotheses are identical. `Pipe.space p n` (`Pipe.need p cs0 n`) is the largest
list the code writes to the output block for an input of `n` bytes: the view length at each `sort` that has
to materialize, 1 or 8 at a fold, the result length at the end. Why a variant: the output block is the
only buffer, so `take 3 ∘ sort` writes `n` bytes there although the result has 3.
`ImplementsPipe.mapped`: if `space |x| ≤ |f x|` the statement is `ImplementsMapped`; this holds e.g. for
every pipe of `map`/`take`/`drop`/`reverse` and for pipes ending `… sort` followed only by `map`/`reverse`
(shown per example by `simp`: `revinc5_mapped`, `mapsort_mapped`; no general lemma).

### What compiles (`Pipe.ok`, decidable)

`Pipe.ok p` = every stage passes `Stage.chk`, every map/fold expression `e` has `e.tr.depth ≤ 6`
(`BExp.tr_depth_le : e.tr.depth ≤ 2 * e.height`, so byte expressions nested at most 3 deep always qualify;
left-leaning chains like `x + 1 + 2 + …` have depth 1), and `Pipe.cost p ≤ 950`, where `Pipe.cost` sums
`BExp.size`/`WExp.size` (bounds on generated words: 1 per variable, 17 per byte literal, 129 per word
constant, 19 per byte `+`/`-`, 1–2 per other operator, 7 per byte `ite`, 5 per word `ite`).
The condition is sufficient, not necessary (`compileP` checks the real depth and loop sizes).

## Limits

- Inputs `≤ 2^20` bytes (from the spec; the proof needs `< 2^32`).
- Output block `≥ Pipe.space p |x|` bytes, present in the memory map.
- Stages: only the seven above. No `filter`, `append`, `zip`, `mapIdx`, `length`, data-dependent counts, no
  second use of the input (`xs ++ xs.reverse`), no custom sort order, no byte `*`, `/`, shifts.
- Expression depth: `e.tr.depth ≤ 6` for map and fold steps (7 temporaries, no spilling).
- All pending maps of a `map`/`take`/`drop`/`reverse` chain share one loop body; body + loop overhead
  `< 1024` words (`beq` reach). Constants are built bit by bit (17 words for a byte literal, up to 129 for a
  word constant), so about 40 byte-literal operations per chain.
- `sort` is the proved merge sort (since PipeStd; before: the quadratic insertion sort).
- Not optimal code: each byte `+`/`-` is masked (19 words); a fold result is stored by a loop;
  `take`/`drop` evaluate `min` twice.

## Tests (`Testing/asm/pipe_test.py NAME N`)

Words: `lake env lean Testing/asm/emit_pipe.lean` → `Testing/asm/pipe-words/NAME.words`, and `NAME.space` (`Pipe.space` for
`n = 0..64`, computed by Lean). Per input: `a0` = input, `a1` = length, `a2` = random word, `a3` = 128-byte
output slot filled with `0x55`. Checked on QEMU and on the Sail C emulator against a Python model of the
Lean function: the first `|result|` output bytes; output bytes from `Pipe.space |xs|` on untouched; input
slot unchanged; every Sail data write inside `out[0, space)`. Inputs: `[]`, five fixed short lists, then
random lists of length 0..64 (random, few-valued, sorted, reverse-sorted). The Python models were also
compared with `Pipe.denote` (`#eval`) on 5 inputs per example. Result (300 inputs each, all pass):

```
revinc5: 300/300 ok (QEMU == Sail == model, 81 words)
mapsum: 300/300 ok (QEMU == Sail == model, 127 words)
revtake5: 300/300 ok (QEMU == Sail == model, 82 words)
mapsort: 300/300 ok (QEMU == Sail == model, 117 words)
sort: 300/300 ok (QEMU == Sail == model, 99 words)
sum64: 300/300 ok (QEMU == Sail == model, 64 words)
hash64: 300/300 ok (QEMU == Sail == model, 91 words)
sortdesc: 300/300 ok (QEMU == Sail == model, 220 words)
mid: 300/300 ok (QEMU == Sail == model, 179 words)
foldsorted: 300/300 ok (QEMU == Sail == model, 233 words)
twosort: 300/300 ok (QEMU == Sail == model, 379 words)
```
(`sort` here is 99 words; the hand-written `sortCode` is 104.)

## Check times

`lake env lean Proven/X.lean`, imports prebuilt, 4-core box: `Pipe` 1.2 s, `PipeSrc` 4.4 s, `PipeMachine` 1.2 s,
`PipeOk` 2.2 s, `PipeFront` 1.2 s, `PipeExamples` 1.1 s (11 `compile%` + 6 rejected + 4 `Pipe.ok`),
`PipeEncode` 0.7 s. Lines: 254 / 815 / 220 / 308 / 226 / 129 / 23.

## Standard-library functions (`Compiler/Front/PipeStd*.lean`, 2026-11-14)

`compile%` now builds an `XPipe` (list of `XStage`: every old `Stage` via `XStage.base`, plus `red r`,
`filter p`, `takeWhile p`, `dropWhile p`, `appendC c`) and compiles it with `compileX`
(`Compiler/Front/PipeStdBMachine.lean`). `List.mergeSort` is now the proved bottom-up merge sort
(O(n log n), `msortG`, `Riscv/Direct/SortMergeGen.lean`), no longer the insertion sort.

### Theorems

```lean
-- Compiler/Front/PipeStdMachine.lean  (pipes without a sort: two blocks, no stack, as compileP)
def ImplementsPipeLen code f space :=   -- hypotheses exactly those of ImplementsPipe; conclusion:
  ... runsTo s fun s' => PC = ra ∧ bytesAt s' output.base (f x).length = (f x).map some ∧
      unchangedOutside s s' [input, ⟨output.base, space x.length⟩] ∧ calleeSavedKept s s' ∧ Cfg s' ∧
      s'.regs.get? .x11 = some (BitVec.ofNat 64 (f x).length)
theorem compileXA_ok (h : compileXA p = .ok code) : ImplementsPipeLen code (XPipe.denote p) (XPipe.space p)
-- Compiler/Front/PipeStdBMachine.lean (all pipes; a sort uses BStmt with 7 slots and a scratch block)
def ImplementsPipeS code f space sspace stackLen :=  -- ImplementsPipeLen's hypotheses plus
  --   sspace x.length ≤ scratch.len, stackLen ≤ stack.len, scratch bytes [0, sspace) present; conclusion:
  ... unchangedOutside s s' [input, ⟨scratch.base, sspace x.length⟩, ⟨output.base, space x.length⟩, stack] ∧
      calleeSavedKept s s' ∧ Cfg s' ∧ s'.regs.get? .x11 = some (BitVec.ofNat 64 (f x).length)
theorem compileX_ok (h : compileX p = .ok code) :
    ImplementsPipeS code (XPipe.denote p) (XPipe.space p) (XPipe.sspace p) (XPipe.stack p)
-- XPipe.stack p = 71 if p has a sort (64-byte frame + alignment), else 0; XPipe.sspace = largest view at a sort
```
Axioms of `compileXA_ok`, `compileX_ok`: the 77 of `compileP_ok` (checked by `Testing/scripts/axioms_c.lean`).
`Compiled.ok` (ImplementsPipeS for `fun xs => enc (f xs)`), `Compiled.okLen`/`okPipe` (sort-free:
`ImplementsPipeLen`/`ImplementsPipe`), `Compiled.mapped` (ImplementsMapped), `Compiled.mapped2`
(ImplementsMapped2, stack 71).

**Variable-length results (one convention, the same as `Spec/Implements1.lean`'s `retLen`):** the result is
the first `a1` bytes of the output block (`a1` = `x11`, the second ABI return register, holds `|f x|` at the
return; proved for every pipe). Output bytes in `[|f x|, space |x|)` are unspecified (used as a buffer);
output bytes from `space |x|` on are unchanged (proved: `unchangedOutside … ⟨output.base, space x.length⟩`).
Fixed-length results are unchanged (`a1` is just their constant length). Bytes beyond the result are NOT
restored to their old value: filter/sort/Option results use the output block as a buffer.

Result encodings (`Spec/Encode.lean`, nothing added there): `List UInt8` raw (+ length in `a1`), `UInt8` 1
byte, `Bool` 1 byte 0/1, `BitVec 64` 8 bytes LE, `Option UInt8` `[0]` or `[1, v]`; a `Nat` result is written
`BitVec.ofNat 64 n` (or `(n : BitVec 64)`).

### Stdlib function table

| Lean function (on `List UInt8`) | stage | status | notes / limits |
|---|---|---|---|
| `map f` `take n` `drop n` `reverse` `foldl` | old `Stage` | proved, tested | as before |
| `mergeSort` (default order) | `base .sort` → `msortG` | proved, tested | O(n log n); scratch `n` bytes, 71 stack bytes |
| `length` (as `BitVec.ofNat 64`) | `red .length` | proved, tested | O(1) (`a1`) |
| `sum : UInt8` | `red .sum8` | proved, tested | mod 256 |
| `(l.map UInt8.toNat).sum` (as `BitVec 64`) | `red .sum64` | proved, tested | |
| `countP p`, `count b` | `red .countP/.count` | proved, tested | `p` a byte condition, `b` closed |
| `any p`, `all p`, `contains b`, `elem b`, `isEmpty` | `red` | proved, tested | `Bool` |
| `head?`, `getLast?`, `l[i]?` (closed `i`) | `take 1`/`reverse`/`drop i` + `red .head` | proved, tested | `Option UInt8` |
| `find? p`, `min?`, `max?` | `red` | proved, tested | `Option UInt8`, full pass |
| `findIdx p`, `idxOf b` (as `BitVec 64`) | `red .findIdx/.idxOf` | proved, tested | |
| `filter p`, `takeWhile p`, `dropWhile p` | stateful-filter loop | proved, tested | length in `a1`; in place on the output block |
| `l ++ c`, `c ++ l` (`c` closed, e.g. `List.replicate 3 0`) | `appendC` (prepend = reverse, append, reverse) | proved, tested (`suffix`, `prefixRev`) | stores unrolled: ~20 words per constant byte |
| compositions of all the above | `XPipe` | proved, tested | e.g. `(xs.filter (· > 3)).mergeSort`, `((xs.dropWhile …).filter …).length` |

Predicates `p` (`BPred`): `<, ≤, >, ≥, =, ≠` (as `decide`), `==`, `!=`, `&&`, `||`, `!`, `true`, `false` over byte
expressions (`+ - &&& ||| ^^^`, `if`, literals).

### Not done / does not fit (why)

- `zipWith f xs xs.reverse`, `zipWith f xs (xs.drop k)`, `mapIdx`/`enum`-style maps: fit the scheme (one
  loop, in-place pair swap / forward read-ahead / index in `a2`), not implemented in this round (each needs
  a new loop proof).
- `xs ++ xs.reverse`, `xs ++ ys` with both sides from the input: needs a second view of the input (one more
  view register pair); not implemented. `++` of two non-constant lists is rejected with a message.
- `List.range n |>.map f`: the result does not depend on `xs` (constant output); not implemented.
- `rotateLeft k`: needs `k % length` at run time — a modulus (no `rem` in `Op`).
- `eraseDups`: quadratic (nested loop) or a 256-bit seen table in scratch; not implemented.
- `replicate n b` with `n` from the input, `take xs.length` etc.: counts must be closed (`Nat` from data).
- byte `*`, `/`, `%`, shifts in byte expressions: not in `ByteExp` (no multiply / divide in `Op`).
- `zip`, `product`, two-list functions (`isPrefixOf ys`, `diff`): need two inputs (the spec has one).
- `sum`/`length` as unbounded `Nat`: must be `BitVec.ofNat 64` (no `Bytes Nat` encoding).
- `List.sort`/`mergeSort` with a custom order, `insertionSort`: only the default `≤`.
- `findIdx?`/`idxOf?` (`Option Nat`), `lookup`, `partition` (pair of lists), `splitAt`, `groupBy`: result
  encodings (`Option Nat`, pairs of variable-length lists) not provided.
- Not provided: a decidable `XPipe.ok` success condition for the new stages (the compiler's own check,
  run by `compile%` with `decide +kernel`, is the criterion; `Pipe.ok` still covers old-stage pipes).

### Compilation of the new stages

- Reductions (`redC`): `a5 := init` (over `a1`), optional loop `a6 := view[i]; a5 := step`, optional
  `a5 := fin`, store the `k ≤ 8` low bytes of `a5`, optional `a1 := len`. Option words: `none ↦ 0`,
  `some v ↦ 1 + 256 v` (stored as `[tag, v]`, `a1 := tag + 1`); `findIdx` state `2 i + found`.
- Filters (`sfC`): view on the output block is first materialized; then `a5 := s0; a7 := 0; for i < m:
  a6 := view[i]; out[a7] := a6; a7 += (K ≠ 0); a5 := N`; `a1 := a7`. `filter`: `K = p`; `takeWhile`:
  `K = N = s &&& p`, `s0 = 1`; `dropWhile`: `K = (s &&& p) ^^^ 1`, `N = s &&& p`, `s0 = 1`.
- Sort (`sortB`): view = input itself (`cs0`): `msortG 0 1 2` (input → output, scratch); else materialize
  to `out[0..m)`, copy to `scr[0..m)`, `msortG 2 1 2`. The `AStmt` stages run renamed (`a2 ↦ v7`,
  `a7 ↦ slot v8`) inside the `BStmt` program (`AExec.rB`), so `a2` keeps the scratch base.
- Renames for importing `Arr2Code`/`SortMerge*` together with `Pipe`: Pipe's `BExp` is now `ByteExp`,
  `minE` is `minN` (no other change to the old files).

### Tests (300 random cases each incl. `[]`, length 1, all-equal, sorted lists; QEMU == Sail == model)

The harness now passes a real scratch slot (`a2`, 0x66-filled) and a per-case 256-byte stack (`sp` at a
random misalignment, 0x77-filled) and sets `gp`; it checks `a1 = |result|`, `gp` restored, no scratch write
beyond `sspace`, no stack write outside the 64-byte frame, no output write beyond `space`. All 36 examples
pass 300/300: old 11 (`sort` 446 words with the merge sort, `twosort` 1144), and `len sum8 sumNat countLt
count7 any3 allRange has5 empty head last get3 findBig min max idxZero idx42 evens ascii unpad suffix
prefixRev filtmap filtsort countBig`.

## What the language needs next (target: SHA-256 of a byte list)

SHA-256 = pad the message, split into 64-byte blocks, for each block: 64-word message schedule, 64 rounds
over 8 working words with the constant table `K`, add into the 8-word state; output 32 bytes big-endian.
Against the current stack (`AExp`/`AStmt`/`compileA`, `Pipe`):

**Expression language / code generator**
1. *Cheap constants.* `genConst` emits up to 2 words per bit (65 words for `0xffffffff`, 129 for a 64-bit
   constant). SHA needs ~100 32-bit constants and many shift amounts. Needed: `addi t, x0, imm12`
   (symbolic immediate) and `lui`+`addi` (+ `slli` for 64-bit) with step lemmas; then `genConst ≤ 2` words
   for 32-bit values.
2. *32-bit arithmetic.* Either W-instructions (`addw`, `subw`, `sllw`, `srlw`, and Zbb `rorw`/`roriw` if the
   `Cfg` enables it) with step lemmas and a lemma "low 32 bits of the sign-extended result = the `BitVec 32`
   operation", or 64-bit ops plus a 2-word zero-extension (`slli 32; srli 32`), which needs
   immediate-shift step lemmas (`slli`/`srli` with any shamt; today only `slli t, t, 1`).
   New `Op`s: `add32`, `rotr32 n`, `shr32 n`, `not` (or xor with a cheap `-1`).
3. *Expression temporaries.* A round computes `h + Σ1(e) + Ch(e,f,g) + K[i] + W[i]` and `Σ0(a) + Maj(a,b,c)`;
   with rotates as shift pairs this exceeds depth 6 unless split into assignments, which costs variables.
   Needed: spilling in `gen8`, or let-bound temporaries in statements.

**Statement language**
4. *More variables.* 8 working words + block pointer + round counter + 2–3 bases + temporaries ≥ 14 live
   values; there are 8 variables. Needed: spill slots / stack frame (the `Arr2` work on `main`), or the
   working words kept in a memory block (needs item 5 to be cheap).
5. *Word loads and stores.* `AStmt` has byte `load`/`store` only. Needed: `lwu`/`sw` (and `ld`/`sd`) on
   blocks, with `Rel` relating 4 (8) block bytes to a word (little-endian; a lemma like `unle_leN` of
   `Encode.lean`), and the big-endian variant for message words and the digest (4 byte loads + shifts work
   today but cost ~40 words per word read with current constants).
6. *Long loops.* `beq` reaches ±4 KiB = 1023 words; one SHA round is larger than that today and still
   several hundred words with items 1–2; the per-block loop contains the schedule loop and the round loop.
   Needed: `bne` over `jal` for loop exits (the `jal` step lemma with symbolic offset exists; its reach is
   ±1 MiB) and the matching `AStmt.wf` bound.
7. *A constant table.* `K[0..63]` indexed by the round counter. Options: (a) a read-only data block in the
   calling convention (changes `Implements`: one more region with given contents), (b) data words placed
   after the code and addressed PC-relative (`auipc` step lemma; loads from the code region — `codeAt` gives
   the bytes), (c) fill a scratch table at run time from immediates (64 × ~8 words with item 1). (b) keeps
   the spec unchanged.
8. *A scratch block in `bv`.* The schedule `W[0..63]` (256 bytes) and the padded last block(s) (≤ 128 bytes)
   need writable memory other than the output; `Pipe` cannot use `scratch` today (no free base register).
   Solved by item 4.
9. *Conditional statements* are still absent; padding can be done branch-free (`ite` selects among message
   byte, `0x80`, `0`, length byte), but a guarded load must stay in bounds, so an `if` statement or a copy
   of the tail into scratch is simpler.

**Source-level proof library**
10. `BitVec 32` vs low half of `BitVec 64`: `setWidth 32` commutes with `+ - &&& ||| ^^^`, shifts and
    rotates as shift pairs (`BitVec.rotateRight` unfolded), without `bv_decide`.
11. Words ↔ bytes: big-endian 4-byte and 8-byte encodings of block contents (`List UInt8` ↔
    `Vector (BitVec 32) 16`), `set`/`get` on word-indexed blocks expressed over the byte list.
12. A loop rule for *fixed-trip loops with array state* (`for i in [a, b)`, invariant indexed by `i`):
    `loopV_exec` in `PipeSrc.lean` is that rule for one counter; the schedule needs "block cells `< i` hold
    `f` of earlier cells" (the pointwise-`getElem?` invariant style used in `matLoop_exec`/`rev_exec` fits).
13. The reference function as plain Lean: `pad`, `chunks 64`, `schedule : Vector (BitVec 32) 16 → Vector
    (BitVec 32) 64`, `round`, `compress`, `sha256 xs = (chunks (pad xs)).foldl compress H0`, checked against
    published vectors by `decide`/`#eval`; `pad` length lemma (`64 ∣ |pad xs|`).

**`Pipe`/frontend level**
14. SHA-256 is not a per-byte map or fold. The DSL needs: (a) `chunks k` views with a per-chunk step,
    (b) fold accumulators that are fixed-size word tuples/vectors (in memory), (c) a stage whose step is
    itself a small first-order program (bounded `for` loops over `Fin n`, `Vector.ofFn`-style array
    definitions with recurrences, tuple updates), i.e. a second, statement-like IR under `Pipe` with its own
    reifier (`Fin.foldl`, `Vector.ofFn`, `let`), (d) output encodings for word vectors (big-endian),
    (e) a padding stage (`append` of a computed suffix), which also needs length-increasing stages:
    today every stage has `len ≤` input and `Pipe.space` relies on it only through `need`.
15. Intermediate steps that exercise the same features at smaller size: CRC-32 (items 1, 2, 5, 7; byte fold
    with a 32-bit accumulator and a 256-entry table — a `foldW` step with a table lookup), `count`/`min`/
    `max` (already expressible as `fold`/`foldW` with `ite`; `Option` result encoding missing), `filter`
    (needs an output index different from the input index: one more variable, which exists).
