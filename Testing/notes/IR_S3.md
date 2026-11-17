# IR stage S3, first increment: one typed source calculus, proved once (branch ir-s3, 2026-11-16/17)

Design: `Testing/notes/S3_CALCULUS.md` (external review). This round builds the calculus, proves its compiler once
through the shared IR, and recompiles 14 existing functions from five old front ends verbatim through it, plus one
function that needs two features at once.

## 1. The calculus (`Compiler/S3/Syntax.lean`)

- **Types** `Ty`: `w` (64-bit word: `UInt64`, `Int64`, `UInt8` zero-extended), `b` (`Bool`), `d i` (datatype `i` of
  the signature: constructors with word / Bool / datatype fields, no function fields). Lists, pairs, `Option`,
  structures and user inductives are all datatypes (monomorphic: `List UInt64` and `List UInt8` are two datatypes).
- **Signature** `Sig`: datatypes (per constructor the field types) and functions (parameter types, result type).
- **Expressions** `Expr S Γ τ`, typed by construction (typed de Bruijn `Var Γ τ`), A-normal form: `var`, `lit`,
  `blit`, `bin` (`Prim`: the 11 `Op`s, `mul`, `udiv`, `urem`, with Lean's `UInt64` meaning, `x / 0 = 0`), `cmp`
  (`eq ne ult ule slt sle`), `bnot`, `let_`, `ite` (on a `Bool`), `mk` (constructor), `cas` (exhaustive match, one
  arm per constructor binding its fields; arms as `Alts`), `call` (fully applied named function).
- **Programs** `Prog`: signature, one body per function (`Bodies`), `main` (a byte list `d 0` to a byte list).
- **Meaning**: `Ev P env e v`, big-step, into universal values `V` (`w x` / `c j fs`), no pointers, registers,
  allocation or fuel; deterministic (`Ev.det`); a program on bytes `Prog.run` (input as `bytesV`, output `bytesOut`),
  the `Program` instance. `⟦τ⟧` is `Ty.den` (a datatype stands for its universal value; the user's Lean types meet
  the calculus through `Enc`, below).
- **Well-foundedness slot**: `WfCert P` (a measure `μ` on calls decreasing along `Reaches`, the calls an evaluation
  reaches; general enough for tuple measures and mutual recursion). Not needed by any theorem yet: the compiler
  theorem takes the meaning as given, and the bridge gets termination from the Lean function's own (functional
  induction). Decision (noted): keep the slot, fill it when the front end becomes a pure function (exported terms).

Deviation from the review, decided: `eval` is the relation `Ev` (plus `Prog.run` by `Classical.choose`, sound by
`Ev.det`), not a total function: a total `eval` needs the WF certificate AND typing of values; the relation needs
neither and is all the compiler theorem uses.

## 2. The theorem (`Compiler/S3/Lower*.lean`, `Riscv/Back/S3Top.lean`)

- **Lowering** `lowerP : Prog → Ir.Prog VReg` (`Compiler/S3/Lower.lean`) through structured code (`SC`/`TC`,
  `mkFunc`): a constructor value is a fresh block `[tag, fields…]` (`alloc` + `st`), `cas` reads the tag and the
  fields (`ld`) and dispatches by a chain of tag tests, calls are IR calls; IR function `|fns|` is the wrapper
  `main`: the input bytes become a byte list (`inLoop`), the S3 `main` is called, the result list is written out
  (`outLoop`).
- **Simulation** `low_ok` (`LowerOk.lean`): every derivation `Ev P env e v` is a run `SC.Ex` of `low e`, writing only
  registers `≥ n`, growing memory (`Grow`), leaving `Rep m' v (g' n)` (`Rep`: a word, or a pointer to a live block
  holding the tag and the fields' representations). By induction on the derivation; calls through `fn_returns`.
- `lower_meaning` (`LowerMain.lean`): `P.Den input v → bytesOut v = some out → (lowerP P).meaning input = some out`.
- **`S3.compile_correct : CompileCorrect riscv S3.compile`**, **`S3.compile_runs : CompileRuns riscv S3.compile`**
  (`Riscv/Back/S3Top.lean`), `S3.compile P := if Accepted P then Ir.compile (lowerP P) else none`, proved once for
  every S3 program by composing `lower_meaning` with `Ir.machine_run` (the proof of `ir_compile_correct`).
  `Accepted P`: datatypes with < 2^32 constructors / fields, a one-parameter `main`. Axioms: exactly the Sail set.
  The out-of-memory flag is exact (`memoryNeeded` is the IR run's peak, as for `IndIr`).

## 3. The bridge and the front end (`Compiler/S3/Cert.lean`, `Compiler/S3/Front.lean`)

- `Enc α` (Lean value ↔ `V`, `dec ∘ enc = id`): instances for words, `Bool`, `Unit`, lists, pairs, `Option`,
  `ExceptT`; `s3_enc I` generates one for any inductive (with the simp lemmas).
- `evalO S φ env e`: evaluation of ONE body with calls answered by the oracle `φ` (structural, `simp` runs it);
  `CallsOk`; `evalO_sound`; `Good P φ f vs := Ev P vs (body f) (φ f vs)`; `good_intro`.
  `computes_of_main`: the certificate of `main` gives `Computes P main id id`.
- **`s3_compile N := main`** (metaprogram, untrusted): reads `f.eq_def` of `main` and of everything it calls
  (kernel terms after elaboration and match compilation), monomorphises and specialises (type, instance and
  function arguments are static: `@NonTail.filter UInt8 (· > 3)` is one S3 function; non-recursive functions whose
  function arguments capture run-time variables, e.g. monad binds and continuations, are inlined; `do` join points
  are substituted), unfolds matchers / `_sparseCasesOn` / class projections of instances, translates `casesOn` /
  recursors used as `casesOn` to `cas`, structure projections to one-arm `cas`, `if`/`dite`/`cond`/`&&`/`||` to
  `ite`, ANF-converts, and generates text: `N.S`, `N.b<k>`, `N.P`, the oracle `N.φ`, per function `N.cert<k>`
  (`∀ x, Good P φ k [enc x]`, by the Lean function's functional induction + the tactic `s3_solve`: simp with the
  oracle evaluator, case splits on stuck values `s3_split`, wildcard contradictions `s3_contra`, hypothesis
  normal forms `s3_norm` / `s3_hyps`), `N.computes : Computes N.P main id id`, `N.correct` (the machine theorem).
  A wrong translation fails its certificate: the front end is not trusted.

## 4. What goes through S3 (`Riscv/Frontx/S3Examples.lean`), QEMU + Sail

Each entry: the function under test verbatim (imported from the old example file), `main = encodeOut ∘ f ∘
decodeIn` with the byte formats of `Riscv/Frontx/S3IO.lean` (harness, compiled through S3 too), certificates,
`computes`, `correct` (exactly the Sail axioms). Tests: `Testing/asm/emit_s3.lean` (words, 50 cases, IR interpreter
== Lean on all 750 cases), `python3 Testing/asm/ir_test.py check 50 s3_<name>`: QEMU == Sail == Lean at
`memoryNeeded`, out-of-memory flag at `memoryNeeded - 1`, writes only in output + work.

| entry | function (verbatim) | old front end | words | QEMU+Sail |
|---|---|---|---|---|
| s3_mirror | `BinTree.mirror` | inductive | 859 | 50 × 2 ok |
| s3_graft | `BinTree.graftLeft` | inductive | 850 | 50 × 2 ok |
| s3_posplus | `Pos.plus` | inductive | 606 | 50 × 2 ok |
| s3_eqtree | `eqBinTree` (`[BEq α]`, two-tree match, wildcard) | inductive | 718 | 50 × 2 ok |
| s3_tailrev | `Tail.reverse` (+ helper) | inductive / list | 1233 | 50 × 2 ok |
| s3_nontailrev | `NonTail.reverse` (`++`) | inductive / list | 1299 | 50 × 2 ok |
| s3_filter | `filterGt3` = `NonTail.filter (· > 3)` | list + higher-order | 278 | 50 × 2 ok |
| s3_append | `append` (`List.append`) | list | 554 | 50 × 2 ok |
| s3_swap | `swap` (pairs) | data | 1219 | 50 × 2 ok |
| s3_weekend | `Weekday.isWeekend` (wildcard) | inductive (enum) | 570 | 50 × 2 ok |
| s3_replacex | `replaceX` (structure update) | structure | 1260 | 50 × 2 ok |
| s3_fromoption | `fromOption` | structure / option | 1124 | 50 × 2 ok |
| s3_small | `MythicalCreature.small` | structure | 343 | 50 × 2 ok |
| s3_find | `EarlyReturn.List.find?` (`do`, `return`, `failure` in `Option`) | monad + higher-order | 433 | 50 × 2 ok |
| s3_pttree | `sumPts : BinTree (PPoint UInt64) → PPoint UInt64` | **inductive + structure** (new) | 1282 | 50 × 2 ok |

**Composition example**: `sumPts` (and `toPts`) — a recursive function over an inductive whose payload is a
structure, returning a structure; the inductive path (`frontx_ind`) has no structures, the structure paths no
recursive inductives. It compiles, certifies and runs like the others.

## 5. Decisions (taken without asking, per the round prompt)

- Meaning as a relation (`Ev`) + `Prog.run` by choice; the WF slot is a structure `WfCert`, unused for now.
- Untyped universal values `V` under typed syntax: the lowering proof needs no value typing; ill-typed values make
  `Ev` stuck (no derivation), never wrong.
- I/O through byte lists: the only IR-level code beyond expressions is two loops (input bytes → list, list →
  output bytes); decoders/encoders are ordinary Lean functions compiled through S3, so nothing type-specific is
  proved at the IR level. Each example's theorem is about its `main` on raw bytes (`Computes P main id id`); `main`
  is the displayed composition. Tree inputs use a postorder stack format with byte payloads (`decTGo`).
- Certificates by the Lean function's functional induction (`f.induct`), oracle `φ` = the Lean functions; the
  certificate is stated as `Good` so recursive calls close by `assumption` and calls of earlier functions by
  their certificates (callees certified first; mutual recursion between functions rejected for now).
- Equation lemmas split nested matches, so the certificate unfolds the Lean function once with `f.eq_def`.
- `Sig.dt`/`fld`/`fn` are reducible (a reducible `lget`) so the types of generated programs compute by `whnfR`.

## 6. Test results

All 15 entries, `python3 Testing/asm/ir_test.py check 50 s3_<name>` (QEMU and the Sail C emulator):

```
s3_mirror: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 190; 859 words; memoryNeeded 632..59992 bytes)
s3_graft: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 284; 850 words; memoryNeeded 1896..128080 bytes)
s3_posplus: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 68; 606 words; memoryNeeded 1784..9464 bytes)
s3_eqtree: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 284; 718 words; memoryNeeded 872..49000 bytes)
s3_filter: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 22; 278 words; memoryNeeded 224..2336 bytes)
s3_append: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 59; 554 words; memoryNeeded 480..4680 bytes)
s3_tailrev: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 64; 1233 words; memoryNeeded 464..5760 bytes)
s3_weekend: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 1; 570 words; memoryNeeded 192..288 bytes)
s3_swap: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 32; 1219 words; memoryNeeded 1808..2568 bytes)
s3_nontailrev: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 64; 1299 words; memoryNeeded 464..6496 bytes)
s3_small: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 1; 343 words; memoryNeeded 192..296 bytes)
s3_find: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 22; 433 words; memoryNeeded 296..1240 bytes)
s3_fromoption: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 24; 1124 words; memoryNeeded 536..2024 bytes)
s3_replacex: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 56; 1260 words; memoryNeeded 2104..4088 bytes)
s3_pttree: 50 cases x 2 ok (QEMU == Sail == Lean at memoryNeeded, flag a0 = -1 at memoryNeeded - 1, writes only in output + work; input lengths up to 190; 1282 words; memoryNeeded 1344..32936 bytes)
```

The IR interpreter's output equals Lean's `main` on all 750 cases (`emit_s3.lean`).

## 7. What the calculus / front end still lacks (next)

- `Nat` (and `String`, arrays): most existing examples use `Nat`; needs a bounded representation with the bound in
  the statement (ROADMAP "unbounded Nat": arguments/hypotheses, bounded types, or fuel) or big numbers.
- `UInt8`/`UInt16`/`UInt32` arithmetic (masking after each op); `Int64` division; shifts by non-literal amounts are
  supported, `Int64` comparisons too.
- Mutual recursion between functions (the WF slot is ready; the front end certifies callees first).
- `ExceptT` over `Option` with `throw` (`Desugared.List.find?`): translates, one certificate does not close yet.
- At most 7 parameters per function (the IR back end's calls).
- Functions as run-time values (closures that escape): only static function arguments and inlined continuations.
- Front end as a pure function `exported kernel terms → Prog` (the metaprogram reads kernel terms already; the
  next step removes MetaM), then self-hosting it.
- Migration next: Wa (word arrays: a block type with `ld`/`st` at an index), paged arrays, the list path's `Tree`
  loops as tail calls (`jmp`), then switch `frontx_ind` entries one at a time; optimisation (IR passes) applies to
  all of them at once.

## 8. Final check

`bash Testing/scripts/check.sh`: ALL CHECKS PASSED (34 min, after merging origin/main at b07a0b9). The statement-fingerprint
step prints its usual WARNING (warning-only; not re-frozen, per the round rules).
