# EXPR: Expr side channel (round 1: design, results, proof)

Goal: tie nano's meaning to Lean's. For every def, nano emits the Lean `Expr` its AST means; a spot check compares it
with Lean's elaborated `Expr`; a proof (`eval (emit a) = Sem a`) plus the compiler theorem then says: the machine code
computes the meaning of the matched Lean `Expr`.

## 0. Final report (round 1)
**What exists**
* `emitSpec` (`Nano/Expr/ExprSpec.lean`): a reference emitter from the parsed AST (ParSpec `DefA`) plus token side info
  (`let` form, `[]`/`bnew`) to the Lean `Expr` fragment `X`, serialized as `S`. It is pure and total, and it
  CHECKS every typing and slot fact the proof uses (operand and argument shapes, binder widths, fresh `let` slots,
  branch shapes, def ids, distinct names).
* E (`Nano/Expr/Emit.lean`, 184 defs in nano's bootstrap subset): the same emitter as a nano program. It is
  compiled by the committed self-compiled C (`B2.bin`, QEMU) to a 311 KB RISC-V binary. C itself is unchanged.
* `eval_emit` (`Nano/Expr/Correct.lean`, proved, standard axioms): for any program whose Exprs `emitAll`
  produces, every output nano's `Sem` computes is the big-step meaning `Ev` of the emitted Expr of `m` applied to the
  input. `Ev` reads each fragment constant with its Lean meaning (UInt64 ops, `ite`/`decide`, `Prod`, `Nat.casesOn`,
  the prelude).

**Self-check results** (`check_E.sh`, `spot_check.sh`)
| set | defs | nano Expr = Lean Expr | not equal | E.bin = emitSpec |
|---|---|---|---|---|
| C's source | 236 | **234** | 2 representation-only (`o32`, `o38`, below) | 236/236 |
| E's own source | 184 | **184** | 0 | 184/184 |
| examples (8 programs) | 19 | 19 | 0 | 19/19 |
| fuzz seed 1 (300 programs; 34 rejected by nano) | 939 | 785 | 69 literal-typing, 85 Lean rejects | 939/939 (+34 rejections) |
| fuzz seed 2 (300 programs; 37 rejected by nano) | 908 | 730 | 81 literal-typing, 97 Lean rejects | — |
* `o32`, `o38`: `let k := (if .. then 1 else 0)` (o32) and `let k := (if 1048575 < p then 1 .. else 0)` (o38).
  Lean types `k` as Nat, nano as UInt64. The only use of `k` is `if k == 1` with k ∈ {0,1}, so no value can differ.
  `Cert.sem_C` (kernel-checked against the Lean defs, where `k` is Nat) already covers them. Nat step 1 (§7) makes
  these two match exactly.
* Lean rejects (fuzz only): programs nano accepts and Lean does not (`let t := []`, `put [] (35 <<< 51)`). These are
  invariant-1 violations. They are recorded for SYNTAX-EXP (parser owner); repros are in `Testing/nano/expr/repro_*.src`.

**What the theorems say for C**
* `ExprSpec.C_expr` (`Nano/Expr/CExpr.lean`, built locally, standard axioms): `emitAll` succeeds on C's certified
  AST `Cert.PC.all` (`decide +kernel`, 10 s; emitSpec is structurally recursive so the kernel can evaluate it), and
  for every input on which C's meaning has a result, `mC inp` is the meaning `Ev` of C's emitted Expr of `m`.
* `NanoMain.self_expr_C` (`Nano/Expr/CExprTop.lean`; it imports the RISC-V model, so it is built only on the runner,
  slot-6 request pending): for every `SelfIn` input, C's RISC-V code writes `mC a`, and `mC a` is that Expr's meaning. That Expr text equals
Lean's elaborated Expr on 234/236 defs (an executable check; the 2 others differ only as above). The theorem does not
yet say "equals Lean's Expr": that link is the spot check, which is a test and not a proof (§6, step 3).

## 1. The Expr fragment `X`
Lean's `Expr` restricted to: `bvar i`, `const n ls` (levels: closed numerals only), `app`, `lam` (binder type, body),
`forallE` (types only), `letE` (type, value, body, `nondep` flag), `lit (natVal k)`, `sort` (types only).
Not in `X`: `fvar`, `mvar`, `mdata`, `proj`, string literals, level params; binder infos are all `default`.
Constants used by nano's source subset (observed on C's own source, 236 defs): the types `UInt64 Nat Bool UInt8 Buf
List Prod`; `OfNat.ofNat` + `UInt64.instOfNat` / `instOfNatNat`; the seven `H*` ops with their fixed instances
(`HAdd.hAdd UInt64 UInt64 UInt64 (instHAdd UInt64 instAddUInt64)`, `instHAndOfAndOp`, `instHShiftLeftOfShiftLeft`, ...);
`ite`, `LT.lt`/`UInt64.decLt`, `Eq Bool (BEq.beq ..) true`/`instDecidableEqBool`; `Prod.mk`, `Prod.casesOn`,
`Nat.casesOn`, `List.nil`; the prelude (`rd len put len' bnew bsize bget bset bpush`) and the program's own defs.

How nano constructs map (the emitter produces exactly this):
| nano (ParSpec `Nd`) | Expr |
|---|---|
| def `f (a : A) .. : R := b` | type `∀ A .., R`; value `λ A .., b` |
| fuel loop `f : Nat → S.. → R \| 0, xs => Z \| n+1, ys => S` | `λ Nat S.., Nat.casesOn (λ Nat, R) #k Z (λ Nat, S)` |
| `CONTINUE e` (tail self-call) | `f #n s..` (input re-inserted, flat PAIR split by the state count) |
| `let x := v; b` | `have T v b` (Lean 4.34 elaborates `let` in these bodies as non-dependent `letE`) |
| `let (a, b) := v; b` | `Prod.casesOn A B (λ A×B, R) v (λ A, λ B, b)` |
| `if a == b` / `if a < b` | `ite R (Eq Bool (BEq.beq ..) true) (instDecidableEqBool ..)` / `ite R (LT.lt ..) (UInt64.decLt ..)` |
| (`<` only) | `UInt64.decLt`'s copies of the operands lose their LEADING unused `have`s (Lean's instance term; found by fuzz) |
| literal k at type T | `OfNat.ofNat T (lit k) (inst T k)`, T = UInt64, or Nat for a fuel argument |
| slot `loc s w` | `bvar` of the binder that owns slot s |

Types come from the def headers (`DefI`) and are inferred bottom-up for `let` / `ite` / tuple nodes.

## 2. Serialization `S`
One line per def: `D <name> <type> <value>`, prefix tokens separated by one space:
`#i` bvar · `c N` or `c N.{l1,..}` const · `@ f a` app · `\ T b` lam · `> T b` forall · `h T v b` / `= T v b` let
(non-dependent / dependent) · `n<k>` nat literal · `s <l>` sort. No binder names. Names are `Name.toString` (the
fragment's names need no escaping; the Lean side asserts the shape). The format is a plain byte stream, so nano can
write it with `put`. Comparison = byte equality per line.

## 3. Normalization (Lean side only; minimal, every step listed)
Lean's value of def `f` is read as:
* N1 recursive defs (the fuel loops): the RHS of Lean's own unfolding equation `f.eq_def`, λ-abstracted over its
  binders, instead of the compiled `Nat.brecOn` value (`getUnfoldEqnFor? f (nonRec := false)`).
* N2 every matcher application (`isMatcher`: the `match_i` helpers of `| 0 / | n+1` and `let (a, b)`) is
  delta-unfolded; N3 then β-normalize (`Core.betaReduce`): the source subset has no λ, so every redex comes from N2.
* N4 binder names dropped (S has none: de Bruijn only); binder infos asserted `default`. `instantiateMVars` first.
Instance terms are kept EXACTLY (no erasure): they are fixed per operator and type, so the emitter writes them.
Nothing else is normalized: `have`/`let` flag, universe levels, literal types are compared as they are.

## 4. Where the emitter lives (self-hosting)
* Round 1: a second nano program `E` (the Expr emitter) = C's lexer + parser defs (the same text as C, unchanged)
  + emitter defs `x*` + its own `m`: `m x = emit (s10 x) (y16 (s10 x))`. Its body walk reads y16's IR words
  (= `serialize p`, by the parser refinement); a token-level side scan gives what IR erases: def names, header types,
  `let x` vs `let (a, b)` and `[]` vs `bnew` (the IR's pre-order = the source order of `let`/atoms).
  E's source is Lean defs in the bootstrap subset (`Nano/Expr/Emit.lean`, like `Nano/Lexer/Lex2.lean`), extracted to
  text like `build_self_S.py`. E is compiled by C (B2, RISC-V / native ARM); C itself does not change in round 1,
  so `selfhost_gate.sh` passes unchanged, and E is self-hosted in the sense of the invariant (subset, compiled by C).
* E's own text goes through the spot check too (nano's Expr of E = Lean's Expr of E).
* Round 2 (proposal, a proven step): fold E into C as a side output (mode byte), regenerate B2/B3/Cert/SrcLink/GA_arm.
* Reference model: `emitSpec` in plain Lean (`Nano/Expr/ExprSpec.lean`) over `refParse`'s `DefA`/`DefI` plus the
  side info; tests check E's bytes = `ser (emitSpec ..)`; the proof (§6) is about `emitSpec`.

### E as built (round 1)
`Nano/Expr/Emit.lean` (~60 defs `e0..e99`, worklist machine: no recursion in the subset) + `EmitStr.lean` (phrase
table, generated by `gen_emitstr.py`). Pass 1 per def walks the IR forward with a stack: node ends, inferred shapes,
side flags (token cursors for `let`/`[]`). Pass 2 pops 4-word items (phrase, type, node, bvar, literal, ident) and
expands nodes in output order. `build_E.py` writes E's text (C's Chain + Lex2 + Par1 text, EmitStr, Emit, `m x = e99 x`).
Output is S-compact: the long fixed phrases (`gen_emitstr.ABBREV`) are written ` !<id>`, and `expand.py` restores S
(a table lookup, unproven glue like the shim). Reason: nano's `put` shares the 2^19 capacity κ. C's S text is 856 KB,
its compact form is 251 KB. When C grows past about 2x, E needs a def-range selector.
Subset rule met on the way: the first `List UInt8` parameter is the program INPUT, so every output-writing def
takes the input `x` first (as C's own defs do).
`check_E.sh`: B2 (QEMU) compiles E's text to E.bin (311 KB), then expand(E.bin output) = `emitSpec` byte for byte on:
C's source (236 defs), E's own text (184), examples (19), fuzz seed 1 (939 defs + 34 rejections).
Spot check of E's own text: 184/184 defs = Lean's Expr EXACTLY (no literal-typing case in E). E as Lean defs
(`emit_lean.lean`) agrees on the examples and 60 fuzz programs.

## 5. The check (`Testing/nano/expr/`)
`lean_side.sh SRC OUT`: elaborates `import Lean` + `Nano/Main/Prelude.lean` + SRC, writes N1-N4 normal forms in S.
`run_check.sh`: emitter output vs Lean side, per def: exact-match count and a category per mismatch
(literal typing, let form, matcher shape, other). Targets: C's source, E's source, `v2self/examples`, fuzz programs.

Results (2026-11-21, `spot_check.sh`; emitter = `emitSpec`, the nano port of E is next):
| set | defs | exact match | literal-typing | Lean rejects | other |
|---|---|---|---|---|---|
| C's source (`self_S_input.txt`) | 236 | 234 | 2 (`o32`, `o38`) | 0 | 0 |
| examples (8 programs) | 19 | 19 | 0 | 0 | 0 |
| fuzz seed 1 (300 programs, 34 rejected by nano) | 939 | 785 | 69 | 85 | 0 |
| fuzz seed 2 (300 programs, 37 rejected by nano) | 908 | 730 | 81 | 97 | 0 |
Mismatch categories:
* literal-typing: a literal-only subterm (`let k := (if .. then 1 else 0)`, `if 3 < 5`, `let t := 7; ..`) gets type
  Nat in Lean, UInt64 in nano. The values agree here (small, compared with literals), but the Expr differs, so nothing
  is claimed for these defs. Fix options: nano rejects literal-only lets/comparisons, or C's source spells `k1`/`k0`.
* lean-rejects: nano (ParSpec, so C) ACCEPTS, Lean REJECTS: invariant 1 violations. Main forms: `let t := []` (Lean
  cannot infer the element type), a shift with literal operands `put [] (35 <<< 51)` (`<<<` is not `binop%`, the
  operands default to Nat), a literal-only value later used as UInt64. Repros: `def m (x : List UInt8) : List UInt8 := let t := []; put [] 1`, `.. := put [] (35 <<< 51)`.
  To fix in the parser (reject), a proven step on C.

Lean-side cost: Lean's `eq_def` for a fuel loop with many states and a big body can take minutes (E's first `e55`, with 15
parameters, did not finish). E keeps its loop bodies small: the per-def work is the non-recursive `e58`.

## 6. Proof (status)
DONE: `Nano/Expr/Correct.lean`. Big-step `Ev`; the relations `R` (value ↔ Sem's flat words), `ArgsR`, `EnvR`
(binders ↔ slots); Sem inversions. `node_ok`: induction over all node kinds, where a loop's CONTINUE becomes the self call
via `Hyp.kont`. `fuelLoop_ok`: induction on the fuel. `def_ok`, `prog_inv`, and `eval_emit`.
Also `Nano/Expr/Eval.lean`: a fuel-bounded executable evaluator `evalX`, with guards. Adequacy (`Ev` → `evalX`) is not proved yet.
The original plan:
1. `evalX : X → env → Option Val` for the fragment: a closed table of the constants above (each with its Lean
   meaning), user defs by name, `Nat.casesOn` on the fuel (structural, so `evalX` is total with fuel).
2. `eval_emit : evalX (emitSpec p) = Sem κC p` (by induction on `Nd`, slot env ↔ de Bruijn env).
3. Per matched def a kernel-checked equation `f xs = evalX ..` (Frontx-style, generated), or a reflection lemma.
4. With `compiler_correct`: the machine code of a text computes the meaning of the matched Lean `Expr`.
No `Spec/` change is needed for round 1. Proposed (owner approval): a `Spec/Expr.lean` stating step 4.

## 7. Nat feature (owner: option 2, big-number Nat in the back end; DESIGN, not implemented)
### Where Nat occurs in Lean's elaborated Expr (S counts from lean_side.sh)
| use | C (236 defs) | E (184) | fuzz seed 1 (939) | Nat operations | bound today |
|---|---|---|---|---|---|
| fuel parameter + `Nat.casesOn` (a loop) | 48 loops | 50 | 250 | casesOn = test 0 / predecessor | a word in nano: `Sem` keeps fuel as UInt64 |
| fuel literal (`OfNat Nat`, `instOfNatNat`) | 101 | 87 | ~400 | literal | ≤ 2^64−1 (8-byte numeral); max seen 2^30 in C/E |
| `len' x` (fuel argument) | 9 | 9 | 186 | `List.length` | ≤ 2^20 (input cap) |
| let-bound literal-only value (o32, o38) | 2 lets | 0 | (part of 69 literal-typing defs) | `==` with a literal | values in {0, 1} |
| Nat comparisons (`BEq Nat`, `Nat.decLt`) | 4 (o32/o38) | 0 | 96 `==`, 33 `<` | `==`, `<` | small literals |
| Nat arithmetic (`HAdd Nat` ..) | 0 | 0 | + 5, − 3, * 3, &&& 6, ||| 11, <<< 6, >>> 3 | `+ - * &&& ||| <<< >>>` | literal operands; `<<<` can exceed 2^64 (`35 <<< 51`) |
| `ite` at type Nat | 7 | 0 | 22 | — | — |
`/`, `%`, `toUInt64`/`ofNat` coercions: none in C, E or the fuzz sample (nano has no syntax for them yet).
Conclusion: in C and E, Nat values are fuel (≤ 2^30 literals, `len'`) and two {0,1} flags. Real Nat arithmetic shows
up only in fuzz programs, i.e. programs that nano accepts today with UInt64 meaning (`literal-typing`) or that Lean
rejects (`<<<`). With big Nat, nano types literal-only terms as Nat, exactly like Lean, and these cases turn into matches.

### Design
* Typing (front end): a literal-only subterm gets type Nat when there is no expected type, as in Lean's default
  instance rule (`let`, `if` comparands, binop operands). `Sh.nt` becomes a storable shape (lets, tuples, params).
  This is a ParSpec change, so it needs the owner's approval. The `<<<` with literal operands case (Lean rejects) stays rejected.
* Representation: a Nat value is ONE word. A tagged small value `2k+1` holds k < 2^63; otherwise it is a pointer to an
  immutable block `[len, limb0 .. limb(len-1)]` (little-endian 64-bit limbs, normalized: top limb ≠ 0) in the block
  model's bump area. Immutable, so aliasing is harmless and the ownership stage treats Nat like a word (no
  linearity). Fuel keeps its fast path: small values decrement in place.
* Operations (templates in Gen, each with a small/small fast path and a limb loop): `+`, truncated `-`, `*`, `/` and `%`
  (schoolbook, then Knuth D), `<`, `==`, `ofNat` (literal → small or block), `toUInt64` (low limb, `% 2^64`),
  `UInt64.toNat`, plus `&&& ||| ^^^ <<< >>>`, which Lean defines on Nat (bitwise on limbs).
* Sem: `W` gets `| n (x : Nat)`; prim/binop cases for Nat call Lean's `Nat` functions directly (`Nat.add`,
  `Nat.sub`, `Nat.div`, `Nat.land`, `Nat.shiftLeft`, ..). So `Sem` IS Lean's meaning, with no model of limbs. The fuel loop is
  `Nat.casesOn` on `.n`. The `Program` meaning is unchanged (bytes → bytes).
* Proof plan: one lemma per template, `limbs ⟦code⟧ = Nat.op a b` through `val : block → Nat` (the abstraction,
  `val [l0..] = Σ li·2^(64i)`) plus a heap-invariant `NatBlk` (blocks immutable, inside the bump area, below the
  allocation pointer). This is the Nat analogue of the UInt64 `binop` correspondence in `Sem` (the machine word op equals Lean's
  UInt64 op). The compiler theorem's simulation relation gets `W.n x ↦ word repr` with `val (repr) = x`.
  Allocation failure joins `.cap` (out of room), as buffers do today.
* Bootstrap subset and self-hosting: C itself needs no new Nat feature (only fuel and the {0,1} flags, which
  agree already, §5). Steps: (1) Sem + ParSpec typing (`.nt` storable, Nat literals by Lean's default rule),
  owner-approved; (2) Gen templates for small Nat (tagged words: `+ - < ==` with overflow → block), proved;
  (3) block limbs for `+ <`, RISC-V first; then `- * / %`, bitwise; ARM mirrors each step. Each step: regenerate
  B2/B3, Cert, SrcLink, GA_arm, and pass selfhost_gate.sh. The Nat runtime routines (limb loops) are written in
  the bootstrap subset as nano defs that Gen links in, so they self-host with C.
Recommendation: start with step (1) and then (2) with `+` and `<` on RISC-V, as the lead suggested. In C's source,
rewrite o32/o38 as `k1`/`k0` constants or leave them: after step (1) Lean and nano agree on their typing.

### Step 1 spec: Nat by Lean's default rule (owner-approved; HAND-OFF to SYNTAX-EXP, which owns the parser)
Scope (owner): literal-only terms are typed by Lean's rule. Nat is storable and comparable; Nat ARITHMETIC is
rejected until bignum lands. This REPLACES the "reject literal-only" rules of SYNTAX-EXP's literal-typing check
(keep_round1_syntax-1), so it is one parser change, not two.

**Lean's rule** (Lean 4.34.1 sources):
* A numeral `n` elaborates to `@OfNat.ofNat ?α n ?inst` with a fresh type metavariable. When ?α is still open at the
  end of elaboration, the default instance `instOfNatNat` (`@[default_instance 100]`, Init/Prelude.lean:1280) sets
  ?α := Nat. Defaulting runs LAST, so any later unification (anywhere in the def body) wins.
* `+ - * &&& |||` are `binop%` (Init/Notation.lean:302-309). The whole operator tree gets one "max type"
  (Lean/Elab/Extra.lean, `binop%` elaborator). A literal leaf takes the type of a typed leaf; if every leaf is a
  literal (or a still-open numeral), the tree stays at ?α and defaults to Nat.
* `<<< >>>` are plain `infixl` (Notation.lean:289-290), NOT `binop%`. With a UInt64 left operand they elaborate as
  in C (`HShiftLeft UInt64 UInt64 UInt64` via `instHShiftLeftOfShiftLeft`). With a literal left operand Lean fails
  (`35 <<< 51` at type UInt64: fuzz repro `repro_lean_rejects_shift.src`).
* `==` is `binrel_no_prop%` (394), `<` is `binrel%` (390): the operands get a common type. Two literal-only operands
  give Nat (`instDecidableEqNat`, `instLTNat`/`Nat.decLt`, as in o32).
* `let x := v`: v is elaborated with no expected type. If v is literal-only, x's type is the open ?α, and uses of x
  in the body can still fix it: `let t := 17709; rd x t` gives `t : UInt64` (Lean accepts), while
  `let k := (if .. then 1 else 0); if k == 1 ..` gives `k : Nat` (o32, o38). `if`/tuples pass the expected type down
  (`ite ?α`, `Prod.mk`); literal-only branches with no expected type stay open.

**Rule for nano (a CHECK added after typing; the IR, `Sem`, Gen and Own are unchanged)**
* Numeral classes: every let slot whose value has type `Ty.lit`, and every literal-only operator tree, comparison
  operand pair or `if`, is a class. Classes are merged by `binop%` trees, by `==`/`<` operand pairs, by `if` branches
  and by `let x := (class)`.
* A class is UInt64 if any member meets a UInt64 position: an operand of a binop/comparison with a UInt64 leaf, a
  UInt64 parameter or prim argument, a UInt64 result or tuple field, a shift's left operand. A class is Nat if it meets
  a fuel argument, and Nat by default otherwise. A class with both a UInt64 and a Nat demand is REJECTED (Lean fails).
* REJECTED as well: a Nat class used as a binop operand (Nat arithmetic: `1 + 2` with no UInt64 leaf, `let t := 7;
  .. t * 2 ..` with no UInt64 use), and a shift whose left operand is a numeral class. Nat comparisons (`==`, `<`) and
  Nat `let`/`if` are ACCEPTED. Their values are literals < 2^64 (8-byte numerals), so the word values agree with Lean's Nat.
* ParSpec change: a new per-def check `numOk : DefI list → DefA → Bool` (classes over the resolved `Nd`, with the
  defs' parameter shapes), called in `pDef` after the body parses (`none` on failure). Par1 (C's source) gets the same
  check, then ParRun/ParInv follow. C's own AST stays byte-identical (C has no Nat arithmetic); C's text changes, so B2/B3,
  Cert, SrcLink and GA_arm regenerate behind `selfhost_gate.sh`.

**emitSpec / E / proof (EXPR-1 side, after the parser change lands)**
* emitSpec: the same class pass per def (it already sees the resolved AST). A Nat-class `let` emits `h c Nat ..`,
  its literals `OfNat Nat .. instOfNatNat`; comparisons of Nat classes emit `BEq.beq Nat (instBEqOfDecidableEq Nat
  instDecidableEqNat)` / `LT.lt Nat instLTNat` + `Nat.decLt`; `ite` at Nat when no expected type. New shape `.nt` in
  let binders. E: the same pass in E's pass 1 (one class word per slot), plus 6 new phrases in `gen_emitstr.py`.
* Proof: `Ev`/`EvB` gain Nat comparisons on `.n` values; `R .nt` (value ↔ one word, `u.toNat = k`) already exists.
  `node_ok`'s ite/let cases get the Nat shape. `eval_emit`/`C_expr` must re-prove with no new hypotheses.

**Acceptance test**
* `spot_check.sh`: C **236/236** exact (o32, o38 now match), E 184/184, examples 19/19; fuzz **literal-typing → 0**:
  each former literal-typing def now matches or is rejected by nano. Lean-rejects falls to the `let t := []` class
  only (a separate SYNTAX-EXP item).
* `check_E.sh`: E.bin = emitSpec byte for byte on C, E, examples, fuzz. `eval_emit`/`C_expr` build with
  standard axioms. `selfhost_gate.sh` PASS. `regress_fuzz.py`: no regression except programs Lean rejects.
