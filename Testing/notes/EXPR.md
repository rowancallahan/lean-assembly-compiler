# EXPR: Expr side channel (round 1 design note)

Goal: tie nano's meaning to Lean's. For every def, nano emits the Lean `Expr` its AST means; a spot check compares it
with Lean's elaborated `Expr`; a proof (`eval (emit a) = Sem a`) plus the compiler theorem then says: the machine code
computes the meaning of the matched Lean `Expr`.

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

## 5. The check (`Testing/nano/expr/`)
`lean_side.sh SRC OUT`: elaborates `import Lean` + `Nano/Main/Prelude.lean` + SRC, writes N1-N4 normal forms in S.
`run_check.sh`: emitter output vs Lean side, per def: exact-match count and a category per mismatch
(literal typing, let form, matcher shape, other). Targets: C's source, E's source, `v2self/examples`, fuzz programs.

## 6. Proof plan
1. `evalX : X → env → Option Val` for the fragment: a closed table of the constants above (each with its Lean
   meaning), user defs by name, `Nat.casesOn` on the fuel (structural, so `evalX` is total with fuel).
2. `eval_emit : evalX (emitSpec p) = Sem κC p` (by induction on `Nd`, slot env ↔ de Bruijn env).
3. Per matched def a kernel-checked equation `f xs = evalX ..` (Frontx-style, generated), or a reflection lemma.
4. With `compiler_correct`: the machine code of a text computes the meaning of the matched Lean `Expr`.
No `Spec/` change is needed for round 1. Proposed (owner approval): a `Spec/Expr.lean` stating step 4.
