# DENOTES spike: can Ev be bridged to con-leche's `Denotes`? (2-hour spike, 2026-11-23)

Con-leche checked out at `dwijayuda/con-leche` @ 3b37939 (Lean 4.35.0-rc3). Lean file:
`Testing/denotes_spike/DenotesSpike.lean`, checked with `lake env lean` inside the con-leche checkout. Every theorem
listed as proved below is sorry-free; `#print axioms` = `propext, Classical.choice, Quot.sound`.

## 1. The one fact that shapes everything
`model_exists` gives `Nonempty (Model V env)`: an ARBITRARY model. A `Model` says only three things about constants:
`mem` (each stored constant is in what its type denotes), `false_empty`, `eq_equality` (`⟦@Eq A a b⟧ = eqv ⟦a⟧ ⟦b⟧`).
Nothing ties `cval UInt64.add` to the definition of `UInt64.add`. (The concrete model inside the proof does
(`EnvModelM.defn_reads`), but `model_exists` does not export it.)
So "what does `UInt64.add a b` denote" has only one answer: whatever the Eq-THEOREMS stored in the env force.
There is no intrinsic "real value" set. The encoding of values has to be defined relative to the model, as the
denotation of canonical constructor terms.

## 2. The tricks (all proved in the Lean file unless marked)
* **Transfer** (`transfer0`, `transfer1`): a stored theorem `∀ x : T, @Eq S a b` gives `⟦a⟧[x] = ⟦b⟧[x]` for every
  `x ∈ ⟦T⟧`. Proof: `mem` puts the theorem's `cval` in `piR r ⟦T⟧ B` (either regime, so the binder annotation does
  not matter, `fibre_inhabited`), so each fibre `B x = eqv ⟦a⟧ ⟦b⟧` is inhabited. The side conditions are what
  `eq_equality` asks: `⟦S⟧ ∈ univ u`, `⟦a⟧, ⟦b⟧ ∈ ⟦S⟧`.
  Consequence: EVERY Ev rule that is not a constructor needs a Lean theorem in the exported env, stated in exactly
  the Expr shape nano emits (same instances, same `OfNat.ofNat` spelling).
* **Canonical encoding**: `nat k = ⟦succ^k zero⟧`; `Denotes_lit`: `lit k` denotes `nat k` (con-leche's own
  `natLit` rule unfolds literals to `Nat.succ (lit (k-1))`). UInt64: `u64 x = ⟦UInt64.ofNat⟧ (nat x.toNat)`; the
  `Fin` bound proof never appears (alternatively proofs denote `pt`, so `⟦UInt64.ofBitVec (BitVec.ofFin ⟨n, h⟩)⟧`
  works too, no bound argument needed). Bool: `⟦Bool.true⟧/⟦Bool.false⟧`. Lists: `⟦List.cons T a l⟧`, pairs
  `⟦Prod.mk A B a b⟧`.
* **Constructors are free**: `List.cons`, `List.nil`, `Prod.mk`, `Bool.true` need NO theorem. The encoding is
  their denotation (`list` in the file).
* **UInt64.add** (`add_u64`, proved at the set level): from `br_add : UInt64.ofNat a + UInt64.ofNat b =
  UInt64.ofNat (a + b)`, `br_wrap : UInt64.ofNat (n + 2^64) = UInt64.ofNat n` and the two `Nat.add` recursion
  theorems (`n + 0 = n`, `n + succ m = succ (n + m)`), `⟦+⟧ (u64 x) (u64 y) = u64 (x + y)` for all x, y.
  The pattern for every arithmetic constant: one or two `ofNat` theorems + Nat recursion equations by induction.
  Comparisons go the same way through `Nat.beq`/`Nat.ble` equations. No injectivity or `False` reasoning needed.
* **ite** (`ite_bool`): `ite R (true = true) (instDecidableEqBool true true) t e = t` and the `false` twin (both
  `rfl`). Ev already knows the condition's Bool, so the instantiated term matches one of the two theorems.
  The condition term `Eq Bool (BEq.beq ..) true` itself needs no theorem: `eq_equality` reads it directly.
* **`let` must become a beta-redex**: `Denotes` has NO `letE` rule (con-leche's annotation pass zeta-expands stored
  lets). Translate nano's `have x := v; b` to `(fun x => b) v`; `Denotes_beta` computes it (graph regime,
  `⟦v⟧ ∈ ⟦T⟧`). Whether Lean keeps the redex in an elaborated theorem TYPE is being checked (helper 1, see §5).
* **Program defs** (`Denotes_call`, one argument shown): `⟦f⟧` is opaque, so each def needs a stored theorem
  `f = λ xs. body` (nano's emitted body, Lean proves it by `rfl`; for fuel loops the `Nat.casesOn` form). Then
  `f a` denotes the body at `push ⟦a⟧ ρ`, which is Ev's `call` rule (`strip` + `vs.reverse`).
  `Nat.casesOn` needs the two iota theorems (`rfl`), quantified over the motive at `Type`.

## 3. The induction for the slice (sketch, NOT proved)
Statement, for a fixed accepted `env` that holds the bridge theorems (§4) and the per-def theorems:
```
∀ M : Model V env, Ev P vs e v → Denotes M.cval env φ (enc ∘ vs) (tr e) (enc v)  ∧  enc v ∈ ⟦ty v⟧
```
by induction on the `Ev` derivation (not on `X`). Each Ev rule is one lemma: `bv` → `Denotes.bvar`; `lt` →
`Denotes_beta`; `litU/litN` → `Denotes_lit` + `br_lit`; `bin` → the op's transfer lemma; `iteT/F` → `ite_bool`;
`mk`, `nil` → constructor, free; `cases` (Prod.casesOn) → its iota theorem + beta twice; `natZ/natS` → casesOn
iota + `nat` inversion; `prim` → one theorem per prelude op; `call` → `Denotes_call` (n arguments).
The second conjunct (typing) is needed because every transfer asks `⟦a⟧ ∈ ⟦S⟧`. It comes from `mem` on the head
constant plus `app_mem_piR`; the piece that needs real work is computing `⟦type of head⟧` applied to type arguments
(e.g. `HAdd.hAdd : ∀ α β γ, HAdd α β γ → α → β → γ` at `UInt64`), i.e. a small typing-soundness lemma for the slice.
Also needed: `regime φ m.pw ≠ 0` for every data `λ` the env stores. That reads the checker's `PropWhen` annotation;
it is decidable on the concrete stored term.

**Decision: do not rewrite Ev to mirror Denotes.** Ev's rules are spine patterns (one rule per constant
application), and each maps to one bridge lemma; the induction on Ev is direct. A Denotes-shaped Ev (graphs,
compositional `app`) would break `eval_emit` and buy nothing. Keep Ev. Small changes only: `lt` must be emitted as
the redex (or translated by `tr`).
**Decision: emitting con-leche's own Expr type is not worth it.** con-leche's `Expr` carries a computed hash field
(`implemented_by`) and `BinderMeta` (the `PropWhen` annotation that the CHECKER computes, nano cannot emit it
correctly without re-implementing the annotation pass). `tr : X → ConLeche.Expr` is a 10-line structural map;
the only real content is `pw`, and it should be read from the stored env (the theorem `f = body` as stored), not
produced by nano. The identity check "nano's X = Lean's Expr" stays on Lean's Expr (existing C_lean tooling).

## 4. What the env must contain (the "bridge prelude", a Lean file exported once)
* per UInt64 op (7 `H*` ops, `<`, `==`): an `ofNat` theorem, `br_wrap`-style overflow theorem where needed;
* Nat: `add/sub/beq/ble` recursion theorems (all `rfl` / core lemmas); `br_lit` (`OfNat.ofNat` = `ofNat`);
* `ite` true/false, `Prod.casesOn` iota, `Nat.casesOn` iota (2);
* per prelude op (`rd len put len' bnew bsize bget bset bpush`): one equation each;
* per program def: `f = <emitted body>` by `rfl` (generated by nano's emitter, like ExprLeanC.defs).
Estimate ~60 small theorems plus one per def. All of these are ordinary Lean facts; the risk is only con-leche
ACCEPTING the exported file (§5).

## 5. Open items checked by helpers (filled in below when they report)
* H1: Lean-side theorems on 4.35 + lean4export + con-leche accept: _pending_
* H2: nano's Expr files on 4.35.0-rc3: ExprSpec, Correct and EvalEmit closures (24 modules, none needs Sail)
  build UNCHANGED on 4.35.0-rc3, 0 errors, 1m10s. Only warnings: deprecated `if_pos/if_neg/if_true/if_false`
  (192 rename hints) and unused simp args. Rest of the repo (Sail/Arm/Codegen/SelfHost) not tested.

## 6. Toolchain: copy Denotes vs bump
* Copy `Denotes.lean` into nano (4.34.1): it imports con-leche's `Kernel.Core` (`Expr` with computed fields,
  `Env`, `ConstantInfo`, `Level`, `PropWhen`), `Verify.Level`, `SetModel.Ops`, `SetTheory.*`. A verbatim copy is
  not one file; it is a large slice of con-leche's kernel. And the Model we need comes from `model_exists`, which
  needs ALL of con-leche. So copying does not give us the theorem, only the statement.
* Recommended: a separate Lake package `bridge/` on con-leche's toolchain that `require`s con-leche and nano
  (con-leche itself does exactly this for `bridge/lean4lean-model`), with nano bumped to 4.35 if H2 says the port is
  cheap; otherwise keep nano on 4.34.1 and let the bridge package import only the toolchain-neutral pieces
  (`ExprSpec`, `Correct`) rebuilt on 4.35.

## 7. Effort estimate for the full bridge
| piece | estimate |
|---|---|
| transfer lemmas for n binders + automation (a tactic that instantiates a stored theorem) | 1-2 days |
| typing-soundness for the slice (`enc v ∈ ⟦ty⟧`, heads' types applied) | 2-3 days |
| bridge prelude: ~60 Lean theorems + their set-level lemmas (pattern of `add_u64`) | 2-3 days |
| export + con-leche acceptance of prelude + C's own defs (incl. `f = body` rfl proofs at scale) | 1-2 days, risk |
| Ev induction (14 rules) + `call` for n args + `strip`/`vs.reverse` bookkeeping | 2 days |
| toolchain/package setup | 0.5-2 days (H2) |
Total: about 2-3 weeks of focused work. Nothing found is a blocker in principle; the biggest risks are con-leche
performance/acceptance on the generated `f = body` theorems for C (236 defs) and the `PropWhen` regime facts.

## 8. Notes
* One auto-mode classifier denial in this session (a `lake build` command with `export PATH=...`); the same build
  run with the full `~/.elan/bin/lake` path was allowed. Nothing else was blocked.
* Option worth asking con-leche for: a `Model` field `defn : ∀ stored definition c, cval c = ⟦c.value⟧` (the proof
  already has it as `defn_reads`). It would remove all per-def `f = body` theorems.
