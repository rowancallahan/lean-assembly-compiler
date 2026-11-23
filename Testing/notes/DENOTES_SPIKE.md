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
* H1 (`Testing/denotes_spike/Bridge.lean`): br_add (core `UInt64.ofNat_add`), br_wrap, br_lit (`rfl`, instance
  `@UInt64.instOfNat n`), br_ite_t/f (`rfl`), Nat add recursion (`rfl`) all proved on 4.35.0-rc3. Exported with
  lean4export @ v4.35.0-rc3 (3.1.0); `con-leche bridge.ndjson` → `accepted 458 declarations (--verified)` in 0.23 s
  (the closure includes `UInt64.ofNat_add`, `Nat.mod/div`, `f._f`). Rejection was not tested (not shown discriminating).
  The beta-redex SURVIVES elaboration in a theorem type (`(fun y => y + y) x`), so `let` → redex works.
  The pp.all shapes match nano's emitted spelling (`@HAdd.hAdd UInt64 UInt64 UInt64 (instHAdd UInt64 instAddUInt64)`,
  `ite R (@Eq Bool Bool.true Bool.true) (instDecidableEqBool ..)`).
  Surprise: `f = fun n x => Nat.casesOn n x (fun k => f k (x+1))` for a structural fuel loop is NOT accepted by `rfl`
  in the elaborator; `funext n x; cases n <;> rfl` works. So per-def theorems should be stated pointwise
  (`∀ n x, f n x = ...`, or `f 0 x = ..` / `f (n+1) x = ..`), which also fits transfer with binders.
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

## 9. S1 overnight (bridge prelude, UInt64 + Nat) — branch `keep_round1_denotes-s1`
File: `Testing/denotes_spike/BridgeU64.lean`, core Lean only, checked with Lean 4.35.0-rc3 (`lean BridgeU64.lean`, 0 errors,
no `sorry`; axioms in `#print axioms` at the end: only `propext`, `Quot.sound` (+ `Classical.choice` for `br_beq64`)).
* **Lean theorems (all proved)**, `ofNat` form with Nat binders, `2^64` as the literal: `br_add br_mul br_wrap br_sub br_and br_or
  br_shl br_shr` (sub is `ofNat (a + (2^64*b - b))`, no `%`; shl is `ofNat (a <<< (b % 64))`; shr is `ofNat ((a % 2^64) >>> (b % 64))`),
  `br_beq64` (`ofNat a == ofNat b = Nat.beq (a % 2^64) (b % 2^64)`), `br_lt64` (`ite R (ofNat a < ofNat b) (UInt64.decLt ..) t e =
  cond (Nat.ble (a % 2^64 + 1) (b % 2^64)) t e`), Nat-fuel twins `br_beqN`, `br_ltN`, `br_ite_cond/t/f`, `br_cond_t/f`, `br_lit`, `br_litN`.
  Nat recursion: add, sub (+pred), mul, `Nat.beq`, `Nat.ble`, shifts, and `br_mod` / `br_div` / `br_land_rec` / `br_lor_rec` (the
  last four are the only non-`rfl` ones; `%`, `/`, `&&&`, `|||` have no structural equations, so each is stated as a
  one-step unfolding `cond (Nat.ble m n) (cond (Nat.beq m 0) ..) ..` that a strong induction on `n` can use).
  `xor` is not emitted by nano and is not covered.
* **Set-level lemmas (all proved)** in `namespace SetLevel`, style of `add_u64` but ABSTRACT over `app : V → V → V` (structure
  `NatEqs`, hypothesis structures `NatRec`, `BitRec`, `U64Rec`; each field is the set-level image of one theorem above, at
  canonical numerals `nat k`): `nat_add nat_mul nat_sub nat_beq nat_ble nat_mod nat_div nat_shl nat_shr nat_land nat_lor`,
  `of_mod` (from `br_wrap`: `OF n = OF (n % 2^64)`), and for UInt64 `u64_add u64_sub u64_mul u64_and u64_or u64_shl u64_shr
  u64_beq u64_lt` (`⟦op⟧ (u x) (u y) = u (x op y)`, `⟦==⟧ = bl (x == y)`, `⟦ite lt⟧ .. t e = if x < y then t else e`).
  Not done: set-level lemma for the Nat-fuel `br_beqN`/`br_ltN` (same shape as `u64_beq/u64_lt`, no `mod`), `ite_bool` re-proved.
* **NOT done: export + con-leche acceptance.** `mcp__claude-code-remote__add_repo dwijayuda/con-leche` was DENIED by the auto-mode
  classifier ("Unauthorized Access"), so I had no con-leche checkout, no lean4export, and did not work around it. Consequences:
  (1) `lean4export`/`con-leche` never ran on `BridgeU64.lean`; acceptance is untested (the closure now includes `Nat.mod/div`,
  `Nat.bitwise`/`Nat.land`, `Nat.shiftLeft/Right`, `UInt64.ofNat_*`, `Nat.strongRecOn`, `Bool`-related `decide` machinery; the set-level
  section drags in `Nat.strongRecOn`, so export only the `br_*` names plus what they use, not `SetLevel`, when testing).
  (2) The set-level lemmas are not tied to con-leche's `SetTheory`: `NatEqs.app` is a free function. Porting = instantiate `app`
  with `SetTheory.app` and discharge each field by `transfer0/1` from the stored theorem of the same name; hypotheses are only at
  canonical numerals, which is weaker than `add_u64`'s `∀ x : V` and so is what `transfer` can give.
* Things the lead should know: `br_mod/div/land/lor` and `br_shl/shr` need `%`/`/` set-level evaluation, so the Nat prelude is
  larger than the spike's estimate (~25 Nat theorems beyond the 7 ops). `BEq`/`<` need the `% 2^64` normalisation because the
  theorem binders are plain `Nat`; the alternative (a hypothesis `a < 2^64` binder) needs multi-binder transfer.
* Environment: `~/.elan` was missing; installed via elan-init (network OK). Use `~/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lean`
  directly (elan default toolchain is none; the repo's `lean-toolchain` is 4.34.1).
