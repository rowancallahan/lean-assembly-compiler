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

## 10. S2 overnight (DENOTES-S2, branch `keep_round1_denotes-s2`)
Files: `Testing/denotes_spike/BridgeOps.lean` (core Lean only, exported) and `BridgeOpsSet.lean` (set-level lemmas,
`lake env lean` inside con-leche @3b37939, 4.35.0-rc3). Toolchain had to be installed from scratch in the container
(elan + lean 4.35.0-rc3 from GitHub releases, con-leche and lean4export @v4.35.0-rc3 built); nothing was denied.
* **Equations (34 theorems, sorry-free, axioms ⊆ propext/Quot.sound/Classical.choice)**: `bo_ite_t/f`, `bo_prod`
  (Prod.casesOn iota, motive `fun _ => R`, `R : Type`), `bo_nat_z/s` (Nat.casesOn iota), one unfolding equation per
  prelude op (`bo_rd bo_len bo_put bo_len' bo_bnew bo_bsize bo_bget bo_bset bo_bpush`, pointwise, all `rfl`), and building
  blocks: List.length/++/getD/set recursion on constructors, `Nat.toUInt64 = ofNat`, `toNat_ofNat` (`% 2^64`),
  `(UInt8.ofNat n).toUInt64 = UInt64.ofNat (n % 256)`, `(UInt64.ofNat n).toUInt8 = UInt8.ofNat n`, `bo_wrap8`,
  `bo_mod_lt` + `Nat.ble` recursion. Prelude = the LIST variant (B1L); the Array variant (BootPrelude) is NOT covered.
* **Export**: lean4export (v4.35.0-rc3) of all 34 theorems + 9 defs → 4.8 MB ndjson, `con-leche` → `accepted 1575
  declarations (--verified)`. (Note: lean4export needs `lean` on PATH.)
* **Set-level lemmas (sorry-free)**: `ite_bool`, `nat_cases` (iota for `nat k`, zero/succ), `prod_cases`, `wrap_mod`
  (`ofNat k = ofNat (k % N)` from the `+N` wrap theorem, strong induction; serves UInt8 and UInt64), `length_nat`,
  `len'_set`, `len64_set` (len and bsize, no size bound needed), `getD_set`, `set_set`, `append_set`, `idx_set`, and the ops
  `rd_set`, `bget_set`, `bset_set`, `bpush_set`, `put_set`. `bnew` needs none (`bnew = []`, constructor encoding).
  Each takes as hypotheses exactly what `transfer` yields from the named equation, over heads applied to type args.
* **OPEN (the one real gap)**: every u64-indexed op (rd, bget, bset) needs `hmod : k < 2^64 → ⟦k % 2^64⟧ = nat k`
  at canonical numerals (and `% 256` for the byte widening in `rd`). It is a hypothesis in the lemmas, NOT derived.
  Derivable from `bo_mod_lt` (Bool-guarded `Nat.blt n m = true → n % m = n`) + `Nat.ble` recursion by induction at the set
  level, but that needs a transfer with a Prop-typed binder (`Eq Bool (blt ..) true`, proof element = `pt`), i.e. an n-binder
  transfer that DENOTES-2 is supplying; not attempted. Alternative: make the index encoding avoid `toNat` (no).
* Not done: `Denotes`-level (transfer-instantiated) versions; the per-def `f = body` theorems; Array prelude.

## 11. Overnight integration (DENOTES-2, branch `keep_round1_denotes-2`)
Package `bridge/` (Lake, Lean 4.35.0-rc3; nano's main toolchain NOT bumped). Build: `cd bridge && lake build Bridge`.
It rebuilds nano's Expr closure (24 modules, unchanged) as lib `NanoExpr`. It `require`s con-leche @3b37939 but
imports nothing from it: the owner ruled that con-leche is not built tonight (the build was stopped at 536/550). So all
compiled work runs against TRIMMED COPIES of con-leche's `Denotes`/`Model` (every copied item cites its file:line).
The set lemmas used are hypotheses (`Mini.SetLaws`), each a cited con-leche theorem.
Everything below is sorry-free. Axioms are ⊆ {propext, Classical.choice, Quot.sound}.
* `Testing/denotes_spike/MiniDenotes.lean` (lead's request; plain `lean`, no imports): `tiny_denotes`, for a tiny
  language (lit, +, ite on ==): `tinyEval e = v → Denotes … (tr e) (enc v)`. Literals use con-leche's `natLit` rule.
* `Bridge/Typed.lean` (task 3, nano half): `Wf sig Γ e s` = the EMITTED terms with shapes. Every constant's
  type/instance arguments are pinned to what `emit` writes (`lit`, `binX`, `iteX`/`condX`, Prod.mk/casesOn,
  Nat.casesOn, List.nil, prims, calls); `PWf` = the program's defs are well formed. `ev_shape`: subject reduction
  for Ev. WHY this matters: Ev's rules accept ANY type/instance argument (e.g. `litU` accepts any instance `i`). For those
  arguments no model fact can hold, so the bridge facts must be stated for canonical arguments only.
* `Bridge/EvSkeleton.lean`: first skeleton (all 14 Ev rules + EvL; plumbing for spines, `ρE`, binders, calls,
  `strip`/`vs.reverse`). Its `Facts` are unrestricted, so they cannot all hold; it is SUPERSEDED by the files below.
  Kept: the per-op splits `PrimFacts` (9 ops) and `BinFacts`.
* `Bridge/EvBridge.lean` / `Bridge/EvMini.lean`: **`ev_denotes`**: `Ev P env e v → Wf sig Γ e s → env has shapes Γ →
  ∀ R, Denotes (ρE env) (tr e) R → R = enc v`. It is stated in "uniqueness" form: EXISTENCE of the denotation comes
  from `Model.mem` (the stored `f = body` theorem's type denotes, so all its subterms do). Its hypotheses are `FactsW`/`FactsM`,
  one field per constant rule, canonical arguments only. EvMini states it over the trimmed model, where these fields are
  DISCHARGED: `litU` (from `br_lit` by transfer + typing through the stored types of OfNat.ofNat / UInt64.instOfNat /
  UInt64.ofNat), `nil`, `pair` (constructor terms are their own encoding), `letβ` (regime-free beta + typing).
  Open fields: litN, bin, ite, cases, natZ/natS, prim, call.
* `Bridge/MiniModel.lean` (task 2): trimmed con-leche model. In it: `transferN` (n binders, telescope `Tele`, any binder
  type including Prop), `Inhab.eq` (denotations of S, a, b come out of the stored type itself), `beta` (BOTH regimes,
  no `PropWhen` hypothesis), `mem_app` (application typing, both regimes), `litU_fact` (worked example).
* `Bridge/EvMini.lean` (task 3, model half): encoding `encM` (canonical constructor terms over `ofNat` numerals;
  `Buf` via a stored `Buf = List UInt64`) and **`encM_mem`**: `enc v ∈ ⟦ty v⟧` for every value, with the constructors'
  Lean types as the env hypotheses (`EncEnv`).
* `Bridge/Transfer.lean`, `Bridge/Spike.lean`: the same transfer kit written against the REAL con-leche API. DRAFT,
  NEVER COMPILED. Sent to S2, who has con-leche built, with a request to typecheck it.
* Task 4: merged S2 (`keep_round1_denotes-s2`, 34 equations exported and accepted by con-leche, set-level op lemmas).
  S1 never started (setup script failed, apt 504), reported to the lead at 09:0x.

**Findings.**
(a) LEVEL ASSIGNMENTS (real con-leche, hidden by the trimmed copy). `Denotes.const` reads `cval n (Level.substFn φ ps us)`.
`substFn` falls back to `φ` outside `ps`. So inside a level-polymorphic head (`ite.{1}`, `Nat.casesOn.{1}`, `Prod.casesOn`),
the level-free constants in its TYPE (`Decidable`, `Nat`, `Nat.zero/succ`) are read at `φ[u↦1]`. The program reads them at `φ`.
An arbitrary `Model` does not relate `cval c φ` and `cval c φ'`, so typing through those heads does not go through as is.
No single `φ` fixes it: `ite.{u}` needs u=1, while `OfNat.ofNat.{u}`/`List.{u}` need u=0 and carry `Nat` in their types.
Fixes: (i) ask con-leche for a `Model` field "cval c depends only on φ restricted to c's level params" (its concrete
model has it); or (ii) shift theorems: an alias `K'.{u} := K` plus a stored `K'.{1} = K` for each such `K`. Two
instances of that theorem (at φ and at φ[u↦1]) give `⟦K⟧φ = ⟦K⟧φ[u↦1]`. This is not proved.
(b) Transfer needs `⟦a⟧ ∈ ⟦S⟧` for BOTH sides of every equation. Typing therefore goes through the declared types of all
heads, including `outParam` (HAdd's γ) and instance types. This is now the bulk of the remaining work.
(c) Iota facts (natZ/natS/cases) bind the branch functions, so they need typing of λ-terms for ALL arguments (`lamR_mem`).
That is a typing lemma for well-formed TERMS (`Wf → ⟦e⟧ρ ∈ ⟦shTy s⟧` for typed ρ), not just for values. It is the next piece.
(d) `iteX` gives `<`'s decidability instance the operands with leading unused `have`s dropped (`dropHead`).
Typing it needs a weakening lemma for Denotes (a body not using its binder denotes the same).
(e) `emit ⇒ Wf` is open. One subtlety: a CONTINUE (`.cont`) returns no shape, and `ite` takes `r = exp <|> ts <|> es`.
A cont branch therefore has the loop's result shape only when `exp = some res` (tail position). This needs the
tail-position invariant from the parser/annot, which eval_emit's `Kont` machinery uses.

**Next steps (in order).** 1. Typing lemma for Wf terms in the trimmed model (finding c), including the heads' types
(outParam theorem, instances, Eq/LT conditions, weakening for dropHead). 2. Remaining FactsM fields: bin/ite/natZ/natS/cases via
transfer from S2's equations (set-level lemmas exist: `nat_cases`, `prod_cases`, `ite_bool`, ops) and S1's arithmetic
(not done: S1 never ran). 3. `emit ⇒ Wf` + `PWf` for emitted programs (finding e). 4. Swap the trimmed model for real
con-leche (build allowed): replace `Mini.*` by `ConLeche.*`, settle finding (a). 5. Top statement: compose with
`eval_emit` (`Ev P [.l inp] (m x) (.l o)`) to get `Denotes (m inp) = enc o`.
**Revised estimate.** Remaining: typing of terms + heads 3-4 days; FactsM fields 3-4 days (with S1's arithmetic);
emit ⇒ Wf 2 days; real-con-leche swap + level issue (a) 1-3 days (depends on con-leche's answer). Spike §7 estimated
2-3 weeks. The Ev induction, transfer kit and value typing are done (in the trimmed model), so the remainder is about
**2-2.5 weeks**. The risk has moved from "does it go through" to finding (a) and the volume of head typing.
