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

### 10.1 S2 follow-up for DENOTES-2: stored-theorem shapes (`Testing/denotes_spike/BridgeStored.lean`)
All 10 theorems stated as requested, sorry-free (br_wrap uses propext only). lean4export → 1.0 MB, `con-leche` → `accepted 441 declarations (--verified)`.
pp.all shapes (as elaborated, `Nat.zero` stays `Nat.zero`, never `OfNat.ofNat 0`; `Nat.succ n` stays `Nat.succ n`, not `n+1`):
* `nat_z : ∀ (R:Type) (z:R) (s:Nat→R), @Eq.{1} R (@Nat.casesOn.{1} (fun (x:Nat) => R) Nat.zero z s) z`
* `nat_s : ∀ R z s (n:Nat), @Eq.{1} R (@Nat.casesOn.{1} (fun (x:Nat) => R) (Nat.succ n) z s) (s n)`
* `prod_c : ∀ (A B R:Type) (f:A→B→R) (a:A) (b:B), @Eq.{1} R (@Prod.casesOn.{1,0,0} A B (fun (x:Prod.{0,0} A B) => R) (@Prod.mk.{0,0} A B a b) f) (f a b)`
* `br_litN : ∀ n, @Eq.{1} Nat (@OfNat.ofNat.{0} Nat n (instOfNatNat n)) n`
* `add0 : ∀ n, @Eq.{1} Nat (@HAdd.hAdd.{0,0,0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n Nat.zero) n`; `addS` same head, RHS `Nat.succ (n + m)`.
* `outParam_eq : @Eq.{3} (Type 1) (outParam.{2} Type) Type`; `buf_eq : @Eq.{2} Type Buf (List.{0} UInt64)`. Both get Lean's automatic `@[defeq]` attribute (harmless; the proof is `rfl`). `Buf` is an `abbrev` (a `def` in the export).
* Motive lambda: non-dependent, binder name `x`, body = the bound variable `R` (a bvar under the λ), type `Nat` / `Prod.{0,0} A B`.
Stored TYPES in the export (level-param NAMES differ from what `#check` prints):
* `ite` : levelParams `[u]` (type `{α : Sort u} → (c:Prop) → [h : Decidable c] → α → α → α`).
* `Nat.casesOn` : `[u]`.  `Prod.casesOn` : `[u_1, u, v]` (motive level FIRST, then α's `u`, β's `v`; `#check` shows `u_1,u_2,u_3` but the stored names are these).
* `HAdd.hAdd` : `[u, v, w]` (γ : `outParam.{w+2} (Type w)`, so at `w=0` it is `outParam.{2} Type`, which `outParam_eq` rewrites).
* `OfNat.ofNat` : `[u]`.
* `instDecidableEqBool` : `[]`, a `def`, type is exactly `@DecidableEq.{1} Bool` (const `DecidableEq` applied to `Bool`, NOT unfolded to `(a b : Bool) → Decidable (a = b)`).

## 11. Overnight integration (DENOTES-2, branch `keep_round1_denotes-2`)
**Setup.** `bridge/` is a separate Lake package on 4.35.0-rc3. Build: `cd bridge && lake build Bridge BridgeC` (~4 min
from scratch). Nano's main toolchain is NOT bumped. The package rebuilds nano's Expr closure UNCHANGED from `../Nano`
(lib `NanoExpr`, 24 modules; lib `NanoC` adds C's emitted Expr `oC`). It `require`s con-leche @3b37939 but imports
none of it: the owner ruled that con-leche is not built tonight (the first build was stopped at 536/550). All compiled
proofs therefore run against a TRIMMED COPY of con-leche's `Denotes`/`Model` (`Bridge/MiniModel.lean`; each copied
item cites file:line). The set lemmas used are hypotheses (`Mini.SetLaws`), each a cited con-leche theorem.
The same kit written against the REAL con-leche API (`Bridge/Transfer.lean`) was compiled unchanged by DENOTES-S2 in
its con-leche checkout (cdc2cf8, merged). Everything listed below is sorry-free; axioms ⊆ {propext, Classical.choice, Quot.sound}.

**What is proved.**
* `Testing/denotes_spike/MiniDenotes.lean` (lead's request; plain `lean`): `tiny_denotes`, for lit/+/ite.
* Ev side (`Typed.lean`, `Check*.lean`). `Wf sig Γ e s` = the EMITTED terms with shapes: every constant's
  type/instance arguments are pinned to what `emit` writes. `ev_shape` is subject reduction.
  `Check.chk`/`pwfChk` is a decidable checker with soundness (`chk_sound`, `pwfChk_sound`). It accepts exSum/exPair,
  and **C's own emitted program (341 defs) is `PWf`, kernel-checked** (`CheckC.cPWf`, `decide +kernel`, 104 s).
  `CheckForm.cDefForm` also checks that every def value has the λ-chain form.
* The induction (`EvMini.lean`): `ev_denotes`: `Ev P env e v → Wf → env shaped → ∀ R, Denotes (ρE env) (tr e) R →
  R = enc v` (uniqueness form; existence comes from `Model.mem`). One `FactsM` field per constant rule.
* Transfer kit (`MiniModel.lean`): `transferN` (n binders, any binder type including Prop), `Inhab.eq`/`eq_ex` (the
  denotations of S, a, b come out of the stored type), `beta` (BOTH regimes, no `PropWhen` hypothesis), `mem_app`.
* Typing (task 3): `EvMini.encM_mem` (`enc v ∈ ⟦ty v⟧` for every value, `Buf` via a stored `Buf = List UInt64`).
  `TermTyping.wf_mem` gives typing soundness for well-formed TERMS (λ branches typed at all arguments, by `lamR_mem`).
  Per-head typings come through the declared Lean types (`HeadTyping`, `Iota2`, `Add`, `Call`), including `outParam`.
* Discharged fields: ALL of them. Each comes by transfer from named stored theorems plus typing:
  `litU`, `litN` (`br_litN`), `nil`/`pair`, `letβ` (beta), `natZ`/`natS`, `cases` (`prod_c`), `call` (stored `f =
  <emitted λ-value>`). All 7 `.bin` ops: `+` (Add), `-`/`*` (Arith: `sub_*`, `mul_*`, `br_sub` guarded, `br_mul`),
  `<<<`/`>>>` (Shift: `pow_*`, guarded `mod_char`/`div_char`, `br_shl`, `br_shr`), and `&&&`/`|||` (Bits: `land_z/r`,
  `lor_z/r` bit recursions by strong induction, `br_and`, `br_or`). Ites: UInt64 `==` (Ite), UInt64 `<` (IteLt,
  guarded `ite_lt_t/f`), Nat `==` (IteNat, `br_nbeq`). All 9 prelude ops: Len, Push, Index, Bytes.
* `Wf.ite` now requires `iteOk n cmp a b` (any `==`, or `<` on UInt64 operands with `dropHead = id`). The kernel check
  of C (`cPWf`) re-ran and passes, so every ite in C has this form. Finding (e) is thereby avoided rather than
  solved: Nat `<` and the `dropHead`-affected `<` are rejected by `Wf` (they occur in 0 places in C).
* **Headline: `TopC.C_denotes_full`, NO open fields.** For every model (trimmed `Model` + `SetLaws`) of an `env` with
  `Final9.Env9` (prelude typings + the ~70 stored equations + C's 341 `f = value` defs) and `br_litN`:
  `Sem κC C inp = .ok (mC inp) → inp.length < 2^64 → ⟦m⟧ (enc inp) = enc (mC inp)`.
  Axioms: propext, Classical.choice, Quot.sound. The chain is `C_denotes_final{,3..9}`, each dropping fields of the
  previous `Open`. `Final9.open9_all` shows the last `Open9` holds outright. `Top.sem_denotes` gives the same for any
  emitted program under its `Open`. With `self_expr_C` (CExprTop, needs Sail) this reaches C's RISC-V code.
* Stored-statement sanity check (`Bridge/StoredFacts.lean`): all 69 stored equations the
  `Env*` structures assume are stated in plain Lean (E-expression in a comment above each) and PROVED, core only, no
  sorry. So `Env9` is not vacuous for a sound checker. The translation E → Lean was done by eye (heads checked with
  `pp.explicit`). Acceptance by con-leche is checked only for S2's 10.
* Task 4: merged S2 three times. Its 34 equations and set lemmas came in; Transfer.lean compiled against real
  con-leche. §10.1 (BridgeStored): the 10 stored theorems I requested (nat_z/s, prod_c, br_litN, add0/S, outParam_eq,
  buf_eq, …) exported and ACCEPTED by con-leche (441 declarations, --verified). Their elaborated shapes and level-param
  order match the `HasTy` types the bridge assumes (checked by eye: `Prod.casesOn.{1,0,0}` motive first,
  `instDecidableEqBool : DecidableEq.{1} Bool` not unfolded, `Nat.zero`/`Nat.succ` kept).
  Merged S1 (§9, BridgeU64). It did run, but late; I never received its messages. Its `br_*` statements differ in form
  from the bridge's (e.g. `br_sub` without a guard), so the bridge does not use them directly. They are independent
  confirmation that the arithmetic facts hold.
* Late merges (the lead's 09:00–10:00 messages reached me at 11:13). S3 `MiniU64.lean` (UInt64 ops and ites),
  S4 `MiniBind.lean` (bvar, lam/beta, let, pairs, casesOn) and FABLE-MINI's `FableMini`, `Universe`, `MiniTyping` and
  `HeadTyping` are now in `Testing/denotes_spike/`. All are standalone over their own trimmed copies, and each one
  compiles with plain `lean` 4.35.0-rc3 here: 0 errors, no sorry. They overlap with the bridge (which already
  covers those features over the emitted Expr) and are NOT wired into it. Their value is FABLE-MINI's level results:
  `HeadTyping.head_has` and `Denotes.shift` under `CvalParams`.
* Finding (a), the way out: `bridge/Bridge/ModelExists2.lean` (DRAFT, NOT BUILT) proves `model_exists'`, which is
  `model_exists` plus `CvalParams M`. It is `congrArg` of con-leche's internal `EnvModel.acval_params` through
  `Model.ofEnvModelM`'s `cval := cvalOf m.base2.acval`, so no upstream change is needed, unless the Model/* def does
  not unfold from outside (the alternatives are in the file header). The **con-leche build was DENIED** by the
  session's permission classifier at ~11:15, so neither the draft nor the real-model swap could be checked.
**Findings.**
(a) LEVEL ASSIGNMENTS. Real con-leche has this problem; the trimmed copy hides it.
`Denotes.const` reads `cval n (Level.substFn φ ps us)`. `substFn` falls back to `φ` outside `ps`. So inside a
level-polymorphic head (`ite.{1}`, `Nat.casesOn.{1}`, `Prod.casesOn.{1,0,0}`), the level-free constants in its type
(`Decidable`, `Nat`, `Nat.zero/succ`) are read at `φ[u↦1]`, while the program reads them at `φ`. An arbitrary `Model`
does not relate the two. No single `φ` fixes it: `ite.{u}` needs u=1, but `OfNat.ofNat.{u}` needs u=0 and carries `Nat`
in its type. Two fixes: (i) a con-leche `Model` field "cval c depends only on φ restricted to c's level params"
(true of its concrete model); or (ii) per affected `K`, an alias `K'.{u} := K` plus a stored `K'.{1} = K`. Its two
instances (at φ and at φ[u↦1]) give `⟦K⟧φ = ⟦K⟧φ[u↦1]`. NOT PROVED; this is the main risk of the real-model swap.
(b) Transfer needs `⟦a⟧ ∈ ⟦S⟧` for both sides of every equation. Typing therefore goes through the declared types
of all heads, including `outParam` and instances. It is routine but voluminous (Add.lean is the template).
(c) Ev's rules accept ANY type/instance arguments, and for those no model fact holds. The bridge therefore needs `Wf`
(canonical arguments only).
(d) `emit ⇒ Wf` is FALSE in general. `emit` accepts a CONTINUE inside a `let` value (as an `ite` branch); Sem rejects
it at run time (`ev_let` needs `.inl`) and Lean would not typecheck it. So `Wf` is checked PER PROGRAM (`pwfChk`, done
for C).
(e) `iteX` gives `<`'s `decLt` the operands with leading unused `have`s dropped (`dropHead`). Typing that needs a
weakening lemma for Denotes. C has no such ite, and `Wf` now excludes them (see above). A program that has one needs the lemma.
(f) Facts for the exported prelude: iota and add theorems must be stated with `Nat.zero`/`Nat.succ`, not `0`/`n+1`.
`OfNat` literals need `br_litN`. Asked S2 to export the exact shapes and check acceptance (pending at the time of writing).

**What is open.** Everything below lies outside the trimmed-model theorem:
1. Real-model swap: `Mini.*` → `ConLeche.*`. It is mechanical (Transfer.lean already compiles there), but con-leche
   could not be built tonight (first by the owner's call, later the build was denied by the permission classifier).
   Finding (a), the level-assignment φ: the draft `model_exists'` (`CvalParams` from the internal `acval_params`)
   should settle it without an upstream change. It is unchecked until con-leche builds.
2. Export: the bridge prelude (types of ~40 heads), the ~70 stored equations and C's 341 `f = value` theorems must be
   written as a Lean file, exported, and ACCEPTED by con-leche (acceptance and performance are untested). Then
   `Env9` must be instantiated from the accepted env (`HasTy` by `decide` on the stored types). The stored statements'
   truth is checked in plain Lean (StoredFacts), not their acceptance.
3. `Sem` totality is a hypothesis (`hs`), as in the C pipeline.
**Next steps.** (1) Agree on finding (a) with the con-leche owner. (2) Build con-leche once and port the bridge:
replace `Mini.SetLaws` with the cited lemmas, keep the `HasTy` interface. (3) Generate the export file from the
`Env*` structures (the statements are already in E form) and run acceptance. (4) Instantiate `Env9` and state
`C_denotes` against con-leche's `Denotes`.
**Revised estimate.** About **1 week**: real-model swap 1-2 days plus finding (a) (1-3 days, depends on the owner's
answer); export, acceptance and `Env9` instantiation 2-3 days, with performance risk on 341 defs. The trimmed-model
side (induction, typing, all ops, ites, prelude, the per-program Wf check on C) is done. Spike §7 estimated 2-3 weeks
in total.

## 13. S6: port to the REAL con-leche definitions (DENOTES-S6, branch `keep_round1_denotes-s6`)
**Setup.** `~/.elan/bin/lake` did not exist in the S6 container; elan was installed there (default toolchain none; the
package's 4.35.0-rc3 is fetched on demand). `cd bridge && ~/.elan/bin/lake build BridgeReal` (new lib: `Bridge.Transfer`,
`Bridge.Real`) builds con-leche's `ConLeche.Denotes`/`SetModel.Ops` (≈40 jobs, ~2 min) and the ported file. No build command was refused.
Axioms of everything below: propext, Classical.choice, Quot.sound; no sorry.

| trimmed (`Mini.*`) | real | statement change |
|---|---|---|
| `D O cval ρ e v` | `Denotes cval env φ ρ e v` | gains `env` and the level assignment `φ` |
| `E.lit k` | `.lit (.natVal k)` | none |
| `natEnc M k` | `Real.natEnc M φ k` | takes `φ`; reads `cval natZeroName φ`/`natSuccName` (levelParams `[]`, so `substFn φ [] [] = φ` by `rfl`) |
| `lit_denotes` (no hypotheses) | `Real.lit_denotes M (H : NatConsts env) φ ρ k` | needs `NatConsts`: `Nat.zero`, `Nat.succ` found in `env` with `levelParams = []` (Mini had them free) |
| `mem_closed` (name+type list membership) | `Real.mem_closed M (h : env.find? n = some ci) (hT : Denotes … ci.toConstantVal.type Tv)` | `find?` instead of list membership; no `SetLaws` argument (real laws are theorems) |
| `natEnc_mem` (`LitEnv`) | `Real.natEnc_mem M (H : NatTypes env) φ ρ k` | `NatTypes` = `NatConsts` + `Nat` found, `Nat.zero : Nat`, `Nat.succ : Nat → Nat` with a binder meta `m` such that `regime φ m.pw ≠ 0` for all `φ` (Mini's `pw=false`) |
| `const` rule (`D.const`) | `Bridge.Denotes_const'` (Transfer, existing) | needs `find?`, `levelParams = ps`, `us.length = ps.length` |
| `app_inv`, `lam_inv`, `pi_inv` | `Bridge.app_inv/lam_inv/pi_inv` (Transfer) | none |
| `beta` (both regimes) | `Bridge.beta` (Transfer; uses `app_lam_any`, `Denotes_functional`) | `L : SetLaws` argument dropped; `m : BinderMeta` for `pw` |
| `mem_app`, `mem_app'` | `Bridge.mem_app` (Transfer) | `mem_app'` not ported (not needed: `Denotes_functional` + `mem_app`) |
| `D_functional` | `ConLeche.Denotes_functional` | none |
| `Inhab`, `Inhab.pi/eq/eq_ex`, `transferN` | `Bridge.Inhab…` (Transfer, existing) | `Inhab.eq` returns the existential form; `transferN` not in Transfer yet (only `Inhab.eq`) |

**Done:** lit/natLit, const, app, beta (the last three were already in Transfer.lean, compiled), `mem_closed`, `natEnc_mem`.

**Handed to DENOTES-3 (not mechanical): the u64 cases, starting with `litU_fact`.** Reason: finding (a), seen concretely.
In `OfNat.ofNat.{u}`'s stored type `∀ {α : Type u} (n : Nat) [OfNat α n], α` the constant `Nat` is denoted at
`φ' = substFn φ [u] [0] = φ[u↦0]`, while the program's `.const Nat []` is denoted at `φ`. `Denotes.const` yields
`cval Nat φ'` and `cval Nat φ`, and an arbitrary `Model` does not equate them. `OfNat` itself is fine
(`substFn φ' [u] [param u] = φ[u↦0]`). So `litU_fact` cannot be ported without the level-insensitivity fact (a)(i)
(`model_exists'`/`CvalParams`: `cval c φ` depends only on `φ` restricted to `c`'s level params). Once that is a hypothesis
`hφ : ∀ n ci φ₁ φ₂, env.find? n = some ci → (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) → M.cval n φ₁ = M.cval n φ₂`,
the port is the Mini proof with `substFn` rewriting at each `const` and `Level.eval` in the `sort` cases. No other
obstacle seen. The remaining u64 ops (`+ - * <<< >>> &&& |||`, ites) all go through the same `OfNat`/instance typings.
