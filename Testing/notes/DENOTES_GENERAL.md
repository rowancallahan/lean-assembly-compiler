# DENOTES_GENERAL: scoping the ∀-program bridge theorem (DENOTES-3)

The per-feature theorems in `bridge/Bridge/Main.lean` cover one program each (`nano_tiny` … `nano_sub`). The
general theorem covers every emitted program. The Lean skeleton is `bridge/Bridge/General.lean`. It builds, uses
std axioms only, and has no `sorry`: each open piece is a named hypothesis.

## 1. The target statement

```lean
theorem general (V : Type w) [SetTheory V] (o : List (String × X × X))      -- any emitted program
    (accepted : Cached.checkDecls .verified pins ds = .ok env)                -- con-leche accepts the export
    (hgen : GenOk o ds = true)                                                -- the export is gen o (Bool, §3)
    : ∃ M : Model V env, CvalParams M ∧
      ∀ inp out, Ev (progOf o) [.l inp] mainX (.l out) →
        ∀ φ ρ, ∃ x, Denotes M.cval env φ ρ (encL inp) x ∧
          ∀ Y, Denotes M.cval env φ ρ (encL out) Y → Denotes M.cval env φ (push x ρ) (tr mainX) Y
```

The conclusion is the same as in `nano_input` and the per-step theorems, and it composes with `expr_rv` at `Ev`.
Every hypothesis is about the stream:
* con-leche's acceptance;
* one Bool `GenOk o ds` saying `ds` is the mechanical export of `o`: the prelude, a def plus an equation `n_eq` per
  emitted def, and the separators;
* `natPin ds` and `blocksOk ds` as today.

`GenOk` is computed by `#eval` on the parsed stream, as `recsOk*` is now. It is not kernel-reduced (§4, risk 1).

Skeleton status (`General.general`): the statement is proved from these hypotheses.
* `hsem`/`hthms`: `TabOk`/`EqsOk`/`ThmsOk` for the program's tables. These become consequences of `GenOk`.
* `hcases : Cases …`: the per-rule lemmas (§2).
* `hwf`: well-formedness of the emitted fragment at `mainX`.

Proved in the skeleton:
* the induction over `Ev`/`EvB`/`EvL` (`ev_R`);
* the last step from a conversion to the denotation (`final_of_conv`, generic over any `tab`/`eqs`/`thms`);
* the assembly (`general`);
* the `bv` case (`case_bv`, from typing of value encodings).

## 2. Proof plan: induction on `Ev`, one lemma per rule

Invariant `R env e r`: `Conv tab eqs thms [] (substD (env.map encV) 0 (tr e)) (encV r) (tyV r)`. That is, the emitted
term, with the environment's values substituted, converts in the model engine (`Conv`, sound by `conv_sound`) to the
value's encoding. The encodings are:
* `.w x` ↦ `UInt64.ofNat (lit x.toNat)`;
* `.n k` ↦ `lit k`;
* `.l bs` ↦ `encL bs`;
* `.p a b` ↦ `Prod.mk A B ⟦a⟧ ⟦b⟧`;
* `.b ws` ↦ open (the prelude's buffer type).

`EvB` uses `RB`: `decide c` converts to `Bool.true/false`. `EvL` is pointwise.

| `Ev` rule | lemma | status |
|---|---|---|
| `bv` | substitution reads the value, `Conv.refl` | **proved** (`case_bv`), given typing of encodings |
| `nil` | `refl` (`hty_nil`) | library has it for `NanoLDen.tab`; needs tab monotonicity |
| `litU`/`litN` | `lit64`, `br_litN` | library (step `arith`); needs `Wf`: the instance argument is canonical |
| `bin` `+ * -` | `br_add64`/`br_mul64`/`br_sub64` + `conv_add`/`conv_mul`/`conv_nsub` (induction on literals) | library (steps arith, sub) |
| `bin` `&&& \|\|\| <<< >>>` | prelude `br_and64` … + bitwise Nat on literals (`Nat.bitwise` / `shiftLeft` recursion) | new; S6 is doing `&&&`/`\|\|\|` |
| `iteT`/`iteF` + `EvB` | `ite` → `cond (decide c)`; `decide (a < b)` → `Nat.ble` (`ite_lt`, `conv_ble`); `==` → `Nat.beq` | `<` in library (step ite); `==` new (S6 step a) |
| `prim rd` | `rd` at any index: equations `rd (b :: l) (i+1) = rd l i` + `rd_cons0`/`rd_nil` | index 0 in library; general index new (S6 step e) |
| `prim len` / `len'` | `conv_len` | library (step len); `len'` (Nat) same shape |
| `prim put` | `put o v = o ++ [byte]`: append over `encL` by induction on `o` | `put []` in library; general `o` new |
| `prim bnew/bsize/bget/bset/bpush` | buffer prelude + encoding | new, the largest prim group |
| `call` | the stored `n_eq` (`Conv.inst`) at the argument encodings, then the IH on the callee body | engine has `inst`; needs `substB` = `substD` on λ-free bodies, **and λ support (below)** |
| `lt` (`let`) | β: `(λ x. b) v → b[v]` | **new Conv rule `beta`**, sound in BOTH regimes given `v ∈ ⟦T⟧` (`app pt _ = pt`; regime 0 forces `F v = pt`) |
| `mk` | congruence | library (`cong`) |
| `cases` (`Prod.casesOn`) | prelude iota `Prod.casesOn (Prod.mk a b) f = f a b`, then β twice, then IH | new: needs λ arguments in `Conv.inst` |
| `natZ`/`natS` (fuel loops) | `lit0`/`litS`, prelude iota `Nat.casesOn zero z s = z`, `Nat.casesOn (succ n) z s = s n`, β, IH | `lit0`/`litS` in library; iota + β new. Recursion depth is handled by the `Ev` induction itself (the `call` case), so no fuel lemma is needed |

**The λ piece** is the one real engine extension. Today `HasTy`/`Conv` are binder-free (`sc` rejects λ, `substB`
stops at binders). The general `n_eq = tr body` has λs: let-redexes, `casesOn` minors and motives. Needed:
1. `HasTy.lam` and `sc`/`substB` under binders.
2. `Conv.beta`, sound in both regimes from `Denotes.lam`'s own premise. This avoids any regime fact for applied λs.
3. A regime fact only where a λ is NOT immediately applied, i.e. for motives and minors passed to `casesOn`.
   Building a `Denotes` for such a λ needs `regime ≠ 0` or a body that is constantly `pt`. Two sources:
   - (i) `LamRegime.lam_regime_ne` (done), with stored separators `a = b → False` for each type that occurs. This
     needs two distinct body values. A constant motive body `T` needs only `⟦T⟧ ≠ pt`, which follows from two
     distinct members of `T`: a one-point variant of the lemma, cheap.
   - (ii) Read the λ's derivation out of `Model.mem` of the stored equation, as `LamDemo` does. This is generic but
     needs position tracking.

   Plan: (i) for motives (finitely many types) and (ii) or (i) for minors.

## 3. The generator: emitted `o` → export, and the Bool checks

`gen o` (a Lean function, run by `#eval`; the parser/emitter do not kernel-reduce) produces con-leche records
directly, as an ndjson writer, with no Lean elaboration needed:
* the fixed prelude: the one used by every program, i.e. today's `TinyL` prelude (`rd put len lp …`, `br_*`, iota
  and recursion equations, separators). It is exported once from Lean with lean4export and appended verbatim;
* per emitted def `(n, ty, val)`:
  - `defnDecl n [] (tr ty) (tr val)`;
  - `thmDecl n_eq [] (∀ xs, n xs = tr body)` with value `fun xs => Eq.refl (n xs)`. con-leche checks the δβ step,
    one unfolding, so this is cheap even for big defs.

`GenOk o ds` = `recsOk` generalized: every prelude record and every per-def record of `o` is in `ds` with exactly
the expected type, plus `natPin ds` and `blocksOk ds`. `TabOk`/`ThmsOk` follow as in `NanoLetDen.tabOk`/`thmsOk`:
* the heads table is `preludeTab ++ heads o`;
* `Thm.ok` is checked by `infer` per equation, as a Bool inside `GenOk`.

`Wf o` (canonical instance arguments, the shapes `emit` produces) is a Bool on `o`. It is small and
kernel-decidable per program, or proved once for `emitXs` output from `ExprSpec.emit`'s shape checks.

## 4. Pieces, effort, risks

| piece | effort | notes |
|---|---|---|
| λ in the engine (`HasTy.lam`, `substD`, `Conv.beta`, soundness) | 1–2 days | core; soundness of β is a short `Denotes.lam` argument |
| `Conv.inst` with λ arguments + casesOn iota (Prod, Nat) | 1 day | needs the regime fact for passed λs (§2.3) |
| regime for motives/minors (one-point `lam_regime`, separators in the prelude) | 0.5 day | (i) done for the two-point case |
| per-rule lemmas for the library ops (lit, + * -, <, rd 0, len, ite, let) at general values | 1 day | mostly re-stating library lemmas over `encV`; tab monotonicity lemma |
| new ops: `== & \| << >>`, `rd i`, `put o`, `len'` | 1–2 days | S6 in progress on several |
| buffers (`b*` prims, encoding) | 2 days | largest prim group; can be scoped out first (programs without buffers) |
| `Wf` for `emitXs` output | 0.5–1 day | or a per-program Bool |
| generator `gen o` + `GenOk` + `TabOk/ThmsOk` from it | 1–2 days | the prelude is fixed; per-def records are `tr` |
| typing of encodings (`encTy`) incl. pairs | 0.5 day | |

Risks:
1. **Stream-check size.** `GenOk` on a full stream (30 MB literal for `tinyr`) cannot be kernel-reduced. It stays a
   hypothesis discharged by `#eval`, as today. A per-program closed theorem with no hypotheses but acceptance needs
   a kernel-reducible parser, which is out of scope.
2. **con-leche fuel/time on big defs** (e.g. `g35`): `n_eq` by `Eq.refl` is one δ-step, cheap. The risk is the
   def's own type-check of `tr val` with deep `casesOn` nesting. Measure on the largest compiler def early.
3. **Instance/level canonicity.** `tr` maps level numerals literally. `Wf` must pin instance arguments and levels
   to the prelude's (`instHAdd.{0}` …); the per-step exports already match.
4. **Self-check cost.** con-leche re-checking the bridge itself (§12.4 of DENOTES_SPIKE) is 32k declarations in
   ~1 min. The general proof adds engine lemmas but no data, so this should stay small.
5. **Toolchain split**: the bridge is on 4.35.0-rc3 and `expr_rv` on nano's toolchain. Composition is at the `Ev`
   interface (statement-level), as before.

## 5. Progress on the λ piece (engine)

Done (all std axioms, no sorry):
* `Bridge/Real/Scope.lean`:
  - `wfk` (scope), `substD` (substitution under binders), `den_move`;
  - `regime_never`: binder data `.never` is regime 1.
* `Bridge/Real/EngineLam.lean`:
  - `den_substD`: substitution commutes with `Denotes`;
  - `beta_den`: β is sound in either regime, whatever binder data is stored;
  - `den_reset` + `Reg1`: once every binder is in regime 1, a term denotes what its `resetMeta` does. So a stored
    statement can be used through its declared (`.never`) form, given a `Reg1` fact.
* `Conv.beta`: a rule from a reached redex to `substD [a] 0 b`, covered by `conv_sound`.
* `HasTy.lam`/`HasTy.app`:
  - non-dependent λ and application at `.never`;
  - `sound` is extended (`Γ` is now an index of `HasTy`);
  - λs are built in regime 1 from `Classical.choose` over the body's soundness at each domain point.

Next, in order:
1. **Typing invariant.** β on a `let` needs the body typed under its binder. Carry `HasTy Γ (tr e) T` in `R`
   (`Γ` = the env values' types), with a `HasTy` substitution lemma for closed values. Its source is a Bool `infer`
   (extended to `lam`/`app`) on each stored `n_eq` rhs, run inside `GenOk`.
2. **`instL`.** An instance rule for stored equations with λs. Soundness: `transferN` on the stored statement, with
   the λ side's denotation moved by `den_reset` from the declared `.never` form. Needs `Reg1 φ (stored type)`
   per equation, from `LamRegime` plus prelude separators.
3. **`casesOn`.** A head with binder-carrying telescope types (the minors `∀ a b, motive (mk a b)`). Either
   generalize `head` to `substD`/`wfk`, or use per-result-type iota equations with closed binder types
   (`∀ (z : R) (s : Nat → R) (n : Nat), Nat.casesOn (fun _ => R) (succ n) z s = s n`). The motive λ needs a
   `Reg1` fact (`⟦R⟧ ≠ pt`, one-point `lam_regime`).

### 5.1 Simpler generator normal form (decided)
Tested: con-leche accepts `h_eq : h p = Prod.fst p * Prod.snd p + Prod.fst p` for
`h p := Prod.casesOn (motive := fun _ => UInt64) p (fun a b => a * b + a)` by `rfl`. That needs structure η, and
con-leche accepts it (`TinyEta.lean`, 229 decls). So the generator emits λ-free or *redex-only* stored equations:
* `let x := v; b` ↦ the redex `(λ x. b) v` (kept, so nested lets do not blow up);
* `Prod.casesOn v (λ a b. body)` ↦ `(λ a. (λ b. body) (Prod.snd v)) (Prod.fst v)`: every λ is directly applied.
  `Prod.fst/snd (Prod.mk a b)` iota equations go in the prelude (by `rfl`);
* fuel loops (`Nat.casesOn` at the def's top) ↦ two equations `f 0 xs = z`, `f (n+1) xs = s[n]` (by `rfl`), as
  `lp_zero`/`lp_succ`.

Consequences:
* no `casesOn` head with binder telescopes;
* no motive or minor λ;
* no regime facts (`Reg1`) at all. A directly applied λ denotes the body at the argument whatever its binder data
  (`beta_den`), so the stored redex and its `.never` form have the same value when the argument is in the domain
  (by typing).

Remaining (2) becomes `instL` for redex-only equations. Its soundness is `transferN` on the stored statement, with
the rhs value moved from the `.never` form by that meta-independence. (3) is replaced by the generator's loop
splitting.

Done for (1): `TySubst.hasTy_subst` (typing under substitution of typed closed values) and `GenLet.conv_let` +
`substD_comp` (the `let` step: congruence into the argument, `Conv.beta`, the env-extended substitution).

### 5.2 Decision: λ-lift at export (supersedes `instL`)
Even redex-only stored equations need an `instL` rule and a meta-independence lemma. Both depend on typing, and
`instL` would change `ThmsOk`/`Conv` in every program file. Instead the generator lambda-lifts:
* `let y := v; b` at env depth `n` ↦ an aux def `kᵢ : T_{n-1} → … → T_0 → T → S`, with
  `kᵢ x_{n-1} … x_0 y = N(b)`, and the use site `N(lt v b) = kᵢ (bv (n-1)) … (bv 0) N(v)`;
* `Prod.casesOn v (λ a b. body)` ↦ `kⱼ … (Prod.fst N(v)) (Prod.snd N(v))` (η, accepted, §5.1);
* fuel loops ↦ `f 0 … = N(z)`, `f (n+1) … = N(s)` (as `lp_zero`/`lp_succ`).

Every stored equation (`n_eq`, `kᵢ_eq`, the prelude) is then **λ-free**, so the existing proved `Conv.inst`
(binder-free `substB`) covers calls, lets and destructuring. The invariant becomes
`R env e r := Conv (substB (env.map encV) (N e)) (encV r) (tyV r)`.
* `Ev.lt`: congruence on the last argument (IH for `v`), `kᵢ_eq`, then IH for `b` at `encV a :: env`.
* `Ev.cases`: the same, with `Prod.fst/snd (Prod.mk a b)` prelude equations.
* `Ev.natS`/`natZ`: `f_succ`/`f_zero` with `litS`/`lit0`.

con-leche checks every `kᵢ_eq`/`n_eq` by `rfl` (δβ). The λ engine pieces (`beta_den`, `HasTy.lam`, `TySubst`,
`GenLet`) stay as proved infrastructure; they are not needed on this path.

Next: the normalizer `N : X → Expr` with the aux-def list, the generic `R` over `substB`/`N`, and the `Cases` from
the library lemmas.
