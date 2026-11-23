# Universe-level issue in con-leche's `Model` (FABLE-MINI)

Checked against dwijayuda/con-leche @ 3b37939 (read only, not built). Lean: `Universe.lean`
(standalone, sorry-free, lean 4.34.1; `Denotes`/`Model` are trimmed copies, not the real ones).

**(a) Confirmed.** `Denotes.const` (Denotes.lean:144) gives `cval n (Level.substFn φ ps us)`, and
`substFn` (Verify/Level.lean:34) falls through to `φ`, so `substFn φ [] [] = φ`
(`substFn_nil`). A level-free constant denotes `cval n φ`, at the ambient assignment. `Model`
(Denotes.lean:265) has only `mem`, `false_empty`, `eq_equality`; none relates `cval n φ` to
`cval n ψ`. `ite.{1}` moves the assignment to `upd φ u 1`, so `mem` for `ite` speaks of
`cval Nat (upd φ u 1)` while the arguments denote into `cval Nat φ`.

**(b) Not provable from `Model`.** `levelFree_not_invariant`: for an env with one axiom
`c : Sort 1`, if `univ 1` has two distinct members there is a `Model` in which `c` denotes
different sets at two assignments (select by `φ` at a name no constant binds). Caveat: proved
for the trimmed `Model` (`mem` only); the other two fields are vacuous for that env because
neither `False` nor `Eq` is stored, but that step is argued, not checked.

**Workaround with no Model change.** `substFn_fixed` / `substFn_ones`: at `φ₁ := fun _ => 1`,
any instantiation whose levels all evaluate to 1 leaves the assignment at `φ₁`. So if every
universe instantiation in the emitted terms is at level 1 (`ite.{1}`, `Nat.casesOn.{1}`,
`Eq.{1}`), state the bridge theorem at `φ₁` only and everything stays at one assignment.
Fails as soon as one parameter name is needed at two different values (e.g. a `.{0}` and a
`.{1}` use of constants sharing the name `u`), or a level-polymorphic emitted term is wanted.

**(c) Field to propose** (`CvalParams` in `Universe.lean`):

```lean
  /-- a constant's value reads only its own level parameters -/
  cval_params : ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
    ∀ ψ₁ ψ₂ : LevelParam → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → cval n ψ₁ = cval n ψ₂
```

con-leche already carries this internally as `EnvModel.acval_params`
(`AcvalParamsAt`, Model/Levels.lean:53), on annotated terms; the public `Model` drops it.
Not checked: that `Model.cval` is built from `acval` in a way that transports it.
With it: `cval_levelFree` (level-free constants are φ-independent) and `Denotes.shift`
(denotation depends on φ only through the values of the term's own levels) — proved for the
bvar/sort/const/app fragment; `lam`/`pi` would additionally need `regime φ pw` to agree.
