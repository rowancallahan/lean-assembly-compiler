/-
# Bridge.Main — a tiny nano program, from its emitted Expr to con-leche's model

The program (nano source text `NanoTiny.srcM`):

    def m (x : List UInt8) : List UInt8 := put [] 1

nano's emitter turns it into the Expr `NanoTiny.oM` (`m := λ x : List UInt8. put (List.nil UInt8) (1 : UInt64)`).
`dsM` is the Lean export of that program (with nano's prelude `put` and three equations: `m_eq`, `put_one`,
`br_litN`; Testing/denotes_real/TinyM.lean), as con-leche's own parser and preparation read it. The con-leche
binary accepts that file ("accepted 304 declarations (--verified)").

**`nano_tiny`.** Take any environment `env` that con-leche's verified fold returns on `dsM`. Then there is a
model of `env` — the one con-leche's main theorem builds (`model_exists'` = `model_exists` plus `CvalParams`) —
in which: whenever nano's big-step meaning `Ev` says the emitted `m`, applied to an input `inp`, yields `out`,
con-leche's `Denotes` gives the same answer: the con-leche term `tr mainX` (`m` applied to the input variable),
with the input variable bound to the denotation of the input bytes `encL inp`, denotes what `encL out` denotes.
`Ev`, `Denotes`, `Model`, `checkDecls` are imported unchanged from nano and con-leche.

Two NAMED hypotheses on `env` remain (no Lean `axiom`; both are true of the env by `#eval`,
Testing/denotes_real/CheckNano.lean):
* `H_natLit : natLitSupported env` — the checker's own guard that `Nat`, `Nat.zero`, `Nat.succ` are stored with
  their usual types;
* `H_indTypes : IndStored env indHeads` — `List`, `List.nil`, `List.cons`, `UInt8`, `UInt64` are stored with
  their declared types. (con-leche proves this for defs and theorems, `checkDecls_consts`, not for inductives.)

The machine end: `expr_rv` (Nano/Expr/RvExpr.lean, branch keep_round1_armfix, nano's 4.34.1 package) says the
RISC-V code writes `f a` and `Ev (progOf o) [.l (encodeInput a)] mainX (.l (f a))` for the emitted `o`. With
`o = oM`, that `Ev` fact is this theorem's premise. They are not composed into one Lean term: the two packages are
on different toolchains (4.34.1 + Sail vs con-leche's 4.35.0-rc3), and `o = oM` is `#eval emitXs srcM`.
-/
import Bridge.Real.NanoDen
import Bridge.Real.Data.DsM

namespace Bridge
open ConLeche ExprSpec Bridge.Real Bridge.Real.NanoDen Bridge.ModelExists2

universe w

/-- the program's records (defs with their declared types, the three equations) are in the parsed stream -/
theorem recs_dsM : recsOk dsM = true := by decide +kernel

/-- **The tiny nano program, end to end at the Expr level, in con-leche's model.** -/
theorem nano_tiny (V : Type w) [SetTheory V] {env : Env}
    (accepted : Cached.checkDecls .verified natOpPinSets dsM = .ok env)
    (H_natLit : natLitSupported env = true)
    (H_indTypes : IndStored env indHeads) :
    ∃ M : Model V env, CvalParams M ∧
      ∀ (inp out : List UInt8), Ev (progOf NanoTiny.oM) [.l inp] NanoTiny.mainX (.l out) →
        ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), ∃ x,
          Denotes M.cval env φ ρ (encL inp) x ∧
          ∀ Y, Denotes M.cval env φ ρ (encL out) Y → Denotes M.cval env φ (push x ρ) (tr NanoTiny.mainX) Y := by
  obtain ⟨M, hP⟩ := model_exists' V natOpPinSets dsM env accepted
  refine ⟨M, hP, fun inp out hev φ ρ => ?_⟩
  have hout : out = [1] := by have := NanoTiny.ev_main hev; cases this; rfl
  subst hout
  exact den_m accepted H_natLit H_indTypes recs_dsM M hP φ ρ inp

end Bridge
