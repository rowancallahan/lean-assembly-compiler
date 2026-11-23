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

`natLitSupported env` (the checker's guard that `Nat`, `Nat.zero`, `Nat.succ` are stored with their usual
types) is PROVED from acceptance (`NatLit.natLit_of_accepted`: the stream's Nat block is the pinned one).
One NAMED hypothesis on `env` remains (no Lean `axiom`; true of the env by `#eval`,
Testing/denotes_real/CheckNano.lean):
* `H_indTypes : IndStored env indHeads` — `List`, `List.nil`, `List.cons`, `UInt8`, `UInt64` are stored with
  their declared types. (con-leche proves this for defs and theorems, `checkDecls_consts`, not for inductives.)

**`nano_input`.** The same for an INPUT-DEPENDENT program, `def m (x : List UInt8) : List UInt8 := put [] (rd x 0 + 1)`
(output: the first input byte plus one, wrapping; `[1]` on the empty input), stated for ANY accepted stream that
holds its records (`recsOkR`, a Bool check) and a Nat-pin record. The actual export
(Testing/denotes_real/tinyr.ndjson, accepted, 755 declarations) satisfies both by `#eval` (CheckNano.lean); its
parsed literal (30 MB unshared) is too large to keep as a Lean term.

The machine end: `expr_rv` (Nano/Expr/RvExpr.lean, branch keep_round1_armfix, nano's 4.34.1 package) says the
RISC-V code writes `f a` and `Ev (progOf o) [.l (encodeInput a)] mainX (.l (f a))` for the emitted `o`. With
`o = oM`, that `Ev` fact is this theorem's premise. They are not composed into one Lean term: the two packages are
on different toolchains (4.34.1 + Sail vs con-leche's 4.35.0-rc3), and `o = oM` is `#eval emitXs srcM`.
Shapes, side by side:
* `ExprCorrect riscv compileC` (expr_rv) concludes, for the emitted `o`:
  `∃ finishState, Runs … ∧ readMemory … (f a).length = some (f a) ∧ Ev (progOf o) [.l (encodeInput a)] mainX (.l (f a))`
* `nano_tiny` / `nano_input` assume: `Ev (progOf oM) [.l inp] NanoTiny.mainX (.l out)` (resp. `oR`), with
  `NanoTiny.mainX` the verbatim copy of `ExprSpec.mainX := .app (.c "m" []) (.bv 0)`; instantiate `inp := encodeInput a`,
  `out := f a` (the bytes the machine wrote).
-/
import Bridge.Real.NanoDen
import Bridge.Real.Data.DsM
import Bridge.Real.NatLit
import Bridge.Real.NanoRDen

namespace Bridge
open ConLeche ExprSpec Bridge.Real Bridge.Real.NanoDen Bridge.ModelExists2

universe w

/-- the program's records (defs with their declared types, the three equations) are in the parsed stream -/
theorem recs_dsM : recsOk dsM = true := by decide +kernel

/-- the parsed stream holds a record con-leche recognises as its pinned `Nat` block -/
theorem natPin_dsM : (dsM.any fun | .indDecl b _ => basisPinHit b == some .natK | _ => false) = true := by
  decide +kernel

theorem natPin_mem : ∃ b nP, Declaration.indDecl b nP ∈ dsM ∧ basisPinHit b = some .natK := by
  obtain ⟨d, hd, hp⟩ := Array.any_eq_true'.mp natPin_dsM
  match d, hp with
  | .indDecl b nP, hp => exact ⟨b, nP, hd, by simpa using hp⟩

/-- **The tiny nano program, end to end at the Expr level, in con-leche's model.** -/
theorem nano_tiny (V : Type w) [SetTheory V] {env : Env}
    (accepted : Cached.checkDecls .verified natOpPinSets dsM = .ok env)
    (H_indTypes : IndStored env indHeads) :
    ∃ M : Model V env, CvalParams M ∧
      ∀ (inp out : List UInt8), Ev (progOf NanoTiny.oM) [.l inp] NanoTiny.mainX (.l out) →
        ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), ∃ x,
          Denotes M.cval env φ ρ (encL inp) x ∧
          ∀ Y, Denotes M.cval env φ ρ (encL out) Y → Denotes M.cval env φ (push x ρ) (tr NanoTiny.mainX) Y := by
  obtain ⟨b, nP, hb, hpin⟩ := natPin_mem
  have H_natLit : natLitSupported env = true := NatLit.natLit_of_accepted V accepted hb hpin
  obtain ⟨M, hP⟩ := model_exists' V natOpPinSets dsM env accepted
  refine ⟨M, hP, fun inp out hev φ ρ => ?_⟩
  have hout : out = [1] := by have := NanoTiny.ev_main hev; cases this; rfl
  subst hout
  exact den_m accepted H_natLit H_indTypes recs_dsM M hP φ ρ inp

/-- a stream holding a record con-leche recognises as its pinned `Nat` block -/
def natPin (ds : Array Declaration) : Bool := ds.any fun | .indDecl b _ => basisPinHit b == some .natK | _ => false

theorem natPin_of {ds : Array Declaration} (h : natPin ds = true) :
    ∃ b nP, Declaration.indDecl b nP ∈ ds ∧ basisPinHit b = some .natK := by
  obtain ⟨d, hd, hp⟩ := Array.any_eq_true'.mp h
  match d, hp with
  | .indDecl b nP, hp => exact ⟨b, nP, hd, by simpa using hp⟩

/-- **An input-dependent nano program (first byte + 1), end to end at the Expr level, in con-leche's model.** -/
theorem nano_input (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env)
    (hrec : NanoRDen.recsOkR ds = true) (hpin : natPin ds = true)
    (H_indTypes : IndStored env indHeads) :
    ∃ M : Model V env, CvalParams M ∧
      ∀ (inp out : List UInt8), Ev (progOf NanoR.oR) [.l inp] NanoTiny.mainX (.l out) →
        ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), ∃ x,
          Denotes M.cval env φ ρ (encL inp) x ∧
          ∀ Y, Denotes M.cval env φ ρ (encL out) Y → Denotes M.cval env φ (push x ρ) (tr NanoTiny.mainX) Y := by
  obtain ⟨b, nP, hb, hpin'⟩ := natPin_of hpin
  have H_natLit : natLitSupported env = true := NatLit.natLit_of_accepted V accepted hb hpin'
  obtain ⟨M, hP⟩ := model_exists' V pins ds env accepted
  refine ⟨M, hP, fun inp out hev φ ρ => ?_⟩
  have hout : out = [NanoR.outR inp] := by have := NanoR.ev_mainR hev; cases this; rfl
  subst hout
  exact NanoRDen.den_mR accepted H_natLit H_indTypes hrec M hP φ ρ inp

end Bridge
