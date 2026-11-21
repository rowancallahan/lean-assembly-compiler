/- **nano → S3, link 3: S3 expressions over words** (`Testing/notes/NANO_S3.md`).

L3 = the S3 calculus' expressions of type `w` (`Compiler/S3/Syntax.lean`: `Expr S Γ .w`, meaning the relation `Ev`),
using only `var`, `lit`, `bin`, `let_`.  The ONE construct changed: variables are typed, scoped de Bruijn variables
(`Var Γ .w`) instead of raw indices with "out of range = 0".  `tr3 σ` maps nano index `i` to the S3 variable `σ[i]`
and an out-of-range index to the literal `0` (an operand out of range: a `let` of `0` in front).  The context map `σ`
lets the expression live in any S3 context (link 4 puts it under the input decoder's matches).
Theorems: `tr3_ok` (any context agreeing with the word environment), `tr3_prog` (programs: context = the arguments,
for every argument list). -/
import Legacy.Nano.S3L2
import Legacy.Compiler.S3.Syntax

namespace Nano.S3
open Proven.S3

def Bop.prim : Bop → Prim
  | .add => .op .add
  | .sub => .op .sub
  | .mul => .mul

theorem Bop.prim_eval (o : Bop) (x y : UInt64) : o.prim.eval x.toBitVec y.toBitVec = (o.eval x y).toBitVec := by
  cases o <;> simp [Bop.prim, Prim.eval, Proven.Op.eval, Bop.eval]

/-- an operand under one extra `let` of `0`: the variable shifted, or the `0` -/
def opd {Γ : List Ty} (x : Option (Var Γ .w)) : Var (.w :: Γ) .w := (x.map .s).getD .z

/-- **link 3**: nano index `i` is the S3 variable `σ[i]` -/
def tr3 {S : Sig} : {Γ : List Ty} → List (Var Γ .w) → A → Expr S Γ .w
  | _, _, .num n => .lit n.toBitVec
  | _, σ, .var i => match σ[i]? with
    | some x => .var x
    | none => .lit 0
  | _, σ, .bin o i j => match σ[i]?, σ[j]? with
    | some x, some y => .bin o.prim x y
    | x, y => .let_ (.lit 0) (.bin o.prim (opd x) (opd y))
  | _, σ, .let_ v b => .let_ (tr3 σ v) (tr3 (.z :: σ.map .s) b)

/-- the S3 variables `σ` hold the words `ws` in `env` -/
def Agree {Γ : List Ty} (env : List V) : List (Var Γ .w) → List UInt64 → Prop
  | [], [] => True
  | x :: σ, w :: ws => env[x.idx]? = some (.w w.toBitVec) ∧ Agree env σ ws
  | _, _ => False

theorem Agree.get {Γ : List Ty} {env : List V} : ∀ {σ : List (Var Γ .w)} {ws : List UInt64}, Agree env σ ws →
    ∀ i, (∀ x, σ[i]? = some x → env[x.idx]? = some (.w (ws.getD i 0).toBitVec)) ∧ (σ[i]? = none → ws.getD i 0 = 0)
  | [], [], _, i => by simp
  | x :: σ, w :: ws, ⟨hx, h⟩, 0 => by simp [hx]
  | x :: σ, w :: ws, ⟨_, h⟩, i + 1 => by simpa using h.get i
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem Agree.lift {Γ : List Ty} {env : List V} (τ : Ty) (v : V) : ∀ {σ : List (Var Γ .w)} {ws : List UInt64},
    Agree env σ ws → Agree (v :: env) (σ.map (Var.s (σ := τ))) ws
  | [], [], _ => trivial
  | x :: σ, w :: ws, ⟨hx, h⟩ => ⟨by simpa [Var.idx] using hx, Agree.lift τ v h⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem opd_get {Γ : List Ty} {env : List V} {σ : List (Var Γ .w)} {ws : List UInt64} (h : Agree env σ ws) (i : Nat) :
    (V.w 0 :: env)[(opd σ[i]?).idx]? = some (.w (ws.getD i 0).toBitVec) := by
  obtain ⟨h1, h2⟩ := h.get i
  cases hx : σ[i]? with
  | none =>
    have := h2 hx; simp only [List.getD_eq_getElem?_getD] at this ⊢; simp [opd, Var.idx, this]
  | some x => simp [opd, Var.idx, h1 x hx]

/-- **link 3 is correct**: in any environment where `σ` holds the words `ws`, `tr3 σ a` evaluates to `den2 a ws` -/
theorem tr3_ok (P : Proven.S3.Prog) : ∀ (a : A) {Γ : List Ty} (σ : List (Var Γ .w)) (env : List V) (ws : List UInt64),
    Agree env σ ws → Ev P env (tr3 σ a) (.w (den2 a ws).toBitVec)
  | .num n, _, σ, env, ws, _ => .lit
  | .var i, _, σ, env, ws, h => by
    obtain ⟨h1, h2⟩ := h.get i
    simp only [tr3, den2]
    split
    · next x hx => exact .var (h1 x hx)
    · next hx => rw [h2 hx]; exact .lit
  | .bin o i j, _, σ, env, ws, h => by
    obtain ⟨hi1, hi2⟩ := h.get i
    obtain ⟨hj1, hj2⟩ := h.get j
    simp only [tr3, den2, ← Bop.prim_eval]
    split
    · next x y hx hy => exact .bin (hi1 x hx) (hj1 y hy)
    · next x y hn =>
      exact .let_ .lit (.bin (opd_get h i) (opd_get h j))
  | .let_ v b, _, σ, env, ws, h => by
    simp only [tr3, den2]
    refine .let_ (tr3_ok P v σ env ws h) (tr3_ok P b _ _ _ ?_)
    exact ⟨rfl, Agree.lift _ _ h⟩

/-- the arguments as S3 variables: argument `i` (counting from the newest) is variable `i` -/
def idVars : (n : Nat) → List (Var (List.replicate n .w) .w)
  | 0 => []
  | n + 1 => .z :: (idVars n).map .s

theorem idVars_agree : ∀ ws : List UInt64,
    Agree (ws.map fun w => V.w w.toBitVec) (idVars ws.length) ws
  | [] => trivial
  | _ :: ws => ⟨rfl, Agree.lift _ _ (idVars_agree ws)⟩

/-- **link 3, programs**: the S3 expression over the arguments (`Γ` = `n` words) evaluates, for every argument list
of the arity, to `Prog2.eval` -/
theorem tr3_prog (P : Proven.S3.Prog) (p : Prog2) (args : List UInt64) (v : UInt64) (h : p.eval args = some v) :
    Ev P (args.reverse.map fun w => V.w w.toBitVec) (tr3 (idVars p.1) p.2) (.w v.toBitVec) := by
  unfold Prog2.eval at h
  split at h
  · next hl =>
    cases h
    have := tr3_ok P p.2 (idVars args.reverse.length) _ args.reverse (idVars_agree _)
    rw [List.length_reverse, hl] at this
    exact this
  · exact nomatch h

end Nano.S3
