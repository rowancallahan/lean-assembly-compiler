/- Nano/Parser/ParRunWF: the Layer-2 invariant `WF fs st` for box C (machine ↔ Layer 2).  Under `WF`, a `none` of `stepF`
is a genuine machine failure: the reads that Layer 2 cannot express (operand stack too shallow, `ty` unset, row / parameter
index out of range, a binder placeholder used as a value, a CALL / CONT whose callee has no result code) are excluded.
The task stack is read top-down with a ghost state `G` (operand depth `v`, binding count `b`, `t` = "`ty` is set"); each frame has a
"big-step" effect `effF` (what it and everything it pushes do to `G`) and a precondition. -/
import Nano.Parser.ParRunStar
namespace ParRun
open ParSpec

structure G where
  v : Nat
  b : Nat
  t : Bool

/-- the parts of the state the preconditions read (unchanged by every non-final frame) -/
structure Ctx where
  rows : List DefR
  arm : Bool

def St.ctx (st : St) : Ctx := ⟨rows st, st.arm⟩
def St.g (st : St) : G := ⟨st.vals.length, st.binds.length, st.ty.isSome⟩

def Ctx.arity (c : Ctx) : Callee → Nat
  | .df j => (c.rows[j]?.map fun d => d.params.length).getD 0
  | .pr p => primAr p
def Ctx.callee (c : Ctx) : Callee → Prop
  | .df j => j < c.rows.length
  | .pr _ => True
/-- a CALL target: a FINISHED row (the current row is the last one) -/
def Ctx.callTgt (c : Ctx) : Callee → Prop
  | .df j => j + 1 < c.rows.length
  | .pr _ => True

/-- prims 1..3 (`p < 4`) take at least one argument: their node's first child is read by the flattener -/
def _root_.ParRun.Callee.need1 : Callee → Bool
  | .pr p => decide (p < 4)
  | .df _ => false

/-- the parameter count of the current (last) row -/
def Ctx.npar (c : Ctx) : Nat := (c.rows.getLast?.map fun d => d.params.length).getD 0

instance (c : Ctx) (x : Callee) : Decidable (c.callee x) := by cases x <;> unfold Ctx.callee <;> infer_instance
instance (c : Ctx) (x : Callee) : Decidable (c.callTgt x) := by cases x <;> unfold Ctx.callTgt <;> infer_instance

/-- frames below which nothing may stand (they never return to a frame below: the def header / body / close chain) -/
def Frame.final : Frame → Bool
  | .binders | .group _ | .plainBody | .afterColon | .stateTy | .armsStart | .armBind .. | .zeroDone | .defEnd | .defClose | .defs => true
  | _ => false

/-- big-step effect and precondition of a frame -/
def effF (c : Ctx) : Frame → G → Option G
  | .expr .., ⟨v, b, t⟩ => some ⟨v + 1, b, t⟩
  | .prim _, ⟨v, b, t⟩ => some ⟨v + 1, b, t⟩
  | .binLoop _, g => if 1 ≤ g.v then some g else none
  | .shiftNum _, g => if 1 ≤ g.v then some g else none
  | .mkBin _, ⟨v, b, t⟩ => if 2 ≤ v then some ⟨v - 1, b, t⟩ else none
  | .parenClose, g => if 1 ≤ g.v then some g else none
  | .tupRest, g => if 1 ≤ g.v then some g else none
  | .mkPair, ⟨v, b, _⟩ => if 2 ≤ v then some ⟨v - 1, b, true⟩ else none
  | .rparen, g => some g
  | .ifCmp _, g => if 1 ≤ g.v then some g else none
  | .ifThen .., ⟨v, b, t⟩ => if 2 ≤ v then some ⟨v - 1, b, t⟩ else none
  | .ifElse, g => some g
  | .mkIte _, ⟨v, b, t⟩ => if 4 ≤ v then some ⟨v - 3, b, t⟩ else none
  | .letStart _, ⟨v, b, t⟩ => some ⟨v + 1, b, t⟩
  | .letSemi .., g => if 1 ≤ g.v then some g else none
  | .letEnd _ d, ⟨v, b, t⟩ => if 2 ≤ v ∧ d ≤ b then some ⟨v - 1, d, t⟩ else none
  | .letPairX _, ⟨v, b, t⟩ => some ⟨v + 1, b, t⟩
  | .letPairY .., ⟨v, b, t⟩ => some ⟨v + 1, b, t⟩
  | .stash _, g => some g
  | .letPairSemi .., g => if 1 ≤ g.v then some g else none
  | .args _ k, ⟨v, b, t⟩ => some ⟨v + k, b, t⟩
  | .argAtom, ⟨v, b, t⟩ => some ⟨v + 1, b, t⟩
  | .argName, ⟨v, b, t⟩ => some ⟨v + 1, b, t⟩
  | .mkCallN x d, ⟨v, b, t⟩ => if d ≤ v ∧ v - d ≤ c.arity x ∧ c.callTgt x ∧ (x.need1 = true → d < v) then some ⟨d + 1, b, t⟩ else none
  | .argCheck x k, g => if k ≤ g.v ∧ k ≤ c.arity x ∧ c.callee x then some g else none
  | .mkCall x n, ⟨v, b, t⟩ => if n ≤ v ∧ c.callTgt x ∧ (x.need1 = true → 1 ≤ n) then some ⟨v - n + 1, b, t⟩ else none
  | .selfArgs, ⟨v, b, t⟩ => if c.arm then some ⟨v + 1, b, t⟩ else none
  | .mkCont f k, ⟨v, b, t⟩ => if k ≤ v ∧ f + 1 = c.rows.length ∧ c.arm then some ⟨v - k + 1, b, t⟩ else none
  | .tyAtom, ⟨v, b, _⟩ => some ⟨v, b, true⟩
  | .tyCross, g => if g.t then some g else none
  | .tyPair _, g => if g.t then some g else none
  | .flat _, g => some g
  | .flatL _, g => some g
  | .assign a _, g => if a ≤ g.b ∧ (a < g.b → g.t) then some g else none
  | .group a, g => if a ≤ g.b then some g else none
  | .stateTy, g => if g.t ∧ 1 ≤ c.npar then some g else none
  | .plainBody, g => if g.t then some g else none
  | .afterColon, g => if g.t then some g else none
  | .armsStart, g => if g.t ∧ 2 ≤ c.npar then some g else none
  | .zeroDone, g => if 1 ≤ g.v ∧ 2 ≤ c.npar then some g else none
  | .mkLoop, ⟨v, b, t⟩ => if 2 ≤ v then some ⟨v - 1, b, t⟩ else none
  | .armBind stp i, g => if 1 ≤ i ∧ i < c.npar ∧ (stp → 1 ≤ g.v) then some g else none
  | .defClose, g => if (c.rows.getLast?.bind DefR.res).isSome then some g else none
  | _, g => some g

def effL (c : Ctx) : List Frame → G → Option G
  | [], g => some g
  | f :: r, g => (effF c f g).bind (effL c r)

/-- the frames that may stand above `assign` (a binder group's type) -/
def Frame.isTy : Frame → Bool
  | .tyAtom | .tyCross | .tyPair _ | .rparen => true
  | _ => false

/-- the shape of a task stack: final frames only at the bottom, a binder group's `group` frame alone, `assign` only directly
above `binders` with type frames above it -/
def finalsLast : List Frame → Bool
  | [] => true
  | [_] => true
  | x :: r => !x.final && finalsLast r

def Shape (fs : List Frame) : Prop :=
  finalsLast fs ∧
  (∀ a, .group a ∈ fs → fs = [.group a]) ∧
  (∀ a sz, .assign a sz ∈ fs → ∃ tys, (∀ f ∈ tys, f.isTy) ∧ fs = tys ++ [.assign a sz, .binders])

/-- binder placeholders (shape code 0) exist only while their group is being parsed -/
def PhOK (fs : List Frame) (st : St) : Prop :=
  ∀ i (h : i < st.binds.length), st.binds[i].sh = none → ∃ a ≤ i, .group a ∈ fs ∨ ∃ sz, .assign a sz ∈ fs

/-- the state invariants -/
def SInv (st : St) : Prop := (∀ x ∈ st.vals, x.sh.isSome) ∧ (∀ d ∈ st.defs, d.res.isSome) ∧ (st.arm → st.cur.res.isSome)

structure WF (fs : List Frame) (st : St) : Prop where
  ghost : (effL st.ctx fs st.g).isSome
  shape : Shape fs
  ph : PhOK fs st
  inv : SInv st

theorem wf_init (toks : List Tok) : WF [.defs] (init toks) := by
  refine ⟨by simp [effL, effF, St.g, init], ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rfl
  · intro a ha; simp at ha
  · intro a sz ha; simp at ha
  · intro i h; simp [init] at h
  · simp [SInv, init]

end ParRun
