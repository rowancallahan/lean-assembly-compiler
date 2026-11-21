/- Nano/Expr/EvalEmit: eval_emit (EXPR.md §6 step 2), the relation and its first cases.
`VR v ws`: the evaluator's structured value `v` stands for Sem's flat slot words `ws` (a pair is the concatenation;
a byte list is a buffer whose words' low bytes are the bytes, as Sem's `put` keeps the word and the output keeps the
low byte; a Nat is a word, as Sem's fuel). Target, per node `e` and def table:
  emit cx bs exp e = (x, _) ∧ EnvR bs env venv ∧ ev cx' e env = .ok (.inl ws) → ∃ f v, evalX P f venv x = some v ∧ VR v ws
then per def (`defMean`) and per program (`Sem` ↔ `runX`). Proved so far: the leaf cases. -/
import Nano.Expr.EvalLeaf
import Nano.Main.Sem
namespace ExprSpec
open NanoMain ParSpec

inductive VR : V → List W → Prop
  | w (v : UInt64) : VR (.w v) [.w v]
  | n (k : Nat) (u : UInt64) : u.toNat = k → VR (.n k) [.w u]
  | b (l : List UInt64) : VR (.b l) [.b l]
  | l (o : List UInt8) (ws : List UInt64) : ws.map UInt64.toUInt8 = o → VR (.l o) [.b ws]
  | p {a b : V} {xs ys : List W} : VR a xs → VR b ys → VR (.p a b) (xs ++ ys)

/-- the const case: Sem's value and the emitted literal's value are related -/
theorem const_case (cx : Ctx) (env : List W) (P : Prog) (f : Nat) (venv : List V) (v : UInt64) :
    ev cx (.const v) env = .ok (.inl [.w v]) ∧ evalX P (f + 1) venv (lit .uw v.toNat) = some (.w v) ∧
      VR (.w v) [.w v] := by
  refine ⟨by simp [ev], eval_lit_uw P f venv v, .w v⟩

/-- a fuel literal: Sem's word and the Nat agree when the literal fits a word (it always does: numerals are
8-byte tokens) -/
theorem const_case_nt (P : Prog) (f : Nat) (venv : List V) (v : UInt64) :
    evalX P (f + 1) venv (lit .nt v.toNat) = some (.n v.toNat) ∧ VR (.n v.toNat) [.w v] :=
  ⟨eval_lit_nt P f venv v.toNat, .n _ v rfl⟩

end ExprSpec
