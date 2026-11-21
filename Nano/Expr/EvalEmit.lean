/- Nano/Expr/EvalEmit: eval_emit (EXPR.md §6 step 2), the relation and its first cases.
`VR v ws`: the evaluator's structured value `v` stands for Sem's flat slot words `ws` (a pair is the concatenation;
a byte list is a buffer whose words' low bytes are the bytes, as Sem's `put` keeps the word and the output keeps the
low byte; a Nat is a word, as Sem's fuel). Target, per node `e` and def table:
  emit cx bs exp e = (x, _) ∧ EnvR bs env venv ∧ ev cx' e env = .ok (.inl ws) → ∃ f v, evalX P f venv x = some v ∧ VR v ws
then per def (`defMean`) and per program (`Sem` ↔ `runX`). Proved so far: const (UInt64, Nat), loc, bin (ops 1..7), ite
(`==`, `<`) as one-step lemmas. Next: let (single, pair), pair, call, prim, the loop (loopRun ↔ Nat.casesOn), the env relation,
the induction over `emit`, fuel monotonicity. -/
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

/-- the bin case: an emitted operator application evaluates to Sem's `binop` (ops 1..7, all `.bin` nodes the
parser makes) -/
theorem bin_case (P : Prog) (f : Nat) (venv : List V) (op : Nat) (a b : X) (x y z : UInt64)
    (hop : 1 ≤ op ∧ op ≤ 7) (ha : evalX P f venv a = some (.w x)) (hb : evalX P f venv b = some (.w y))
    (hz : binop op x y = .ok z) : evalX P (f + 1) venv (binX op a b) = some (.w z) := by
  obtain ⟨h1, h7⟩ := hop
  have : op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [binX, apps, U, evalX, spine, binV, binop]

/-- the loc case: a slot read is the bvar of its binder -/
theorem loc_case (cx : Ctx) (env : List W) (P : Prog) (f : Nat) (venv : List V) (s w i : Nat) (v : V)
    (hs : s + w ≤ env.length) (hv : venv[i]? = some v) (hr : VR v ((env.drop s).take w)) :
    ev cx (.loc s w) env = .ok (.inl ((env.drop s).take w)) ∧ evalX P (f + 1) venv (.bv i) = some v ∧
      VR v ((env.drop s).take w) :=
  ⟨by simp [ev, hs], by simp [evalX, hv], hr⟩

/-- the ite cases: the emitted condition decides as Sem's comparison (`==` cmp 1, `<` cmp 2) -/
theorem ite_eq_case (P : Prog) (f : Nat) (venv : List V) (r : Sh) (a b t e : X) (x y : UInt64)
    (ha : evalX P f venv a = some (.w x)) (hb : evalX P f venv b = some (.w y)) :
    evalX P (f + 2) venv (iteX r 1 a b t e) = if x = y then evalX P (f + 1) venv t else evalX P (f + 1) venv e := by
  by_cases h : x = y <;> simp_all [iteX, apps, U, evalX, evalB, spine]

theorem ite_lt_case (P : Prog) (f : Nat) (venv : List V) (r : Sh) (a b t e : X) (x y : UInt64)
    (ha : evalX P f venv a = some (.w x)) (hb : evalX P f venv b = some (.w y)) :
    evalX P (f + 2) venv (iteX r 2 a b t e) = if x < y then evalX P (f + 1) venv t else evalX P (f + 1) venv e := by
  by_cases h : x < y <;> simp_all [iteX, apps, U, evalX, evalB, spine]

end ExprSpec
