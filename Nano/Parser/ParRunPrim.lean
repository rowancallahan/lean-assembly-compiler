/- Nano/Parser/ParRunPrim: Layer 2, PRIMITIVES.  Par1's prim tables (`primAr` = v91, `primRes` = v92, `primPar` = v90, prim id = token − 38)
agree with ParSpec's `primSig`: same id, arity, result shape, and parameter codes (`psCode`: the input and a List value are both code `ls`;
which one is meant is decided by the callee: for prims, exactly parameter 0 of rd / len / len' (ids 1..3) is the input). -/
import Nano.Parser.ParRunCall
namespace ParRun
open ParSpec

/-- the shape code Par1 stores for a parameter kind (v133 / v136: the input is a code-3 List, the fuel a code-4 Nat) -/
def psCode : Ps → Sh | .inp => .ls | .fuel => .nt | .sh s => s

theorem prim_sig {t : Nat} (h1 : 38 < t) (h2 : t < 48) :
    ∃ ps, primSig t = some (t - 38, ps, primRes (t - 38)) ∧ ps.length = primAr (t - 38) ∧
      (∀ i : Nat, i < ps.length → ps[i]?.map psCode = some (primPar (t - 38) i)) ∧
      (∀ i : Nat, ps[i]? = some Ps.inp ↔ (i = 0 ∧ t - 38 < 4)) ∧ (∀ i : Nat, ps[i]? ≠ some Ps.fuel) := by
  have ht : t = 39 ∨ t = 40 ∨ t = 41 ∨ t = 42 ∨ t = 43 ∨ t = 44 ∨ t = 45 ∨ t = 46 ∨ t = 47 := by omega
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨_, rfl, by decide, ?_, ?_, ?_⟩ <;> intro i <;>
    first
      | (intro hi; simp only [List.length_cons, List.length_nil] at hi
         (obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega) <;> first | rfl | (exact absurd hi (by decide)))
      | (match i with
         | 0 => decide
         | 1 => decide
         | 2 => decide
         | _ + 3 => simp)

theorem prim_head {md : Nat} {st : St} {t : Nat} {r : List Tok} (ht : st.toks = .k t :: r) (h1 : 38 < t) (h2 : t < 48) :
    stepF (.prim md) st =
      some ([.args (.pr (t - 38)) (primAr (t - 38)), .mkCallN (.pr (t - 38)) st.vals.length], { st with toks := r }) := by
  have ht' : t = 39 ∨ t = 40 ∨ t = 41 ∨ t = 42 ∨ t = 43 ∨ t = 44 ∨ t = 45 ∨ t = 46 ∨ t = 47 := by omega
  rcases ht' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [stepF, ht]

end ParRun
