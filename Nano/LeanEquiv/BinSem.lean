/- Nano/LeanEquiv/BinSem: the meaning nano gives a binary operator (`NanoMain.binop`, Nano/Main/Sem.lean) is the
function Lean's notation for the same token denotes on `UInt64` (Init/Notation.lean:281-290:
`infixl:65 " + " => HAdd.hAdd`, …).  Chain: token bytes → lexer tag (`LexSpec.opTable`) → op id (`ParSpec.opInfo`)
→ `binop`.  Proved here: tag → op id → Lean function, never stuck.  Bytes ↔ tag ↔ Lean's symbol: `Prec.binOps_eq_lean`.
NOT proved: that Lean's macro for the symbol produces that function (the `=> HAdd.hAdd` part is `macro_rules` code),
and the elaborator's choice of the `UInt64` instance. -/
import Nano.Main.Sem
import Nano.LeanEquiv.Prec
namespace LeanEquiv

/-- nano's binary operators: (lexer tag, the Lean function of the notation, on `UInt64`) -/
def binFns : List (Nat × (UInt64 → UInt64 → UInt64)) :=
  [(27, HOr.hOr), (26, HAnd.hAnd), (10, HAdd.hAdd), (11, HSub.hSub), (12, HMul.hMul),
   (28, HShiftLeft.hShiftLeft), (29, HShiftRight.hShiftRight)]

/-- the same tags as the precedence table -/
theorem binFns_tags : binFns.map (·.1) = binOps.map (·.1) := rfl

/-- **operator meaning**: for every operator tag, the op id the parser emits evaluates to Lean's function -/
theorem binop_eq_lean (a b : UInt64) :
    (ParSpec.opInfo 27).map (fun e => NanoMain.binop e.1 a b) = some (.ok (a ||| b)) ∧
    (ParSpec.opInfo 26).map (fun e => NanoMain.binop e.1 a b) = some (.ok (a &&& b)) ∧
    (ParSpec.opInfo 10).map (fun e => NanoMain.binop e.1 a b) = some (.ok (a + b)) ∧
    (ParSpec.opInfo 11).map (fun e => NanoMain.binop e.1 a b) = some (.ok (a - b)) ∧
    (ParSpec.opInfo 12).map (fun e => NanoMain.binop e.1 a b) = some (.ok (a * b)) ∧
    (ParSpec.opInfo 28).map (fun e => NanoMain.binop e.1 a b) = some (.ok (a <<< b)) ∧
    (ParSpec.opInfo 29).map (fun e => NanoMain.binop e.1 a b) = some (.ok (a >>> b)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- table form: every entry of `binFns` -/
theorem binFns_eq_lean (a b : UInt64) : ∀ e ∈ binFns,
    (ParSpec.opInfo e.1).map (fun i => NanoMain.binop i.1 a b) = some (.ok (e.2 a b)) := by
  intro e he
  simp only [binFns, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end LeanEquiv
#print axioms LeanEquiv.binop_eq_lean
#print axioms LeanEquiv.binFns_eq_lean
