/- Harvest/H4/Link: the standalone copies in Reserved.lean equal nano's own definitions (needs the nano tree to build). -/
import Nano.Lexer.Lex2Spec
import Harvest.H4.Reserved
namespace H4
theorem isW_copy : ∀ b, H4.isW b = LexSpec.isW b := fun _ => rfl
theorem isD_copy : ∀ b, H4.isD b = LexSpec.isD b := fun _ => rfl
theorem kw_copy : H4.kwWords.map H4.bytes = LexSpec.kwTable.map (·.1) := by decide +kernel
/-- nano's keywords that Lean also reserves (the others, e.g. `UInt64`, `Buf`, are free names in Lean) are in `reserved` -/
theorem kw_reserved : ["def", "let", "if", "then", "else"].all (· ∈ H4.reserved) = true := by decide +kernel
end H4
