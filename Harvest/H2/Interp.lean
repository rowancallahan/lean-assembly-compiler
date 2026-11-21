/- Harvest/H2/Interp: the notation descriptors of `s!` / `m!` (data: `ParserDescr` constants, Init/Data/ToString/Macro.lean:14,
Lean/Message.lean:854) and the escape set inside an interpolated string (Lean/Parser/StrInterpolation.lean:14).
`f!` is `Init/Data/Format/Macro.lean:16` (same shape; not a named constant in Init-only scope, see README). -/
import Lean.Parser.StrInterpolation
import Lean.Message
namespace H2
open Lean

/-- candidate nano token shape of an interpolated-string term: keyword `s!` (no trailing space), then the literal -/
def interpShape (kw : String) : ParserDescr → Bool
  | .node _ 1024 (.binary `andthen (.symbol k) (.unary `interpolatedStr (.cat `term 0))) => k == kw
  | _ => false

theorem s_bang : interpShape "s!" «termS!_» = true := by decide +kernel
theorem m_bang : interpShape "m!" Lean.«termM!_» = true := by decide +kernel

/- inside `interpolatedStr`, `{` is one more quotable escape: the set is nano's escape set ∪ `{`
(proved in Escape.lean as `quotable_interp_iff`); the body parser is `term` at precedence 0 -/
