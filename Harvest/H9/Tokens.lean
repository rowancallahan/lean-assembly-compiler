/- Harvest/H9/Tokens: lexical facts the match/`fun |` syntax relies on, from Init/Meta/Defs.lean (isIdFirst :120). -/
namespace H9

/-- candidate rule: the wildcard token is exactly the single byte `_` (95); any longer word starting `_` is an identifier -/
def isWild (w : List UInt8) : Bool := w == [95]

/-- `_` lexes as an identifier start in Lean's char class, so Lean must (and does) special-case the hole token;
nano's word lexer accepting `_` is therefore consistent, and `isWild` must be tested before treating the word as a name. -/
theorem underscore_isIdFirst : Lean.isIdFirst '_' = true := by decide
theorem underscore_isIdRest : Lean.isIdRest '_' = true := by decide

/-- `|`, `,`, `=>` bytes used by alternatives are not identifier characters, so word lexing stops at them -/
theorem sep_not_idRest : ∀ c ∈ ['|', ',', '=', '>', '@', '+'], Lean.isIdRest c = false := by decide

/-- `@` (as-pattern), `+` (n+1) are not identifier chars either: `x@p` and `n+1` split into tokens -/
theorem as_split : Lean.isIdFirst '@' = false ∧ Lean.isIdFirst '+' = false := by decide

end H9
