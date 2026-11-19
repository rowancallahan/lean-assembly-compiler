/- Nano/V2Self/Proof/ParTokWF: `TokWF ts`, the token-buffer well-formedness hypothesis of `ParserSound` (parser lead; D derives it
from the lexer spec).  List-level mirror of box C's heap relation `ParInv.TokAt`: keyword words (okTag, ≠ 5, ≠ 14), numerals
`5, b₀..b₇` with byte words < 256, identifiers `14, (1, c)*, 0` with at least one character. -/
import Nano.V2Self.Proof.ParSpec
namespace ParSpec

inductive TokL : List UInt64 → List Tok → Prop
  | nil : TokL [] []
  | kw {r : List UInt64} {toks : List Tok} (t : UInt64) : t ≠ 5 → t ≠ 14 → okTag t.toNat = true → TokL r toks →
      TokL (t :: r) (.k t.toNat :: toks)
  | num {r : List UInt64} {toks : List Tok} (bs : List UInt64) : bs.length = 8 → (∀ b ∈ bs, b.toNat < 256) → TokL r toks →
      TokL (5 :: bs ++ r) (.num (bytesVal (bs.map UInt64.toNat)) :: toks)
  | id {r : List UInt64} {toks : List Tok} (nm : List UInt64) : nm ≠ [] → TokL r toks →
      TokL (14 :: nm.flatMap (fun c => [1, c]) ++ 0 :: r) (.id (nm.map UInt64.toNat) :: toks)

/-- the token buffer decodes (as `TokL`) to some token list -/
def TokWF (ts : List UInt64) : Prop := ∃ toks, TokL ts toks

end ParSpec
