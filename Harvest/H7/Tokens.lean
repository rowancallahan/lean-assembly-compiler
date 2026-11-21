/- Harvest/H7/Tokens (STATUS: checked by `#guard` = compiled evaluation, NOT a kernel proof): the keyword/token tables of Lean 4.34.1's declaration parsers as DATA.
Every `Parser` carries a `ParserInfo` (`firstTokens`, `collectTokens`) built by total combinators (`symbolInfo`, `andthenInfo`,
`orelseInfo`); the parser *function* (`ParserFn`) is not touched.
Why not a theorem: every `symbol "x"` stores `"x".trimAscii.copy` (Parser/Basic.lean:1114), and `String.trimAscii` is not kernel-reducible in 4.34.1
(`example : "ab ".trimAscii.copy = "ab" := by decide` gets stuck), so `decide +kernel` on any `Parser.info` fails. Fold-in: a Lean-side patch is impossible;
the table stays a guard (re-run on every Lean bump). Antiquotation noise (`$`, `_`, `(`, ... from `leading_parser` quotations) is filtered by `kwOnly` (alphabetic tokens). -/
import Lean
open Lean Parser
namespace H7

def ft : FirstTokens → List String | .tokens l | .optTokens l => l | _ => []
def kwOnly (l : List String) : List String := (l.filter fun s => s.length > 0 && s.all Char.isAlpha).eraseDups
/- keywords that can START the parser -/
def firstKw (p : Parser) : List String := kwOnly (ft p.info.firstTokens)
/- every keyword the parser mentions -/
def allKw (p : Parser) : List String := kwOnly (p.info.collectTokens [])
/- every non-alphabetic symbol it mentions -/
def allSym (p : Parser) : List String := (p.info.collectTokens []).filter fun s => !(s.length > 0 && s.all Char.isAlpha)

/- Lean's declaration heads (no modifiers), exactly: 4.34.1 also has `coinductive`, `public`, `meta` -/
#guard firstKw Command.declaration == ["private", "public", "protected", "meta", "noncomputable", "unsafe", "partial", "nonrec", "abbrev", "def", "theorem", "opaque", "scoped", "local", "instance", "axiom", "example", "inductive", "coinductive", "class", "structure"]

#guard firstKw Command.definition == ["def"]
#guard firstKw Command.«abbrev» == ["abbrev"]
#guard firstKw Command.«theorem» == ["theorem"]
#guard firstKw Command.«structure» == ["structure", "class"]
#guard firstKw Command.«inductive» == ["inductive"]
#guard firstKw Command.«instance» == ["scoped", "local", "instance"]

/- the declaration-modifier keywords, exactly -/
#guard firstKw (Command.declModifiers false) == ["private", "public", "protected", "meta", "noncomputable", "unsafe", "partial", "nonrec"]

/- the clause keywords inside each declaration form -/
#guard ["extends", "where", "deriving"].all (allKw Command.«structure»).contains
#guard ["where", "deriving"].all (allKw Command.«inductive»).contains
#guard ["where", "deriving"].all (allKw Command.definition).contains
#guard ["where"].all (allKw Command.«instance»).contains
/- `deriving` of an `inductive`/`structure`/`def`: the `deriving instance ... for` command and the `deriving C, D` list -/
#guard ["deriving", "instance", "for"].all (allKw Command.«deriving»).contains

/- symbols: `:=` (def), `|` and `=>` (equations / constructors), `::` (structure constructor name), doc-comment opener, attribute opener -/
#guard [":=", "|", "=>", "@["].all (allSym Command.definition).contains
#guard ["::", ":=", "{", "}", "/--", "@["].all (allSym Command.«structure»).contains
#guard ["|", "/--", "@[", ":="].all (allSym Command.«inductive»).contains

/-! ### Candidate nano rules (future syntax), as byte tables like `LexSpec.kwTable` -/
def bytes (s : String) : List UInt8 := s.toUTF8.toList
/- nano today: `def`, `private`. Candidate heads for later: `theorem` (erased), `abbrev`, `instance`, `structure`, `inductive` -/
def nanoHeads : List (List UInt8) := ["def", "abbrev", "theorem", "instance", "structure", "inductive", "example"].map bytes
def nanoMods : List (List UInt8) := ["private", "protected", "partial", "unsafe", "noncomputable"].map bytes

/- **subset form**: every candidate head / modifier byte word is a keyword Lean's `declaration` parser can start with -/
#guard nanoHeads.all (fun w => (firstKw Command.declaration).any (bytes · == w))
#guard nanoMods.all (fun w => (firstKw (Command.declModifiers false)).any (bytes · == w))

end H7
