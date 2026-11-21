/- Harvest/H6/Shapes: the builtin term parsers of this area are `leading_parser` values (Lean/Parser/Term.lean), i.e. a `Parser` =
{info, fn} with `fn` a closure over `ParserState`. Their `info` (first tokens, token list, node kinds) IS total data, but the kernel
cannot evaluate it: every `symbol` runs `String.trimAscii` (Init/Data/String/Slice.lean), which is stuck in `decide +kernel`/`rfl`
(reproducer in README). So these checks are `#guard` (compiled evaluation, NOT kernel-checked): status "drafted".
Candidate nano rule = `shapes` below (leading token, kind name): what `pAtom`/`pExpr` would dispatch on. -/
import Lean
namespace H6
open Lean Parser

def ftoks : FirstTokens → List String
  | .tokens l | .optTokens l => l
  | _ => []

/-- (parser, first tokens besides the antiquotation `$`, node kind) -/
def shapes : List (Parser × List String × Name) :=
  [(Term.paren, ["("], ``Term.paren), (Term.tuple, ["("], ``Term.tuple), (Term.typeAscription, ["("], ``Term.typeAscription),
   (Term.anonymousCtor, ["⟨"], ``Term.anonymousCtor), (Term.«fun», ["λ", "fun"], ``Term.«fun»),
   (Term.«show», ["show"], ``Term.«show»), (Term.«have», ["have"], ``Term.«have»), (Term.«let», ["let"], ``Term.«let»)]

#guard shapes.all fun (p, t, k) => (ftoks p.info.firstTokens).filter (· != "$") == t && (p.info.collectKinds {}).contains k

/- `fun` bodies: `basicFun` (binders `=>`/`↦` term) or `matchAlts` (`fun | p => e`) -/
#guard (Term.basicFun.info.collectTokens []).contains "=>" && (Term.basicFun.info.collectTokens []).contains "↦"
#guard (Term.«fun».info.collectTokens []).contains "|"
/- `show T from e` / `show T by tac`; `have`'s `from`-less form; tuple separators -/
#guard (Term.«show».info.collectTokens []).contains "from" && (Term.«show».info.collectTokens []).contains "by"
#guard (Term.tuple.info.collectTokens []).contains "," && (Term.typeAscription.info.collectTokens []).contains ":"
#guard (Term.app.info.collectTokens []).contains ".."
end H6
