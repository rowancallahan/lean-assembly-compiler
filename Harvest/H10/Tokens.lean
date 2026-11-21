/- Harvest/H10/Tokens: command-level data of Lean 4.34.1: precedence constants (kernel `rfl`) and the keyword tokens of the
module/command parsers (`ParserInfo.collectTokens`, checked by `#guard` = interpreter, NOT kernel: `Parser.info` is
not kernel-reducible, tried `decide +kernel`/`rfl`, stuck on `Array`/`ParserInfo` closures). -/
import Lean
import Nano.Lexer.Lex2Spec
namespace H10
open Lean Parser

-- precedence numbers (Init/Prelude.lean, Init/Notation.lean)
theorem prec_consts : (maxPrec, argPrec, leadPrec, minPrec) = (1024, 1023, 1022, 10) := rfl

-- tokens of the commands nano skips (LexSpec.lineKw = namespace open section end) and `private`
private def toks (p : Parser) : List String := p.info.collectTokens [] |>.filter fun s => s.length > 1 && s.all Char.isAlpha
#guard (toks Command.«namespace») = ["namespace"]
#guard (toks Command.«end») = ["end"]
#guard "section" ∈ toks Command.«section»
#guard "open" ∈ toks Command.«open» && "hiding" ∈ toks Command.«open» && "renaming" ∈ toks Command.«open»
#guard "universe" ∈ toks Command.«universe»
#guard "set_option" ∈ toks Command.«set_option» || (Command.«set_option».info.collectTokens []).contains "set_option"
#guard (Command.«variable».info.collectTokens []).contains "variable"
#guard (Command.docComment.info.collectTokens []).contains "/--"
#guard (Command.moduleDoc.info.collectTokens []).contains "/-!"
-- nano's lineKw words are exactly the first tokens of four of these commands
#guard LexSpec.lineKw.map (fun w => String.ofList (w.map fun b => Char.ofNat b.toNat)) = ["namespace", "open", "section", "end"]
end H10
