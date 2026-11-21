/- Harvest/H8/Keywords: the keyword each do-element parser contributes (`ParserInfo.collectTokens`, Parser/Do.lean). NOT a kernel proof:
`symbol` trims its string with `String.trimAscii`, which the kernel cannot reduce (`decide +kernel` gets stuck), and `native_decide`
is not allowed. These are `#guard`s evaluated by the interpreter: a regression check against 4.34.1, not a theorem. -/
import Lean
open Lean Parser Term
#guard doBreak.info.collectTokens [] |>.contains "break"
#guard doContinue.info.collectTokens [] |>.contains "continue"
#guard doReturn.info.collectTokens [] |>.contains "return"
#guard doWhile.info.collectTokens [] |>.contains "while"
#guard doWhile.info.collectTokens [] |>.contains "do"
#guard doRepeat.info.collectTokens [] |>.contains "repeat"
#guard doRepeatUntil.info.collectTokens [] |>.contains "until"
#guard doUnless.info.collectTokens [] |>.contains "unless"
#guard doFor.info.collectTokens [] |>.contains "for"
#guard doFor.info.collectTokens [] |>.contains "in"
#guard doLet.info.collectTokens [] |>.contains "mut"
#guard doLetArrow.info.collectTokens [] |>.contains "←"
#guard doIf.info.collectTokens [] |>.contains "else"
#guard doNested.info.collectTokens [] |>.contains "do"
#guard leadPrec == 1022 && argPrec == 1023
