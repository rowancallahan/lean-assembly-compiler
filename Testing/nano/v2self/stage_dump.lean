import Nano.V2Self.C.Lex2
import Legacy.Nano.V2Self.Legacy.C.Par0
import Nano.V2Self.C.Gen
/- Stage-boundary dump for B₁ (native Lean) of C on one source file: tokens (C.s10), AST words (C.y13), code bytes (C.g41),
one hex value per line, in `OUT.tok`, `OUT.ast`, `OUT.code`.  The B₂/B₃ dumps use the same format, so the first differing
stage is found with `cmp`/`diff`.  run: lean --run Testing/nano/v2self/stage_dump.lean SRC OUT -/
def hx (l : List UInt64) : String := String.join (l.map fun v => (Nat.toDigits 16 v.toNat).asString ++ "\n")
def main (args : List String) : IO Unit := do
  let src := args.getD 0 ""
  let out := args.getD 1 ""
  if src.isEmpty || out.isEmpty then throw (IO.userError "usage: stage_dump SRC OUT")
  let txt ← IO.FS.readFile src
  let tk := C.s10 txt.toUTF8.toList
  let ast := C.y13 tk
  let code := C.g41 [] ast
  IO.FS.writeFile (out ++ ".tok") (hx tk)
  IO.FS.writeFile (out ++ ".ast") (hx ast)
  IO.FS.writeFile (out ++ ".code") (hx (code.map (·.toUInt64)))
  IO.println s!"{src}: tokens {tk.length}, ast words {ast.length}, code bytes {code.length}"
