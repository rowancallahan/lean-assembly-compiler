import Nano.V2Self.Legacy.C.Main
/- `lean --run sizes.lean SRC`: words (Buf entries) after each chained stage: lex, parse, inline, expand, asm. -/
def main (a : List String) : IO Unit := do
  let x := (← IO.FS.readFile a[0]!).toUTF8.toList
  let b1 := C.l15 x; let b2 := C.r16 b1; let b3 := C.j8 b2; let b4 := C.e2 b3; let b5 := C.a5 b4
  IO.println s!"input {x.length} B; words: lex {b1.length} parse {b2.length} inline {b3.length} expand {b4.length} asm {b5.length}"
