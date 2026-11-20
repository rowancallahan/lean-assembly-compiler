import Nano.V2Self.Legacy.C.Main
/- `lean --run native_ref.lean SRC OUT`: the chained driver `C.m` (Lean semantics) on SRC; writes OUT bytes, prints length. -/
def main (a : List String) : IO Unit := do
  let x := (← IO.FS.readFile a[0]!).toUTF8.toList
  let y := C.m x
  IO.println s!"C.m output: {y.length} bytes"
  IO.FS.writeBinFile a[1]! (ByteArray.mk y.toArray)
