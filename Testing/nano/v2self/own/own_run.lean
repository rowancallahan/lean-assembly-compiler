import Nano.Ownership.Own
/-! `lake env lean --run Testing/nano/v2self/own/own_run.lean AST.bin...`: runs the ownership stage `C.o41` on Par1 AST
dumps (8-byte LE words); prints ACCEPT (output = input) / REJECT (empty) per file. -/
def readWords (path : String) : IO (List UInt64) := do
  let b ← IO.FS.readBinFile path
  let n := b.size / 8
  return (List.range n).map fun i => (List.range 8).foldl (fun a j => a ||| ((b.get! (8 * i + j)).toUInt64 <<< (8 * j).toUInt64)) 0

def main (args : List String) : IO UInt32 := do
  for p in args do
    let w ← readWords p
    let r := C.o41 w
    IO.println s!"{p}: {if r.isEmpty then "REJECT" else if r == w then "ACCEPT" else "MISMATCH"}"
  return 0
