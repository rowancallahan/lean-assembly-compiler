import Nano.Ownership.Own
/-! debug: run `C.o38` def by def, print the first failing def and the walk state. -/
def readWords (path : String) : IO (List UInt64) := do
  let b ← IO.FS.readBinFile path
  let n := b.size / 8
  return (List.range n).map fun i => (List.range 8).foldl (fun a j => a ||| ((b.get! (8 * i + j)).toUInt64 <<< (8 * j).toUInt64)) 0

def main (args : List String) : IO UInt32 := do
  let x ← readWords args[0]!
  let mut s := bset (C.o40 64 bnew 16) 0 1
  let mut f : Buf := bnew
  let mut v : Buf := bnew
  let mut t := C.o40 4096 bnew 4096
  let mut d := 0
  while (bget s 0).toNat < x.length do
    let (s1, (f1, (v1, t1))) := C.o38 x s f v t
    if bget s1 1 == 1 then
      IO.println s!"def {d} FAILS: cursor {bget s1 0} (def at {bget s 0}), frames {bget s1 4}, phase {bget s1 11}, top frame {(List.range 8).map fun j => bget s1 (16 + 8 * (bget s1 4 - 1) + j.toUInt64)}, vtop {bget s1 7}, v {v1.take (bget s1 7).toNat}, K {f1.take (bget s1 6).toNat}, F {(f1.drop (bget s1 6).toNat).take (bget s1 6).toNat}, node words {(x.drop (bget s1 0).toNat).take 8}"
      return 1
    IO.println s!"def {d} ok: P {f1.take (bget s1 2).toNat} R {v1.take (bget s1 3).toNat}"
    s := s1; f := f1; v := v1; t := t1; d := d + 1
  IO.println "ALL OK"
  return 0
