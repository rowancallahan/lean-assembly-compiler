import Legacy.Nano.ElabB
/- run with `lake env lean Testing/nano/elabb_check.lean` after writing Testing/nano/work/elabb_in.txt
(elabb_inputs.py): stage 1 (`lexB`, decoded) == `lexT` on every input -/
open Nano Nano.B
def parseLine (s : String) : List UInt8 :=
  ((s.splitOn " ").drop 1).filter (· ≠ "") |>.map (fun x => x.toNat!.toUInt8)
#eval show IO Unit from do
  let ls ← IO.FS.lines "Testing/nano/work/elabb_in.txt"
  let mut bad := 0
  let mut acc := 0
  for l in ls do
    let x := parseLine l
    let a := lexBytes (decL (lexB x)); let b := lexBytes (lexT x)
    if (lexT x).isSome then acc := acc + 1
    if a != b then
      bad := bad + 1
      if bad ≤ 10 then IO.println s!"MISMATCH {x} machine {a} spec {b}"
  IO.println s!"stage1: {ls.size} inputs, {acc} lexed, {bad} mismatches"
