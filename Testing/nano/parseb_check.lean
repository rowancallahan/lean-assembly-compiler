import Legacy.Nano.ParseBGas
import Legacy.Nano.ElabB
import Legacy.Nano.ElabU
/- `lake env lean Testing/nano/parseb_check.lean` after `python3 Testing/nano/elabb_inputs.py N SEED >
Testing/nano/work/parseb_in.txt`: layer A (`parseA` on stage 1's decoded tokens) == `(Nano.U.nanoElabU x).map Nano.U.serU` -/
open Nano Nano.B Nano.PB
def parseLine (s : String) : List UInt8 :=
  ((s.splitOn " ").drop 1).filter (· ≠ "") |>.map (fun x => x.toNat!.toUInt8)
#eval show IO Unit from do
  let ls ← IO.FS.lines "Testing/nano/work/parseb_in.txt"
  let mut bad := 0
  let mut acc := 0
  let mut lexed := 0
  for l in ls do
    let x := parseLine l
    let spec := (Nano.U.nanoElabU x).map Nano.U.serU
    let mach := match decL (lexB x) with
      | some (_, ts) => parseA 100000000 ts
      | none => none
    if (decL (lexB x)).isSome then lexed := lexed + 1
    if spec.isSome then acc := acc + 1
    let st2 := stage2 (lexB x)
    if st2 != (spec.getD []) then
      bad := bad + 1
      if bad ≤ 10 then IO.println s!"STAGE2 MISMATCH {x}"
    if spec != mach then
      bad := bad + 1
      if bad ≤ 10 then IO.println s!"MISMATCH {x}"
  IO.println s!"parseA: {ls.size} inputs, {lexed} lexed, {acc} accepted, {bad} mismatches"
