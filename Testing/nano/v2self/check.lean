import Nano.V2.Front
/- `lake env lean --run Testing/nano/v2self/check.lean FILE...`: per FILE, strip comments/imports, then (a) the whole text
+ a stub `m` is run through `frontElabK 256`; (b) on reject, defs are added one at a time and the FIRST def whose prefix
is rejected is reported (a def calling a missing earlier def is also rejected: files are checked in dependency order
by passing several FILEs, the texts are concatenated and every def of the LAST file is tested). -/
open Nano.V2B
def strip (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut inC := false
  for l in s.splitOn "\n" do
    if inC then
      if (l.splitOn "-/").length > 1 then inC := false
    else if l.startsWith "/-" then
      if (l.splitOn "-/").length ≤ 1 then inC := true
    else if l.startsWith "import" || l.startsWith "--" then pure ()
    else out := out ++ [l]
  return out
/-- split into defs (a def starts at a line beginning with `def`) -/
def defs (ls : List String) : List String := Id.run do
  let mut out : List String := []
  for l in ls do
    if l.startsWith "def" then out := out ++ [l]
    else if l.trimAscii.isEmpty then pure ()
    else if out.isEmpty then pure () else out := out.dropLast ++ [out.getLast! ++ "\n" ++ l]
  return out
def stub := "def m (x : List UInt8) : List UInt8 := put [] 0\n"
def acc (txt : String) : Bool := (frontElabK 256 (txt ++ stub).toUTF8.toList).isSome
def main (args : List String) : IO UInt32 := do
  let mut pre : List String := []
  let mut bad := 0
  for f in args do
    let ds := defs (strip (← IO.FS.readFile f))
    let mut cur := pre
    let mut first : Option String := none
    for d in ds do
      cur := cur ++ [d]
      if first.isNone && !acc ("\n".intercalate cur ++ "\n") then first := some d
    match first with
    | none => IO.println s!"{f}: ACCEPT ({ds.length} defs)"
    | some d => bad := bad + 1; IO.println s!"{f}: REJECT, first offending def: {(d.splitOn "\n")[0]!}"
    pre := pre ++ ds
  return (if bad == 0 then 0 else 1)
