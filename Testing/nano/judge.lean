import Nano.Elab
/- usage: lake env lean --run Testing/nano/judge.lean LISTFILE.  Each line of LISTFILE: `path a1 a2 …` (argument words as
naturals < 2^64).  Prints per line `NONE`, or `I v` / `U v` (type Int64 / UInt64, `Prog.eval` of the words, `v` < 2^64),
or `ARITY` when the argument count is not the entry's arity. -/
open Nano
def main (args : List String) : IO Unit := do
  let ls ← IO.FS.lines (args.getD 0 "")
  for l in ls do
    match l.splitOn " " |>.filter (· ≠ "") with
    | f :: ws =>
      let src ← IO.FS.readBinFile f
      match nanoElabT src.toList with
      | none => IO.println "NONE"
      | some (s, p) =>
        match p.eval (ws.map fun w => UInt64.ofNat w.toNat!) with
        | some v => IO.println s!"{if s then "I" else "U"} {v.toNat}"
        | none => IO.println "ARITY"
    | [] => pure ()
