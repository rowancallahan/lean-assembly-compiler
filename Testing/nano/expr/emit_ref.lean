import Nano.Expr.ExprSpec
/- usage: Testing/scripts/lean_run.sh Testing/nano/expr/emit_ref.lean SRC... : the reference emitter's S text of each
SRC (names prefixed `P<i>.` when there are several, as lean_side.sh); a source nano rejects gives `R <i> <reason>` -/
def main (args : List String) : IO Unit := do
  for (f, i) in args.zipIdx do
    let p := if args.length > 1 then s!"P{i}." else ""
    match ExprSpec.emitProg (← IO.FS.readBinFile f).toList with
    | .ok s => IO.print (String.join (s.splitOn "\n" |>.filter (· ≠ "") |>.map fun l => "D " ++ p ++ (l.drop 2).toString ++ "\n"))
    | .error e => IO.println s!"R {i} {e}"
