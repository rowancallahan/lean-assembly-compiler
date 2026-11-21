import Nano.Expr.Emit
/- usage: Testing/scripts/lean_run.sh Testing/nano/expr/emit_lean.lean SRC... : E (Nano/Expr/Emit.lean) run as Lean
defs on each SRC (List-backed prelude: slow, for small sources); names prefixed `P<i>.` as emit_ref.lean -/
def main (args : List String) : IO Unit := do
  for (f, i) in args.zipIdx do
    let s := String.fromUTF8! ⟨(C.e99 (← IO.FS.readBinFile f).toList).toArray⟩
    let p := if args.length > 1 then s!"P{i}." else ""
    if s == "R\n" then IO.println s!"R {i}" else
    IO.print (String.join (s.splitOn "\n" |>.filter (· ≠ "") |>.map fun l => "D " ++ p ++ (l.drop 2).toString ++ "\n"))
