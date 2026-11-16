import Lean
import Nano.Elab
/- Subset oracle: for each case (JSON line `{"src":..,"name":..,"ty":"UInt64"|"Int64","ins":[["1","2"],..]}` on stdin) run
   Lean's REAL frontend on the text (header-less file = `import Init` only) and `nanoElab` + `Prog.eval`.  Output per case one line
   `real=R|A[v,..] nano=R|A[v,..]` (outputs as decimals of the result bits; `A?` = accepted but not evaluable).
   usage: lake env lean --run Testing/nano/oracle.lean < cases.jsonl -/
open Lean Elab

def rejectOrOut (r : Option (List String)) : String := match r with
  | none => "R" | some vs => "A[" ++ ",".intercalate vs ++ "]"

unsafe def evalReal (env : Environment) (src name ty : String) (arity : Nat) (ins : List (List Nat)) :
    IO (Option (List String)) := do
  let run (s : String) : IO (Environment × Bool) := do
    let st ← IO.processCommands (Parser.mkInputContext s "<nano>") {} (Command.mkState env {} {})
    return (st.commandState.env, !st.commandState.messages.hasErrors)
  let (_, ok) ← run src
  if !ok then return none
  let conv (j : Nat) := if ty == "Int64" then s!"(a.getD {j} 0).toInt64" else s!"(a.getD {j} 0)"
  let call := name ++ " " ++ " ".intercalate ((List.range arity).map conv)
  let body := if ty == "Int64" then s!"({call}).toUInt64" else call
  let (env2, ok2) ← run (src ++ s!"\ndef __w (a : List UInt64) : UInt64 := {body}\n")
  if !ok2 then return some ["?"]
  match env2.evalConst (List UInt64 → UInt64) {} `__w with
  | .error _ => return some ["?"]
  | .ok f => return some (ins.map fun a => toString (f (a.map UInt64.ofNat)).toNat)

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Init}] {} 0 (loadExts := true)
  let stdin ← IO.getStdin
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    let .ok j := Json.parse l | throw (IO.userError s!"bad json {l}")
    let src := (j.getObjValAs? String "src").toOption.get!
    let name := (j.getObjValAs? String "name").toOption.get!
    let ty := (j.getObjValAs? String "ty").toOption.get!
    let ins : List (List Nat) := ((j.getObjValAs? (List (List String)) "ins").toOption.get!).map (·.map String.toNat!)
    let arity := (ins.headD []).length
    let real ← evalReal env src name ty arity ins
    let nano := match Nano.nanoElab src.toUTF8.toList with
      | none => none
      | some p => some (ins.map fun a => match p.eval (a.map UInt64.ofNat) with | some v => toString v.toNat | none => "?")
    IO.println s!"real={rejectOrOut real} nano={rejectOrOut nano}"
