/- writes Testing/nano/work/{roots,tokens}.txt: the single-component constants of `Init` and the identifier-like tokens of its parser
   (the names nano's identifiers must avoid).  `lake env lean --run Testing/nano/names.lean` -/
import Lean
open Lean Elab
def isId (s : String) : Bool := s.all (fun c => c.isAlphanum || c == '_') && !s.isEmpty && !(s.front).isDigit
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Init}] {} 0 (loadExts := true)
  let mut roots : Array String := #[]
  for (n, _) in env.constants.toList do
    match n with
    | .str .anonymous s => if isId s then roots := roots.push s
    | _ => pure ()
  roots := roots.qsort (· < ·)
  IO.println s!"roots {roots.size}"
  IO.FS.writeFile "Testing/nano/work/roots.txt" ("\n".intercalate roots.toList)
  let tt := Parser.getTokenTable env
  let mut toks : Array String := #[]
  for k in tt.findPrefix "" do if isId k then toks := toks.push k
  toks := toks.qsort (· < ·)
  IO.println s!"tokens {toks.size}"
  IO.FS.writeFile "Testing/nano/work/tokens.txt" ("\n".intercalate toks.toList)
