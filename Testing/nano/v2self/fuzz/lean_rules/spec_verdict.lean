import Nano.Parser.ParSpec
import Nano.Lexer.DsSpec
def verdict (s : String) : String :=
  match ParSpec.lexAll (s.length * 9 + 9) s.toUTF8.toList with
  | none => "REJECT(lex)"
  | some ts => match DsSpec.ds ts with
    | none => "REJECT(ds)"
    | some t2 => match ParSpec.refParse t2 with
      | none => "REJECT(parse)"
      | some _ => "ACCEPT"
def main (args : List String) : IO Unit := do
  for f in (← System.FilePath.readDir args[0]!).qsort (·.fileName < ·.fileName) do
    if f.fileName.endsWith ".lean" then
      IO.println s!"{f.fileName} {verdict (← IO.FS.readFile f.path)}"
