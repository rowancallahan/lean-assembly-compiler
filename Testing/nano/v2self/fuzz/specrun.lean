import Nano.V2Self.Proof.Parser.ParSpec
open ParSpec
/- usage: specrun DIR N : for each DIR/p{i}.txt print `i REJECT` or `i w1 w2 …` (serialize (refParse (lex src))) -/
def main (args : List String) : IO Unit := do
  let d := args[0]!
  for i in List.range args[1]!.toNat! do
    let src ← IO.FS.readBinFile s!"{d}/p{i}.txt"
    match parseStr (String.fromUTF8! src) with
    | none => IO.println s!"{i} REJECT"
    | some ws => IO.println (s!"{i} " ++ " ".intercalate (ws.map toString))
