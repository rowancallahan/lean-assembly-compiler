import Nano.Parser.ParRun
open ParSpec ParRun
/- usage: runrun DIR N : for each DIR/p{i}.txt print `i REJECT` or `i w1 w2 …` (Layer 2 `runParse` on the Lex2-spec tokens of the source) -/
def main (args : List String) : IO Unit := do
  let d := args[0]!
  for i in List.range args[1]!.toNat! do
    let src ← IO.FS.readBinFile s!"{d}/p{i}.txt"
    match (lexAll (src.size + 1) src.toList).bind (runParse (64 * src.size + 64)) with
    | none => IO.println s!"{i} REJECT"
    | some ws => IO.println (s!"{i} " ++ " ".intercalate (ws.map toString))
