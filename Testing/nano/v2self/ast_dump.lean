/- AST dump for the certificate generator: `lake env lean --tstack=1000000 --run Testing/nano/v2self/ast_dump.lean Testing/nano/v2self/self_S_input.txt > ast.txt`
   then `python3 Testing/nano/v2self/gen_cert.py Testing/nano/v2self/self_S.lean ast.txt Nano/V2Self/Proof 20`. -/
import Nano.V2Self.Proof.Parser.ParSpec
open ParSpec
def main (args : List String) : IO Unit := do
  let src ← IO.FS.readBinFile args[0]!
  match lexAll (src.size + 1) src.toList with
  | none => IO.println "lex failed"
  | some ts =>
    match refParse ts with
    | none => IO.println "refParse REJECTED"
    | some p =>
      for d in p do
        IO.println s!"{d.id}|{d.npw}|{d.nslots}|{d.kind}|{d.nres}|{(repr d.body).pretty 1000000}"
