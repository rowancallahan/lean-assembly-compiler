import Nano.Parser.ParSpec
open ParSpec
def main (args : List String) : IO Unit := do
  let src := (← IO.FS.readBinFile args[0]!).toList
  let some ws := lexAll (src.length + 1) src | IO.println "lex REJECT"
  let some toks := tokens ws | IO.println "tokens REJECT"
  let F := 8 * toks.length + 8
  let mut defs : List DefI := []
  let mut rest := toks
  while !rest.isEmpty do
    match pDef F defs rest with
    | some (di, _, r) => defs := defs ++ [di]; rest := r
    | none =>
      let nm := match rest with | _ :: .id n :: _ => String.ofList (n.map Char.ofNat) | _ => "?"
      IO.println s!"pDef REJECT at def #{defs.length}: {nm}"; return
  IO.println s!"all {defs.length} defs parse"
