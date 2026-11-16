/- prints every nano-shaped name (1-3 lowercase letters, optional digit or `_1`) that Lean resolves globally, has as an
   alias, or reads as a token: the `reserved` list of Nano/Elab.lean.  Run: lake env lean Testing/nano/reserved.lean -/
import Lean
open Lean Elab Command in
elab "#reserved" : command => do
  let env ← getEnv
  let tt := Lean.Parser.getTokenTable env
  let toks := tt.values
  let ls := "abcdefghijklmnopqrstuvwxyz".toList
  let mut words : Array String := #[]
  for a in ls do
    words := words.push (String.singleton a)
    for b in ls do
      words := words.push (String.ofList [a, b])
      for c in ls do words := words.push (String.ofList [a, b, c])
  let mut out : Array String := #[]
  for w0 in words do
    for suf in ["", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "_1"] do
      let w := w0 ++ suf
      let n := Name.mkSimple w
      let isTok := toks.contains w
      let isG := env.contains n || !(getAliases env n false).isEmpty
      let rs := Lean.ResolveName.resolveGlobalName env {} Name.anonymous [] n
      if isTok || isG || !rs.isEmpty then out := out.push w
  logInfo m!"{out.size}: {" ".intercalate out.toList}"
#reserved
