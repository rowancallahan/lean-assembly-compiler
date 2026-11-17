/- **`s3_compileF` in parts** (untrusted, build-time only): `s3_compileF N := main s3_part a b` generates exactly the
text of `s3_compileF N := main` and elaborates only its commands with index in `[a, b)` (plus every
`namespace`/`open`/`end`). Splitting one program over several files (each importing the previous one) gives the
same declarations, hence the same `N.P` and the same compiled words, with each file's build bounded.
`s3_compileF N := main s3_count` logs the number of commands and the index and head of each. -/
import Compiler.S3.Front

namespace Proven.S3.Front
open Lean Meta Elab Command

syntax (name := s3CompileFPart) "s3_compileF " ident " := " term " s3_part " num num : command
syntax (name := s3CompileFCount) "s3_compileF " ident " := " term " s3_count" : command

def s3Cmds (N : Name) (t : Syntax) : CommandElabM (Array Syntax) := do
  let txt ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let (_, st) ← (fnIdx e).run {}
    genText N st "" "s3_solveF"
  let inputCtx := Parser.mkInputContext txt "<s3_compile>"
  let env ← getEnv
  let mut pstate : Parser.ModuleParserState := {}
  let mut cmds := #[]
  repeat
    let (cmd, ps', msgs) := Parser.parseCommand inputCtx { env, options := {} } pstate {}
    pstate := ps'
    unless msgs.toList.isEmpty do throwError "S3 parse error"
    if cmd.isOfKind ``Parser.Command.eoi then break
    cmds := cmds.push cmd
  return cmds

def isScope (cmd : Syntax) : Bool :=
  cmd.isOfKind ``Parser.Command.namespace || cmd.isOfKind ``Parser.Command.open || cmd.isOfKind ``Parser.Command.end

@[command_elab s3CompileFPart] def elabS3FPart : CommandElab := fun stx => do
  let a := stx[5].isNatLit?.get!
  let b := stx[6].isNatLit?.get!
  let cmds ← s3Cmds stx[1].getId stx[3]
  unless a < b ∧ b ≤ cmds.size do throwError "s3_compileF part: bad range {a} {b} of {cmds.size}"
  for i in [0:cmds.size] do
    if isScope cmds[i]! || (a ≤ i ∧ i < b) then elabCommand cmds[i]!

@[command_elab s3CompileFCount] def elabS3FCount : CommandElab := fun stx => do
  let cmds ← s3Cmds stx[1].getId stx[3]
  let mut s := s!"{cmds.size} commands\n"
  for i in [0:cmds.size] do
    s := s ++ s!"{i}: {(cmds[i]!.reprint.getD "").take 60 |>.replace "\n" " "}\n"
  logInfo s

end Proven.S3.Front
