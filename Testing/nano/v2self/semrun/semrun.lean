/- semrun: run a Nano source under the proved semantics (for RG's runtime differential tests).
   usage: SRC=prog.nano INP=input.bin OUT=out.bin lake env lean Testing/nano/v2self/semrun/semrun.lean
   (an #eval, not `--run`: the Sail model imported by Main already defines `main`.)
   pipeline = the objects of `compiler_correct`: lexAll (sound for Lex2Spec.Lexes, SrcLink.lexAll_sound) → refParse
   (ParsesProgram) → C.o41 on `serialize p` (≠ [] certifies LinearK, OwnStage) → `Sem κC p INP`.
   OUT: the output bytes on success (a file: #eval would capture stdout as text).  A rejection / Stop is a Lean error (nonzero exit) naming the stage. -/
import Nano.V2Self.Proof.Main.Main
open ParSpec NanoMain

def semrun : IO Unit := do
  let some s ← IO.getEnv "SRC" | throw (IO.userError "semrun: set SRC")
  let some i ← IO.getEnv "INP" | throw (IO.userError "semrun: set INP")
  let some o ← IO.getEnv "OUT" | throw (IO.userError "semrun: set OUT")
  let src ← IO.FS.readBinFile s
  let inp ← IO.FS.readBinFile i
  let some ts := lexAll (src.size + 1) src.toList | throw (IO.userError "semrun: LEX REJECT")
  let some p := refParse ts | throw (IO.userError "semrun: PARSE REJECT")
  if C.o41 (serialize p) == [] then throw (IO.userError "semrun: OWN REJECT")
  match Sem κC p inp.toList with
  | .ok out => IO.FS.writeBinFile o (ByteArray.mk out.toArray)
  | .error .cap => throw (IO.userError "semrun: STOP cap")
  | .error .stuck => throw (IO.userError "semrun: STOP stuck")

#eval semrun
