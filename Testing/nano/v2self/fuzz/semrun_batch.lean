/- semrun_batch: semrun.lean for many programs in one Lean process (the fuzzer's reference side).
   Same pipeline and same checks as semrun.lean (lexAll → refParse → C.o41 → Sem κC), one manifest line per run:
     MANIFEST=list.txt RESULTS=res.txt lake env lean Testing/nano/v2self/fuzz/semrun_batch.lean
   manifest line: SRC INP OUT (paths without spaces).  Result line i: OK | REJ lex | REJ parse | REJ own | STOP cap | STOP stuck.
   OUT is written only on OK.  Any other exception aborts the whole batch (fail fast). -/
import Nano.Main.Sem
open ParSpec NanoMain

def one (s i o : String) : IO String := do
  let src ← IO.FS.readBinFile s
  let inp ← IO.FS.readBinFile i
  match lexAll (src.size + 1) src.toList with
  | none => return "REJ lex"
  | some ts =>
  match refParse ts with
  | none => return "REJ parse"
  | some p =>
  if C.o41 (serialize p) == [] then return "REJ own" else
  match Sem κC p inp.toList with
  | .ok out => do
      IO.FS.writeBinFile o (ByteArray.mk out.toArray)
      return "OK"
  | .error .cap => return "STOP cap"
  | .error .stuck => return "STOP stuck"

def batch : IO Unit := do
  let some mf ← IO.getEnv "MANIFEST" | throw (IO.userError "batch: set MANIFEST")
  let some rf ← IO.getEnv "RESULTS" | throw (IO.userError "batch: set RESULTS")
  let mut acc : Array String := #[]
  for l in (← IO.FS.lines mf) do
    match l.splitOn " " with
    | [s, i, o] => acc := acc.push (← one s i o)
    | _ => throw (IO.userError s!"batch: bad manifest line: {l}")
  IO.FS.writeFile rf (String.intercalate "\n" acc.toList ++ "\n")

#eval batch
