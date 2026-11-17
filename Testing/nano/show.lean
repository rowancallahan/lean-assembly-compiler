import Nano.Gen
/- usage: lake env lean --run Testing/nano/show.lean file...   prints, per nano source file, `n P` as Lean terms -/
namespace Nano
def Ex.show : Ex → String
  | .num n => s!"(Ex.num {n})" | .var i => s!"(Ex.var {i})"
  | .add a b => s!"(Ex.add {a.show} {b.show})" | .sub a b => s!"(Ex.sub {a.show} {b.show})"
  | .mul a b => s!"(Ex.mul {a.show} {b.show})" | .let_ v b => s!"(Ex.let_ {v.show} {b.show})"
  | .call b a => s!"(Ex.call {b.show} {a.show})" | .anil => "Ex.anil" | .acons e r => s!"(Ex.acons {e.show} {r.show})"
end Nano
open Nano
def main (fs : List String) : IO Unit := do
  for f in fs do
    let src ← IO.FS.readFile f
    match nanoElab src.toUTF8.toList with
    | some (n, e) => IO.println s!"({n}, {e.show})"
    | none => IO.println "NONE"
