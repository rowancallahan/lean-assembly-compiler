import Nano.Parser.ParSpec
open ParSpec
/- usage: dump_pc FILE : print the reference parse of FILE as Lean definitions `PC.d<i> : DefA` (input of gen_cert.py) -/
partial def nd : Nd → String
  | .const v => s!"(.const {v})"
  | .loc s w => s!"(.loc {s} {w})"
  | .bin o a b => s!"(.bin {o} {nd a} {nd b})"
  | .ite c a b t e => s!"(.ite {c} {nd a} {nd b} {nd t} {nd e})"
  | .letE s w v b => s!"(.letE {s} {w} {nd v} {nd b})"
  | .pair cs => s!"(.pair [{", ".intercalate (cs.map nd)}])"
  | .call i as => s!"(.call {i} [{", ".intercalate (as.map nd)}])"
  | .prim p as => s!"(.prim {p} [{", ".intercalate (as.map nd)}])"
  | .loop z s => s!"(.loop {nd z} {nd s})"
  | .cont e => s!"(.cont {nd e})"
def main (args : List String) : IO Unit := do
  let src ← IO.FS.readBinFile args[0]!
  match (lexAll (src.size + 1) src.toList).bind refParse with
  | none => throw (IO.userError "REJECT")
  | some ds =>
    for d in ds do
      match d.body with
      | .loop z st => IO.println s!"{d.id} {d.npw} {d.nslots} {d.kind} {d.nres}\tL\t{nd z}\t{nd st}"
      | b => IO.println s!"{d.id} {d.npw} {d.nslots} {d.kind} {d.nres}\tP\t{nd b}"
