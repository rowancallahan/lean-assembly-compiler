/- Dump (name, kind, level params, hash of type, hash of value) for every `Armv9.*` constant of the full model,
sorted by name, to the file named by $DUMP_OUT. Run inside the model's lake project, after the full build:
  DUMP_OUT=/path/dump.txt lake env lean dump_hashes.lean
The imports are the 35 modules of the unpartitioned model; the partitioned model has the same module names (its core
modules are imported through them), so one script serves both layouts. Diff the two outputs with `diff`. -/
import Armv9
import Armv9.Arith import Armv9.ArmExtras import Armv9.Armv9 import Armv9.Builtins import Armv9.Common
import Armv9.DecodeEnd import Armv9.Defs import Armv9.Devices import Armv9.EventClauses import Armv9.FakeReal
import Armv9.Fetch import Armv9.Flow import Armv9.Impdefs import Armv9.Instrs32 import Armv9.Instrs64
import Armv9.Instrs64Sme import Armv9.Instrs64Sve import Armv9.Interface import Armv9.Interrupts
import Armv9.MapClauses import Armv9.MonoRewrites import Armv9.Option import Armv9.Prelude import Armv9.ReadWriteV1
import Armv9.Reset import Armv9.Result import Armv9.ReverseEndianness import Armv9.SpecializationV1 import Armv9.String
import Armv9.Stubs import Armv9.Sysregs import Armv9.SysregsAutogen import Armv9.V8Base import Armv9.Vector

open Lean Elab Command

run_cmd do
  let path ← IO.getEnv "DUMP_OUT"
  let some path := path | throwError "set DUMP_OUT"
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    unless (`Armv9).isPrefixOf n do continue
    let (kind, v) : String × Option Expr := match ci with
      | .defnInfo d => (s!"def/{repr d.safety}", some d.value)
      | .thmInfo t => ("thm", some t.value)
      | .opaqueInfo o => (s!"opaque/{o.isUnsafe}", some o.value)
      | .axiomInfo a => (s!"axiom/{a.isUnsafe}", none)
      | .inductInfo i => (s!"induct/{i.ctors}", none)
      | .ctorInfo c => (s!"ctor/{c.induct}/{c.cidx}", none)
      | .recInfo r => (s!"rec/{r.rules.map (·.rhs.hash)}", none)
      | .quotInfo _ => ("quot", none)
    rows := rows.push s!"{n} {kind} {ci.levelParams} {ci.type.hash} {v.map (·.hash)}"
  rows := rows.qsort (· < ·)
  IO.FS.writeFile path (String.intercalate "\n" rows.toList ++ "\n")
  logInfo m!"{rows.size} Armv9.* constants written to {path}"
