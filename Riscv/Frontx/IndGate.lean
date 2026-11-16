/- `frontx_ind_gate f on T`: the type gate of `frontx_ind` alone (no program, no proofs), for surveys of many
functions (NOTES section 25, the con-leche depth probe).  It reports `gate ok` when `f`'s result and parameters are
of kinds `frontx_ind` takes (the structural argument of a declared type, at most one scalar and one more value of a
declared type, a scalar / `Bool` / `Decidable` / declared-type result), and then whether the arms of `f` and of
the functions it calls translate (`arms ok`), or the first message. -/
import Riscv.Frontx.IndCmd

namespace Proven.Frontx.IndCmd
open Lean Meta Elab Command Term

syntax "frontx_ind_gate " ident " on " ident : command
elab_rules : command
  | `(frontx_ind_gate $f:ident on $T:ident) => do
  let embN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo (mkIdentFrom T (T.getId ++ `emb)))
  let Tn := embN.getPrefix
  let fN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
  let msg ← liftTermElabM do
    let env ← getEnv
    let tys ← (#[Tn] ++ nestedNames env Tn).mapM rTyOfName
    let gate ← try
        let _ ← fnInfo tys fN
        pure none
      catch e => pure (some (← e.toMessageData.toString))
    match gate with
    | some m => return s!"gate FAIL: {m}"
    | none =>
      try
        let fns ← programOf tys fN
        for i in [0:fns.size] do
          let found ← IO.mkRef #[]
          discard <| armsOf fns[i]!.name fns[i]!.ty tys fns i found
        return s!"gate ok; arms ok ({fns.size} function(s))"
      catch e => return s!"gate ok; arms FAIL: {← e.toMessageData.toString}"
  logInfo m!"frontx_ind_gate {fN}: {msg}"

end Proven.Frontx.IndCmd
