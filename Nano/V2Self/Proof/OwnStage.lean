/- Nano/V2Self/Proof/OwnStage: the ownership stage on parsed programs.  `serialize` writes numbers mod 2^64, so `o41`
alone cannot rule out wrapped fields: the size bounds `Bnd` (Gen: nslots, nres < 251) and `|serialize p| < 2^64`
are premises. -/
import Nano.V2Self.Proof.OwnP30
import Nano.V2Self.Proof.OwnWF
namespace OwnP
open C OwnSpec ParSpec

theorem own_stage {ts : List UInt64} {p : List DefA} (hp : ParsesProgram ts p) (hb : OwnWF.Bnd p)
    (hlen : (serialize p).length < 2 ^ 64) (h : o41 (serialize p) ≠ []) :
    ∃ Ks, progOk [] [] Ks p = true ∧ ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2 :=
  o41_sound p (fun d hd => OwnWF.parsed_wfp hp hb d hd) hlen h

end OwnP
