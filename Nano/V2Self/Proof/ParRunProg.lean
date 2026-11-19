/- Nano/V2Self/Proof/ParRunProg: the Layer-2 PROGRAM level (box B).  `loopStep`: B's `loop_spec` in the shape F's
`defs_spec` consumes; the program theorem (Accepts ⇒ refParse = some p ∧ o = serialize p) on top of `defs_spec`. -/
import Nano.V2Self.Proof.ParRunDef
import Nano.V2Self.Proof.ParRunLoop
namespace ParRun
open ParSpec

theorem loopStep : LoopStep := by
  intro n ks st fin defs name r h ht hcur hb hv _ harm hD hNN hfr hL
  obtain ⟨lp, st', n', hn, hrun, hstar, hv', hd, ho, hal, hname, hloop, hlt, hspec⟩ :=
    loop_spec h ht hcur hb hv harm hD hNN hfr hL
  exact ⟨lp, st', n', hn, hstar, hrun, hv', hd, ho, hname, hloop, hlt, hspec⟩

end ParRun
