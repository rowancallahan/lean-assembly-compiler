/- The global facts of the node theorem, `RunCxS` (callees' success contracts, ranges), and `lnT_pos`.  The node
theorem itself is `runVO` / `runTO` / `runLO` (CapNode.lean: success and failure outcomes in one induction). -/
import Nano.Run.EVSCall
import Nano.Run.EVSLoop
import Nano.Run.NdRun
import Nano.Run.NdCG
namespace Templates
open CallProbe SimW SafeRun ParSpec

/-- the global facts of the safe node theorem -/
structure RunCxS (K : SC) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64) (KL : LayW) : Prop where
  ig : IGOK K.hb E0 IG
  e62 : E0 < 2 ^ 62
  cb : ∀ s, IG s → LinkOK C s
  p20 : K.p < 2 ^ 20
  inp : InpOK IG c28 K.c29 K.inp
  inw : InpW KL IG
  nl251 : K.nl < 251
  c18 : C.length < 2 ^ 18
  defs : ∀ id, id < K.nd → DefXS KL C (K.T id) (K.npwOf id) (K.nresOf id) IG K.hb E0 (K.fs id)
  tl : ∀ id, id < K.nd → K.T id < C.length

theorem RunCxS.hI {K C IG E0 c28 KL} (h : RunCxS K C IG E0 c28 KL) : InvOKH K.hb K.p (IGp IG E0 K.p) :=
  invOKH_IGp h.ig K.p

theorem RunCxS.inpP {K C IG E0 c28 KL} (h : RunCxS K C IG E0 c28 KL) : InpOK (IGp IG E0 K.p) c28 K.c29 K.inp :=
  fun s hs => h.inp s hs.1

theorem RunCxS.inwP {K C IG E0 c28 KL} (h : RunCxS K C IG E0 c28 KL) : InpW KL (IGp IG E0 K.p) :=
  fun s hs => h.inw s hs.1

theorem lnT_pos (K : SC) : ∀ e : Nd, 1 ≤ lnT K e
  | .ite _ _ _ _ e => by have := lnT_pos K e; simp only [lnT]; omega
  | .letE _ _ _ b => by have := lnT_pos K b; simp only [lnT]; omega
  | .cont _ => by simp only [lnT]; omega
  | .const _ => by simp only [lnT]; omega
  | .loc _ _ => by simp only [lnT]; omega
  | .bin _ _ _ => by simp only [lnT]; omega
  | .pair _ => by simp only [lnT]; omega
  | .call _ _ => by simp only [lnT]; omega
  | .prim _ _ => by simp only [lnT]; omega
  | .loop _ _ => by simp only [lnT]; omega

end Templates
