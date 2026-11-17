/- The five nano v2 source stages composed (Testing/notes/NANO_V2_SRC.md): on every source whose intermediate
results are short enough, the v2 pipeline computes exactly the v1 pipeline of `Nano.selfHosted`
(lexA → stage2b → inlB → mexp → asm). -/
import Nano.V2S.ParseProof
import Nano.V2S.Expand

namespace Nano.V2S
open Nano Nano.U Nano.PS Nano.LS

/-- the five v2 stages, linked -/
def chainV (src : List UInt8) : List UInt8 := asmV (mexpV (inlV (p2bV (lexV src))))

theorem chainV_eq (src : List UInt8) (h1 : src.length < 2 ^ 32) (h2 : (lexA src).length < 2 ^ 27)
    (h3 : (stage2b (lexA src)).length < 2 ^ 32) (h4 : (inlB (stage2b (lexA src))).length < 2 ^ 32)
    (h5 : (mexp (inlB (stage2b (lexA src)))).length < 2 ^ 32) :
    chainV src = asm (mexp (inlB (stage2b (lexA src)))) := by
  unfold chainV
  rw [LexP.lexV_eq src h1, ParseP.p2bV_eq _ h2, InlP.inlV_eq _ h3, mexpV_eq _ h4, asmV_eq _ h5]

end Nano.V2S
