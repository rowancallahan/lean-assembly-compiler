/- Bridge.CheckC: the compiler C's own emitted program (`ExprSpec.oC`, 341 defs) is well formed: `PWf`,
kernel-checked (`decide +kernel` on `Check.pwfChk`).  This discharges the `PWf` hypothesis of `Top.sem_denotes`
for the compiler itself (self-hosting).

STATUS: proved, no sorry. -/
import Bridge.CheckExamples
import Nano.Expr.CExpr
set_option maxHeartbeats 0

namespace Bridge.CheckC
open ExprSpec Bridge.Check Bridge.CheckEx Bridge.Typed

theorem cChk : pwfChk (sigOf oC) 100000 (ExprSpec.progOf oC) = true := by decide +kernel

/-- **C's emitted program is well formed** -/
theorem cPWf : PWf (sigOf oC) (ExprSpec.progOf oC) := pwfChk_sound cChk sigOf_res

/-- `m : List UInt8 → List UInt8` -/
theorem c_sig_m : sigOf oC "m" = some ([.ls], .ls) := by decide +kernel

end Bridge.CheckC
