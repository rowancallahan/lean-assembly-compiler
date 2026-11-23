/- Nano/Expr/CNat: C's Nat slots `ExprC.natC` (data in CData) are NumSpec's numeral classes (`natList`, i.e.
`NumSpec.slotNat`, kernel-checked; its own module: the class analysis needs about 9 GB in the kernel). So `oC` is
`emitAll`'s output for C, the emitter that reads `NumSpec.slotNat`. -/
import Nano.Expr.CExpr
set_option maxHeartbeats 0
namespace ExprSpec

/-- C's def kinds and result widths (the numeral classes' inputs) -/
def ksC : List Nat := Cert.PC.all.map (·.kind)
def wsC : List Nat := Cert.PC.all.map (·.nres)

theorem natC_ok : Cert.PC.all.map (natList ksC wsC) = ExprC.natC := by decide +kernel

theorem emitC_spec : emitAll ExprC.ds ksC wsC 0 Cert.PC.all ExprC.st = some oC := by
  unfold emitAll; rw [natC_ok]; exact emitC

end ExprSpec
