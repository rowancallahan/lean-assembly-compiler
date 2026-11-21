/- **`A64SemN armSail TT TT`**: the native back end's abstract AArch64 interface (Nano/Run/A64SemN.lean: `A64Sem` plus
movn, movz with a shift, cbnz, ldur, stur, ldp, ldrb register offset, add lsl #3, lsl #sh) on the official Sail ARM
model. `A64Sem` from `a64Sail`; the nine extra fields from FieldsN.lean. -/
import ArmSail.A64
import ArmSail.FieldsN
namespace ArmSail
open Proven.Top

theorem a64SailN : JT.A64SemN armSail TT TT where
  toA64Sem := a64Sail
  movn := F_movn
  movzH := F_movzH
  cbnz := F_cbnz
  ldur := F_ldur
  stur := F_stur
  ldp := F_ldp
  ldrbR := F_ldrbR
  addLsl3 := F_addLsl3
  lslI := F_lslI

end ArmSail
