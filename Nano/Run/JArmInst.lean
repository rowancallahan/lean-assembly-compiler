/- The instance of `JT.JArmBits` (Nano/Run/JArmView.lean), assembled from the field theorems `jab_<field>` of
JArmBitsL2.lean / JArmBitsL4a.lean / JArmBitsL4b.lean. -/
import Nano.Run.JArmBitsL2
import Nano.Run.JArmBitsL4a
import Nano.Run.JArmBitsL4b
namespace JT

/-- **the bit-level facts about the translator hold** -/
theorem jArmBits : JArmBits where
  l2_lt := jab_l2_lt
  l2_big := jab_l2_big
  l2_kind := jab_l2_kind
  l2_A := jab_l2_A
  l2_B := jab_l2_B
  l2_C := jab_l2_C
  l2_op := jab_l2_op
  l2_zero := jab_l2_zero
  l4_neg := jab_l4_neg
  l4_reg := jab_l4_reg
  l4_mapped := jab_l4_mapped
  l4_al := jab_l4_al
  l4_e50 := jab_l4_e50
  l4_br := jab_l4_br
  l4_lsl := jab_l4_lsl
  l4_e51 := jab_l4_e51
  l4_alu := jab_l4_alu
  l4_e52 := jab_l4_e52
  l4_e53 := jab_l4_e53
  l4_cb := jab_l4_cb
  l4_e63 := jab_l4_e63
  l4_e62 := jab_l4_e62
  l4_li := jab_l4_li
  l4_mem := jab_l4_mem

end JT
