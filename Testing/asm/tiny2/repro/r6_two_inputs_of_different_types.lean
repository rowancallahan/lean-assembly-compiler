import Riscv.Frontx.IndCmd
namespace R
inductive Ex where
  | lit (n : UInt64)
  | neg (a : Ex)
inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
  | pz (rest : Ins)
def comp : Ex → Ins → Ins
  | .lit n, K => .push n K
  | .neg a, K => comp a (.pz K)
frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind comp on ExT using InsT
end R
