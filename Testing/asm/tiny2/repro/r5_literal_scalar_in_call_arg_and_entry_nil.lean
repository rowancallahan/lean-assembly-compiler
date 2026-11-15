import Riscv.Frontx.IndCmd
namespace R
inductive Ex where
  | lit (n : UInt64)
  | neg (a : Ex)
inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
def comp : Ex → Ins → Ins
  | .lit n, K => .push n K
  | .neg a, K => comp a (.push 0 K)
def compile (e : Ex) : Ins := comp e .nil
frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind compile on ExT using InsT
end R
