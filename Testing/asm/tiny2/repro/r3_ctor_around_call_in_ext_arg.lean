import Riscv.Frontx.IndCmd
namespace R
inductive Ex where
  | lit (n : UInt64)
  | set (a b : Ex)
inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
  | op (k : UInt64) (rest : Ins)
  | pop (rest : Ins)
def Ins.app : Ins → Ins → Ins
  | .nil, ys => ys
  | .push n r, ys => .push n (r.app ys)
  | .op k r, ys => .op k (r.app ys)
  | .pop r, ys => .pop (r.app ys)
def comp : Ex → Ins
  | .lit n => .push n .nil
  | .set a b => (comp a).app (.pop (comp b))
frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind comp on ExT using InsT
end R
