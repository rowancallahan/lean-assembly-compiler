import Riscv.Frontx.IndCmd
namespace R
inductive Ex where
  | lit (n : UInt64)
  | var
  | add (a b : Ex)
  | sub (a b : Ex)

inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
  | ldx (rest : Ins)
  | add (rest : Ins)
  | sub (rest : Ins)

def Ins.app : Ins → Ins → Ins
  | .nil, ys => ys
  | .push n r, ys => .push n (r.app ys)
  | .ldx r, ys => .ldx (r.app ys)
  | .add r, ys => .add (r.app ys)
  | .sub r, ys => .sub (r.app ys)

def comp : Ex → Ins
  | .lit n => .push n .nil
  | .var => .ldx .nil
  | .add a b => (comp a).app ((comp b).app (.add .nil))
  | .sub a b => (comp a).app ((comp b).app (.sub .nil))

frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind comp on ExT using InsT
end R
