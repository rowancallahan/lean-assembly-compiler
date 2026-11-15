import Riscv.Frontx.IndCmd
namespace R17
inductive T where
  | nil
  | lit (n : UInt64)
  | push (n : UInt64) (rest : T)
-- a `_` arm in a function called from another function of the program (the entry's own `_` arms are fine)
def len : T → UInt64
  | .push _ r => len r + 1
  | _ => 0
def f : T → T
  | .nil => .nil
  | .lit n => .lit (len (.push n .nil))
  | .push n r => .push n r
frontx_ind_type TT := T
frontx_ind f on TT
end R17
