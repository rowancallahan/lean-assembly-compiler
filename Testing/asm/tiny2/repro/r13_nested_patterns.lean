import Riscv.Frontx.IndCmd
namespace R
inductive T where
  | nil
  | lit (n : UInt64)
  | var
  | bin (k : UInt64) (a b : T)
  | op (k : UInt64) (rest : T)
def fold : T → T
  | .nil => .nil
  | .lit n => .lit n
  | .var => .var
  | .op k r => .op k r
  | .bin k (.lit x) (.lit y) => .lit (x + y)
  | .bin k a b => .bin k (fold a) (fold b)
frontx_ind_type TT := T
set_option maxHeartbeats 0 in
frontx_ind fold on TT
end R
