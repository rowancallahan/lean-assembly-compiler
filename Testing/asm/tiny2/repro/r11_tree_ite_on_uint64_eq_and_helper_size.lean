import Riscv.Frontx.IndCmd
namespace R
inductive T where
  | nil
  | lit (n : UInt64)
  | var
  | bin (k : UInt64) (a b : T)
  | op (k : UInt64) (rest : T)
def mk2 : T → UInt64 → T → T
  | .lit x, k, .lit y => if k == 0 then .lit (x + y) else .bin k (.lit x) (.lit y)
  | a, k, b => .bin k a b
def fold : T → T
  | .nil => .nil
  | .lit n => .lit n
  | .var => .var
  | .op k r => .op k r
  | .bin k a b => mk2 (fold a) k (fold b)
frontx_ind_type TT := T
set_option maxHeartbeats 0 in
frontx_ind fold on TT
end R
