import Riscv.Frontx.IndCmd
namespace R
inductive T where
  | nil
  | lit (n : UInt64)
  | bin (k : UInt64) (a b : T)
  | op (k : UInt64) (rest : T)
-- `if` inside the b-argument of a recursive call: `sem` is not provable (unsolved goals, case bin)
def comp : T → T → T
  | .nil, K => K
  | .lit n, K => .op n K
  | .op k r, K => .op k r
  | .bin k a b, K => comp a (comp b (if k == 5 then K else .op k K))
def compile (e : T) : T := comp e .nil
frontx_ind_type TT := T
frontx_ind compile on TT
end R
