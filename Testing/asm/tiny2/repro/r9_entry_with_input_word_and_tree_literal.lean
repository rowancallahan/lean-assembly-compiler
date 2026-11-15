import Riscv.Frontx.IndCmd
namespace R
inductive T where
  | nil
  | lit (n : Nat)
  | bin (k : Nat) (a b : T)
def comp : T → Nat → T → T
  | .nil, _, K => K
  | .lit n, d, K => .lit (n + d)
  | .bin k a b, d, K => comp a d (comp b (d + 1) K)
def compile (e : T) (d : Nat) : T := comp e d .nil
frontx_ind_type TT := T
frontx_ind compile on TT
end R
