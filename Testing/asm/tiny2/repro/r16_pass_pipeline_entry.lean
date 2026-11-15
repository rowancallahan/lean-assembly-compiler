import Riscv.Frontx.IndCmd
namespace R16
inductive T where
  | nil
  | lit (n : Nat)
  | var
  | bin (k : Nat) (a b : T)
-- one pass as a function of its own: fine
def ren : T → T
  | .nil => .nil
  | .lit n => .lit (n + 1)
  | .var => .var
  | .bin k a b => .bin k (ren a) (ren b)
-- two passes composed at the entry (`ren (ren e)`): not `f xs = g lit xs`
def twice (e : T) : T := ren (ren e)
frontx_ind_type TT := T
frontx_ind twice on TT
end R16
