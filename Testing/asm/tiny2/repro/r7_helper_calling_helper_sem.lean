import Riscv.Frontx.IndCmd
namespace R
inductive T where
  | lit (n : UInt64)
  | alt (t e : T)
  | nil
  | push (n : UInt64) (rest : T)
  | jz (n : UInt64) (rest : T)
  | jmp (n : UInt64) (rest : T)
def len : T → UInt64
  | .lit _ => 0
  | .alt _ _ => 0
  | .nil => 0
  | .push _ r => len r + 1
  | .jz _ r => len r + 1
  | .jmp _ r => len r + 1
def wrap : T → UInt64 → T → T
  | E, m, K => if m == 0 then .jmp (len E - len K) E else .jz (len E - len K) E
def comp : T → UInt64 → T → T
  | .lit n, _, K => .push n K
  | .alt t e, w, K =>
    let E := comp e w K
    let T := comp t w (wrap E 0 K)
    wrap T 1 E
  | .nil, _, K => K
  | .push n r, _, K => .push n r
  | .jz n r, _, K => .jz n r
  | .jmp n r, _, K => .jmp n r
def compile (e : T) : T := comp e 0 .nil
frontx_ind_type TT := T
frontx_ind compile on TT
end R
