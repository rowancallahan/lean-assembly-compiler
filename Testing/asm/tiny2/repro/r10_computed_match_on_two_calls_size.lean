/- TINYSELF2, step 4: a second pass, constant folding, as its own function over the step-3 source (opcodes ×16).
`fold` is compiled by `frontx_ind` as a program of its own (entry `fold`); the pass pipeline `comp (fold e)` as ONE
entry does not go through (F11, see `TinyS4Pipe.lean`), so the two binaries are chained by the test harness. -/
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
  | .bin k a b =>
    match fold a, fold b with
    | .lit x, .lit y => .lit (x + y)
    | a', b' => .bin k a' b'

frontx_ind_type TT := T
set_option maxHeartbeats 0 in
frontx_ind fold on TT

end R
