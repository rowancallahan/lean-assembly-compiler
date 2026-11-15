/- TINYSELF2, step 1: the source program is a user inductive (an expression tree), the output a user inductive
(a stack-machine instruction list); both go through `frontx_ind` (NOTES §17–21), not bytes.
Binary operators are ONE constructor `bin k a b` (k = 0 add, 1 sub, 2 xor): one constructor per operator does not
fit the plain back end (TINYSELF2.md, failure F1). -/
import Riscv.Frontx.IndCmd

namespace Proven.Frontx.Tiny2S1

inductive Ex where
  | lit (n : UInt64)
  | var
  | bin (k : UInt64) (a b : Ex)

inductive Ins where
  | nil
  | push (n : UInt64) (rest : Ins)
  | ldx (rest : Ins)
  | op (k : UInt64) (rest : Ins)

def Ins.app : Ins → Ins → Ins
  | .nil, ys => ys
  | .push n r, ys => .push n (r.app ys)
  | .ldx r, ys => .ldx (r.app ys)
  | .op k r, ys => .op k (r.app ys)

def comp : Ex → Ins
  | .lit n => .push n .nil
  | .var => .ldx .nil
  | .bin k a b => (comp a).app ((comp b).app (.op k .nil))

def apply (k a b : UInt64) : UInt64 := if k == 0 then a + b else if k == 1 then a - b else a ^^^ b

def Ex.eval (x : UInt64) : Ex → UInt64
  | .lit n => n
  | .var => x
  | .bin k a b => apply k (a.eval x) (b.eval x)

/-- reference stack machine -/
def Ins.run (x : UInt64) : Ins → List UInt64 → UInt64
  | .nil, s => s.headD 0
  | .push n r, s => r.run x (n :: s)
  | .ldx r, s => r.run x (x :: s)
  | .op k r, s => r.run x (apply k (s.getD 1 0) (s.getD 0 0) :: s.drop 2)

frontx_ind_type ExT := Ex
frontx_ind_type InsT := Ins
frontx_ind comp on ExT using InsT

end Proven.Frontx.Tiny2S1
