-- trivia: comments, docstrings, attributes, namespace/section/open/end and `private` (SYNTAX_EXP.md, construct 1).
-- ROT13 on ASCII letters, every other byte copied.
-- input  (hex): 48 65 6c 6c 6f 2c 20 6e 61 6e 6f 21
-- expect (hex): 55 72 79 79 62 2c 20 61 6e 61 62 21
/-! Module docstring.  /- a nested comment -/ is still inside it. -/
namespace Demo
open Nat
section Letters

/-- rotate a letter in the range [b, b + 26) by 13 -/
@[inline] private def r (c b : UInt64) : UInt64 :=
  if c - b < 13 then c + 13 else c - 13 -- the second half wraps back

@[simp, inline]
def u (c : UInt64) : UInt64 := if 96 < c then if c < 123 then r c 97 else c
  else if 64 < c then if c < 91 then r c 65 else c else c

end Letters

/- the loop: one byte per fuel step -/
def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => o
  | n + 1, x, i, o => f n x (i + 1) (put o (u (rd x i))) --  -/ in a line comment is ignored
def m (x : List UInt8) : List UInt8 := f (len' x) x 0 []
end Demo
