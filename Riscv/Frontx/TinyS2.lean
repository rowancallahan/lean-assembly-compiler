/- TINYSELF2, step 2: comparisons, conditionals, assignment, sequencing, compiled to a stack machine.
Findings that shaped it (TINYSELF2.md): `comp` may have at most about four constructor arms with a call (F1), so the
source AND the target are encoded in ONE four-constructor type `T = nil | lit n | var | bin k a b` (F6: one type);
difference lists `comp e K` (code of `e` then `K`), no `append`; call arguments contain no literal scalar and no
call result (F2, F3).  Source `bin k a b`: k = 0 add, 1 sub, 2 xor, 3 ult, 4 eq, 5 seq, 6 set (b unused),
7 cnd (a = alt node, b = condition), 8 alt t e.  Target instruction = `bin k rest imm` (k = 0..4 binary, 6 store x,
7 select (pop c, e, t; push if c ≠ 0 then t else e), 9 push imm (`imm = lit n`), 10 load x), list ends in `nil`.
target `op 5` (seq) = nip (drop the element under the top), `op 8` (alt) = no-op: the instruction is always emitted, an `if`
around it breaks the `sem` proof (F9).
`if` is a strict select (t, e, c evaluated, no jumps), since jumps need `len` (F4, F5, F7). -/
import Riscv.Frontx.IndCmd

namespace Proven.Frontx.Tiny2S2

inductive T where
  | nil
  | lit (n : UInt64)
  | var
  | bin (k : UInt64) (a b : T)
  | op (k : UInt64) (rest : T)   -- target instruction without immediate

def comp : T → T → T
  | .nil, K => K
  | .lit n, K => .bin 9 K (.lit n)
  | .var, K => .bin 10 K .nil
  | .op k r, K => .op k r
  | .bin k a b, K => comp a (comp b (.op k K))

def compile (e : T) : T := comp e .nil

/-! reference semantics: (value, x) -/
def apply (k a b : UInt64) : UInt64 :=
  if k == 0 then a + b else if k == 1 then a - b else if k == 2 then a ^^^ b else if k == 3 then (if a < b then 1 else 0)
  else (if a == b then 1 else 0)

def ev : T → UInt64 → UInt64 × UInt64
  | .lit n, x => (n, x)
  | .var, x => (x, x)
  | .bin k a b, x =>
    if k < 5 then let (va, x1) := ev a x; let (vb, x2) := ev b x1; (apply k va vb, x2)
    else if k == 5 then let (_, x1) := ev a x; ev b x1
    else if k == 6 then let (v, _) := ev a x; (v, v)
    else match a with
      | .bin 8 t e => let (vt, x1) := ev t x; let (ve, x2) := ev e x1; let (vc, x3) := ev b x2
                      (if vc != 0 then vt else ve, x3)
      | _ => (0, x)
  | _, x => (0, x)
def eval (e : T) (x : UInt64) : UInt64 := (ev e x).1

/-- run target code on a stack -/
def run : T → UInt64 → List UInt64 → UInt64
  | .op k r, x, s =>
    if k < 5 then run r x (apply k (s.getD 1 0) (s.getD 0 0) :: s.drop 2)
    else if k == 6 then run r (s.headD 0) s
    else if k == 5 then run r x (s.headD 0 :: s.drop 2)
    else if k == 8 then run r x s
    else run r x ((if s.getD 0 0 != 0 then s.getD 2 0 else s.getD 1 0) :: s.drop 3)
  | .bin k r imm, x, s =>
    if k == 9 then (match imm with | .lit n => run r x (n :: s) | _ => 0)
    else run r x (x :: s)
  | _, _, s => s.headD 0

frontx_ind_type TT := T
frontx_ind compile on TT

end Proven.Frontx.Tiny2S2
