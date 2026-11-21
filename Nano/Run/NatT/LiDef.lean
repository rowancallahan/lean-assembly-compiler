/- GenArm's `li t, V` (`a6` / `a7` / `a8`) as a pure word list `liL` (definitions only; from T01's Nano/Run/NatT/Li.lean,
moved here so that the image definition Nano/Run/NatImg.lean and the run lemma `n_li` share them). -/
import Nano.Run.A64SemN
namespace JT

/-- chunk `j` of `V` -/
def chk (V j : Nat) : Nat := V / 2 ^ (16 * j) % 65536

/-- the `movk` words for the chunks `j ..` (`n` of them) that differ from the fill `e` -/
def chain (t V e : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, j => if chk V j = e then chain t V e n (j + 1) else ArmEnc.movk t (chk V j) j :: chain t V e n (j + 1)

/-- until the first chunk that differs from `e`: skipped; then `movz` (fill 0) / `movn` (fill 0xFFFF) with `lsl 16j`, then `chain` -/
def walk0 (t V e : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, j => if chk V j = e then walk0 t V e n (j + 1) else
      (if e = 0 then ArmEnc.movzH t (chk V j) j else ArmEnc.movn t (65535 - chk V j) j) :: chain t V e n (j + 1)

/-- how many of the 4 chunks equal `e` (`a8`) -/
def cnt (V e : Nat) : Nat := ((List.range 4).filter (fun j => chk V j = e)).length

/-- GenArm's `li t, V` (`a6`) for `V < 2^64` -/
def liL (t V : Nat) : List Nat :=
  if V < 65536 then [ArmEnc.movz t V]
  else if 2 ^ 64 - 1 - V < 65536 then [ArmEnc.movn t (2 ^ 64 - 1 - V) 0]
  else if cnt V 0 < cnt V 65535 then walk0 t V 65535 4 0 else walk0 t V 0 4 0

end JT
