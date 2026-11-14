-- as triple.lean, but the RV64 code is the interface route `Mach.Riscv.rv.code (Mach.mcompile e)` (asserted equal to `compile e`)
import Proven.CompilerArm
import Proven.Reify
import Proven.Mach.RiscvExp
open Proven
def hex (w : Nat) : String := String.ofList (Nat.toDigits 16 w)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def edge : List Nat := [0, 1, 2, 3, 63, 64, 65, 127, 128, 2^31, 2^32 - 1, 2^62, 2^63 - 1, 2^63, 2^63 + 1, 2^64 - 2, 2^64 - 1]
def amts : List Nat := [0, 1, 2, 31, 32, 63, 64, 65, 127, 128, 2^63, 2^63 + 5, 2^64 - 1, 2^64 - 64]
/-- all edge pairs in (a0, a1), then random inputs; `f` post-processes a random row -/
def pairs (xs ys : List Nat) (n : Nat) (f : List Nat → List Nat := id) : List (List Nat) :=
  xs.flatMap (fun a => ys.map fun b => [a, b, rnd a b, rnd b a]) ++
  (List.range n).map fun i => f ((List.range 4).map (rnd (i + 7)))
def v (i : Fin 4) : Exp := .var i
/-- right-nested chain of depth `n`: every level needs one more temporary -/
def chain : Nat → Exp
  | 0 => .bin .add (v 0) (.const 0x123456789abcdef)
  | n + 1 => .bin (([Op.xor, .shl, .sub, .lshr, .ult, .ashr, .slt, .eq, .or, .and, .add][n % 11]?).getD .add) (v ⟨n % 4, by omega⟩) (chain n)
def deepIte : Exp := .ite (v 0) (chain 6) (.ite (v 1) (chain 5) (chain 4))
def cases : List (String × Exp × List (List Nat)) := [
  ("one_plus_one", .bin .add (.const 1) (.const 1), [[0,0,0,0]]),
  ("n_plus_n", .bin .add (v 0) (v 0), (List.range 100).map fun n => [n,0,0,0]),
  ("n_plus_m", .bin .add (v 0) (v 1), (List.range 100).flatMap fun n => (List.range 100).map fun m => [n,m,0,0]),
  ("demo", demoE, (List.range 300).map fun i => (List.range 4).map fun j => rnd i j),
  ("shl", .bin .shl (v 0) (v 1), pairs edge amts 300),
  ("lshr", .bin .lshr (v 0) (v 1), pairs edge amts 300),
  ("ashr", .bin .ashr (v 0) (v 1), pairs edge amts 300),
  ("shl_const", .bin .shl (v 0) (.const 65), pairs edge [0] 200),
  ("ult", .bin .ult (v 0) (v 1), pairs edge edge 200),
  ("slt", .bin .slt (v 0) (v 1), pairs edge edge 200),
  ("eq", .bin .eq (v 0) (v 1), pairs edge edge 200 fun r => if r[0]! % 3 = 0 then [r[0]!, r[0]!, r[2]!, r[3]!] else r),
  ("eq_const", .bin .eq (v 0) (.const (2^63)), pairs edge [0] 200),
  ("ite", .ite (v 0) (v 1) (v 2), pairs edge edge 200 fun r => if r[1]! % 2 = 0 then 0 :: r.tail else r),
  ("ite_ult", .ite (.bin .ult (v 0) (v 1)) (v 2) (v 3), pairs edge edge 200),
  ("ite_nested", .ite (.bin .sub (v 0) (v 1)) (.ite (v 2) (.bin .slt (v 0) (v 3)) (.bin .ashr (v 3) (v 2)))
      (.bin .shl (v 2) (.bin .lshr (v 0) (v 3))), pairs edge edge 200 fun r => if r[0]! % 2 = 0 then r[1]! :: r.tail else r),
  ("demo2", demo2E, pairs edge amts 300),
  ("chain9_depth10", chain 9, pairs edge edge 300),
  ("deep_ite", deepIte, pairs edge edge 300)]
#eval show IO Unit from do
  for (name, e, ins) in cases do
    assert! e.depth < 11
    IO.println s!"case {name}"
    let mc := Mach.Riscv.rv.code (Mach.mcompile e)
    assert! mc == compile e
    IO.println s!"rv {" ".intercalate (mc.map (hex ·.toNat))}"
    IO.println s!"arm {" ".intercalate ((Arm.compile e).map (hex ·.toNat))}"
    for a in ins do
      let env : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 (a[i.val]!)
      IO.println s!"t {" ".intercalate (a.map hex)} {hex (e.denote env).toNat}"
