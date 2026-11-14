import Riscv.Direct.MemCompiler
open Proven
def hex (w : Nat) : String := String.ofList (Nat.toDigits 16 w)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def edge : List Nat := [0, 1, 63, 64, 2^63 - 1, 2^63, 2^64 - 1]
def v (i : Fin 4) : Exp := .var i
def ins (n : Nat) : List (List Nat) :=
  edge.flatMap (fun a => edge.map fun b => [a, b, rnd a b, rnd b a]) ++
  (List.range n).map fun i => (List.range 4).map (rnd (i + 7))
def cases : List (String × Exp) := [
  ("add", .bin .add (v 0) (v 1)),
  ("const", .const 0x0123456789abcdef),
  ("shl_sub", .bin .sub (.bin .shl (v 0) (v 1)) (v 2)),
  ("ite_ult", .ite (.bin .ult (v 0) (v 1)) (v 2) (.bin .xor (v 3) (.const 0xff00ff00ff00ff00))),
  ("eq_ashr", .bin .or (.bin .eq (v 0) (v 1)) (.bin .ashr (v 2) (v 3)))]
#eval show IO Unit from do
  for (name, e) in cases do
    assert! e.depth < 11
    IO.println s!"case {name}"
    IO.println s!"rv {" ".intercalate ((compileStore e).map (hex ·.toNat))}"
    for a in ins 50 do
      let env : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 (a[i.val]!)
      IO.println s!"t {" ".intercalate (a.map hex)} {hex (e.denote env).toNat}"
