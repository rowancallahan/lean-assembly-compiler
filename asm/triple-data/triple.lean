import Proven.CompilerArm
import Proven.Reify
open Proven
def hex (w : Nat) : String := String.ofList (Nat.toDigits 16 w)
def cases : List (String × Exp × List (List Nat)) := [
  ("one_plus_one", .bin .add (.const 1) (.const 1), [[0,0,0,0]]),
  ("n_plus_n", .bin .add (.var 0) (.var 0), (List.range 100).map fun n => [n,0,0,0]),
  ("n_plus_m", .bin .add (.var 0) (.var 1), (List.range 100).flatMap fun n => (List.range 100).map fun m => [n,m,0,0]),
  ("demo", demoE, (List.range 300).map fun i => (List.range 4).map fun j => (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64)]
#eval show IO Unit from do
  for (name, e, ins) in cases do
    assert! e.depth < 5
    IO.println s!"case {name}"
    IO.println s!"rv {" ".intercalate ((compile e).map (hex ·.toNat))}"
    IO.println s!"arm {" ".intercalate ((Arm.compile e).map (hex ·.toNat))}"
    for a in ins do
      let env : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 (a[i.val]!)
      IO.println s!"t {" ".intercalate (a.map hex)} {hex (e.denote env).toNat}"
