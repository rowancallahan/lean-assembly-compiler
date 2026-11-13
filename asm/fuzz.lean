/- Random differential testing generator. usage: SEED=1 NCASES=100 K=100 lake env lean asm/fuzz.lean > out.txt
   (the Sail model already defines a root `main`, so this uses #eval + env vars)
   Emits the format read by asm/triple.py (plus an `exp` line per case). Reproducible from SEED. -/
import Proven.CompilerArm
import Proven.Reify
open Proven

abbrev G := StateM UInt64
def next : G UInt64 := modifyGet fun (s : UInt64) =>   -- splitmix64
  let s : UInt64 := s + 0x9E3779B97F4A7C15
  let z : UInt64 := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z : UInt64 := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)
def below (n : Nat) : G Nat := return (← next).toNat % n

def edge : Array Nat := #[0, 1, 2, 3, 2^63, 2^63 - 1, 2^64 - 1, 2^64 - 2, 2^32, 2^32 - 1, 0xFF, 0xFFF, 0x800, 0x7FF, 2^63 + 1]
def word : G Nat := do
  if (← below 3) == 0 then return edge[← below edge.size]! else
  -- uniform 64-bit
  return (← next).toNat
def Op.all : Array Op := #[.add, .sub, .and, .or, .xor]
instance : Inhabited Op := ⟨.add⟩
/-- all constructors of `Exp` the generator knows about; extend here when `Exp` grows -/
def genExp : Nat → G Exp
  | 0 => do if (← below 4) == 0 then return .const (BitVec.ofNat 64 (← word)) else return .var (Fin.ofNat 4 (← below 4))
  | f + 1 => do
    if (← below 5) == 0 then genExp 0 else
    return .bin Op.all[← below Op.all.size]! (← genExp f) (← genExp f)
instance : Inhabited Exp := ⟨.const 0⟩
partial def genOk : G Exp := do
  let e ← genExp (← below 6)
  if e.depth < 5 then return e else genOk
def hex (w : Nat) : String := String.ofList (Nat.toDigits 16 w)

def fuzz : IO Unit := do
  let env := fun v => do return (← IO.getEnv v).get!
  let seed ← env "SEED"; let n ← env "NCASES"; let k ← env "K"
  let mut s : UInt64 := seed.toNat!.toUInt64
  for i in [0:n.toNat!] do
    let (e, s') := genOk.run s
    s := s'
    assert! e.depth < 5
    IO.println s!"case f{seed}_{i}"
    IO.println s!"exp {(repr e).pretty 100000 |>.replace "\n" " "}"
    IO.println s!"rv {" ".intercalate ((compile e).map (hex ·.toNat))}"
    IO.println s!"arm {" ".intercalate ((Arm.compile e).map (hex ·.toNat))}"
    for _ in [0:k.toNat!] do
      let (a, s') := (do let a ← word; let b ← word; let c ← word; let d ← word; pure [a, b, c, d] : G (List Nat)).run s
      s := s'
      let env : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 (a[i.val]!)
      IO.println s!"t {" ".intercalate (a.map hex)} {hex (e.denote env).toNat}"

#eval fuzz
