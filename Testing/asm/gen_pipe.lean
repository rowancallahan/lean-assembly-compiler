/- Generator (a): random `Pipe` values through `compileP`, inputs of many shapes, expected = `Pipe.denote`.
   usage: SEED=1 NPROG=50 K=24 lake env lean Testing/asm/gen_pipe.lean > cases.txt ; python3 Testing/asm/fuzz_run.py cases.txt 4
   (the Sail model defines a root `main`, so this is an `#eval` driven by env vars) -/
import Compiler.Front.PipeMachine
open Proven

abbrev G := StateM UInt64
def next : G UInt64 := modifyGet fun (s : UInt64) =>
  let s : UInt64 := s + 0x9E3779B97F4A7C15
  let z : UInt64 := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z : UInt64 := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)
def below (n : Nat) : G Nat := return (← next).toNat % n
def pick {α} [Inhabited α] (a : Array α) : G α := do return a[← below a.size]!
def byte : G UInt8 := do
  if (← below 3) == 0 then pick #[0, 1, 2, 3, 9, 10, 0x7f, 0x80, 0xfe, 0xff] else return (← below 256).toUInt8
def word : G Nat := do
  if (← below 3) == 0 then pick #[0, 1, 2, 5, 63, 64, 65, 2^63, 2^64 - 1, 2^32] else return (← next).toNat
instance : Inhabited BOp := ⟨.add⟩
instance : Inhabited BCmp := ⟨.lt⟩
instance : Inhabited Op := ⟨.add⟩
instance : Inhabited BExp := ⟨.x⟩
instance : Inhabited WExp := ⟨.x⟩

def bexp (acc : Bool) : Nat → G BExp
  | 0 => do
    match ← below 3 with
    | 0 => return .x
    | 1 => return .lit (← byte)
    | _ => if acc then return .acc else return .x
  | f + 1 => do
    match ← below 6 with
    | 0 => bexp acc 0
    | 1 | 2 | 3 => return .bin (← pick #[BOp.add, .sub, .and, .or, .xor]) (← bexp acc f) (← bexp acc f)
    | _ => return .ite (← pick #[BCmp.lt, .le, .eq, .ne]) (← bexp acc (f / 2)) (← bexp acc (f / 2)) (← bexp acc f) (← bexp acc f)
def wexp : Nat → G WExp
  | 0 => do
    match ← below 3 with
    | 0 => return .x
    | 1 => return .const (BitVec.ofNat 64 (← word))
    | _ => return .acc
  | f + 1 => do
    match ← below 6 with
    | 0 => wexp 0
    | 1 => return .ite (← wexp (f / 2)) (← wexp f) (← wexp f)
    | _ => return .bin (← pick #[Op.add, .sub, .and, .or, .xor, .shl, .lshr, .ashr, .ult, .slt, .eq]) (← wexp f) (← wexp f)
def count : G Nat := pick #[0, 1, 2, 3, 4, 5, 7, 8, 16, 31, 100, 2^63, 2^64 - 1] >>= fun c =>
  do if (← below 3) == 0 then return (← below 20) else return c
instance : Inhabited Stage := ⟨.reverse⟩
def stage : G Stage := do
  match ← below 11 with
  | 0 | 1 | 2 => return .map (← bexp false (← below 4))
  | 3 => return .take (← count)
  | 4 => return .drop (← count)
  | 5 | 6 => return .reverse
  | 7 | 8 => return .sort
  | 9 => return .fold (← bexp true (← below 4)) (← byte)
  | _ => return .foldW (← wexp (← below 4)) (BitVec.ofNat 64 (← word))
def genPipe : G Pipe := do
  let n := 1 + (← below 5)
  let mut p : Pipe := []
  for _ in [0:n] do p := p ++ [← stage]
  return p

def hexb (bs : List UInt8) : String := if bs.isEmpty then "-" else
  String.join (bs.map fun b => let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s)
def hex32 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s

def lens : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129]
def genInput : G (List UInt8) := do
  let L ← pick lens
  let L := if (← below 4) == 0 then (← below 40) else L
  match ← below 5 with
  | 0 => return List.replicate L (← byte)
  | 1 => return ((List.range L).map fun i => (i * 7 % 256).toUInt8)
  | 2 => return ((List.range L).map fun i => (255 - i % 256).toUInt8)
  | _ => return (← (List.range L).mapM fun _ => byte)

def gen : IO Unit := do
  let env := fun v => do return (← IO.getEnv v).get!
  let seed ← env "SEED"; let np ← env "NPROG"; let k ← env "K"
  let mut s : UInt64 := seed.toNat!.toUInt64
  let mut made := 0; let mut tried := 0
  while made < np.toNat! do
    tried := tried + 1
    let (p, s') := genPipe.run s
    s := s'
    match compileP p with
    | .error _ => continue
    | .ok code =>
      IO.println s!"prog pipe_{seed}_{made}"
      IO.println "kind blk"
      IO.println s!"words {" ".intercalate (code.map hex32)}"
      IO.println "a2 junk"
      IO.println "frame 0"
      IO.println s!"# {(repr p).pretty 100000 |>.replace "\n" " "}"
      for _ in [0:k.toNat!] do
        let (xs, s') := genInput.run s
        s := s'
        IO.println s!"in i={hexb xs} e={hexb (p.denote xs)} sp={Pipe.space p xs.length} ss=0 mis=0"
      made := made + 1
  IO.eprintln s!"pipes: {made} accepted of {tried} generated"
#eval gen
