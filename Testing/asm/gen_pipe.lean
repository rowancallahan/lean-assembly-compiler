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
def isSort : Stage → Bool | .sort => true | _ => false
/-- 1..9 stages, at most one `sort` (owner's constraint while the pipe sort is the quadratic insertion sort) -/
def genPipe (maxSt : Nat) : G Pipe := do
  let n := 1 + (← below maxSt)
  let mut p : Pipe := []
  for _ in [0:n] do
    let mut st ← stage
    while isSort st && p.any isSort do st ← stage
    p := p ++ [st]
  return p

def hexb (bs : List UInt8) : String := if bs.isEmpty then "-" else
  String.join (bs.map fun b => let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s)
def hex32 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s

def lens : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129, 200, 255, 256, 257]
/-- input of a random shape; with `cap` (pipes containing a sort) the length is capped at 128 and `shrunk` says it was -/
def genInput (cap : Bool) : G (List UInt8 × Bool) := do
  let L ← pick lens
  let r ← below 4
  let L ← if r == 0 then below 40 else pure L
  let shrunk := cap && L > 128
  let L := if shrunk then 128 else L
  let xs ← genInput' L
  return (xs, shrunk)
where genInput' (L : Nat) : G (List UInt8) := do
  match ← below 5 with
  | 0 => return List.replicate L (← byte)
  | 1 => return ((List.range L).map fun i => (i * 7 % 256).toUInt8)
  | 2 => return ((List.range L).map fun i => (255 - i % 256).toUInt8)
  | _ => return (← (List.range L).mapM fun _ => byte)

def bucket (n : Nat) : String :=
  if n ≤ 50 then "<=50" else if n ≤ 100 then "<=100" else if n ≤ 200 then "<=200" else if n ≤ 400 then "<=400" else if n ≤ 800 then "<=800" else ">800"
def bump (a : Array (String × Nat)) (k : String) : Array (String × Nat) :=
  match a.findIdx? (·.1 == k) with
  | some i => a.modify i fun (k, n) => (k, n + 1)
  | none => a.push (k, 1)
def showStat (a : Array (String × Nat)) : String := ", ".intercalate (a.toList.map fun (k, n) => s!"{k}:{n}")

def genMain : IO Unit := do
  let env := fun v => do return (← IO.getEnv v).get!
  let seed ← env "SEED"; let np ← env "NPROG"; let k ← env "K"
  let maxSt := ((← IO.getEnv "MAXST").bind String.toNat?).getD 9
  let mut s : UInt64 := seed.toNat!.toUInt64
  let mut made := 0; let mut tried := 0; let mut shrunk := 0
  let mut rej : Array (String × Nat) := #[]; let mut hist : Array (String × Nat) := #[]; let mut stg : Array (String × Nat) := #[]
  while made < np.toNat! do
    tried := tried + 1
    let (p, s') := (genPipe maxSt).run s
    s := s'
    match compileP p with
    | .error m => rej := bump rej (((m.splitOn "\n").head!.take 90).toString); continue
    | .ok code =>
      hist := bump hist (bucket code.length); stg := bump stg (toString p.length)
      IO.println s!"prog pipe_{seed}_{made}"
      IO.println "kind blk"
      IO.println s!"words {" ".intercalate (code.map hex32)}"
      IO.println "a2 junk"
      IO.println "frame 0"
      IO.println s!"# {(repr p).pretty 100000 |>.replace "\n" " "}"
      for _ in [0:k.toNat!] do
        let ((xs, sh), s') := (genInput (p.any isSort)).run s
        s := s'
        if sh then shrunk := shrunk + 1
        IO.println s!"in i={hexb xs} e={hexb (p.denote xs)} sp={Pipe.space p xs.length} ss=0 mis=0"
      made := made + 1
  IO.println s!"# STAT pipe: accepted {made} of {tried} generated; code words {showStat hist}; stages {showStat stg}; inputs shrunk to 128 (sort): {shrunk}"
  IO.println s!"# STAT pipe rejected: {showStat rej}"
#eval genMain
