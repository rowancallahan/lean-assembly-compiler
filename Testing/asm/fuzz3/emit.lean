import Riscv.Frontx.Machine
open Proven Proven.Frontx Proven.Frontx.Ex Proven.Frontx.BookOut
-- `SEED=s lake env lean Testing/asm/fuzz3/emit.lean`; writes $OUT/<name>.cases (input hex, Lean result hex)
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def next (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def rnds (s : UInt64) (n : Nat) : List UInt8 × UInt64 := Id.run do
  let mut s := s; let mut o := []
  for _ in [0:n] do s := next s; o := UInt8.ofNat ((s >>> 33).toNat % 256) :: o
  return (o, s)
def mk (seed : Nat) : List (List UInt8) := Id.run do
  let mut s : UInt64 := seed.toUInt64 * 0x9E3779B97F4A7C15 + 1
  let mut out : List (List UInt8) := [[]]
  -- constants: lengths around the thresholds 0..8, all-0x00, all-0xFF, boundary bytes 3/4
  for n in [1,2,3,4,5,6,7,8,9,16,63,64,65,255,256,1000,4096] do
    for b in [0, 255, 3, 4, 5, 128, 127] do out := List.replicate n (UInt8.ofNat b) :: out
  for b in [0,1,2,3,4,5,6,7,8,9,10,127,128,254,255] do out := [b] :: out
  -- random bytes, random lengths; small-alphabet bytes around the filter threshold
  for i in [0:500] do
    s := next s; let n := (s >>> 33).toNat % (if i % 25 = 0 then 3000 else 40)
    let (l, s') := rnds s n; s := s'
    out := (if i % 3 = 0 then l.map (· % 8) else l) :: out
  -- max allowed length (2^20)
  out := List.replicate (2^20) 0 :: List.replicate (2^20) 255 :: ((rnds s (2^20)).1.map (· % 8)) :: out
  return out.reverse
def emit (dir name : String) (ins : List (List UInt8)) (f : ByteArray → List UInt8) : IO Unit :=
  IO.FS.writeFile s!"{dir}/{name}.cases" (String.join (ins.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)
#eval do
  let seed := (← IO.getEnv "SEED").getD "1" |>.toNat!
  let dir := (← IO.getEnv "OUT").getD "/tmp/fuzz3"
  IO.FS.createDirAll dir
  let ins := mk seed
  emit dir "take5" ins take5; emit dir "drop5" ins drop5; emit dir "matchdrop3" ins matchDrop3
  emit dir "filterall" ins filterAll; emit dir "inceach" ins incEach; emit dir "twice" ins twice
  emit dir "headof" ins (enc headOf); emit dir "finalof" ins (enc finalOf); emit dir "findfirstgt3" ins (enc findFirstGt3)
  emit dir "tailsum" ins (enc BookList.tailSum); emit dir "nontailsum" ins (enc BookList.nonTailSum)
  emit dir "taillength" ins (enc BookList.tailLength); emit dir "booklength" ins (enc BookList.bookLength)
  IO.println s!"{ins.length} inputs"
