import Riscv.Frontx.Machine
import Riscv.Frontx.RecExamples
import Riscv.Frontx.PairExamples
open Proven Proven.Frontx Proven.Frontx.Ex Proven.Frontx.Pairs
-- `SEED=s OUT=dir lake env lean --tstack=4000000 Testing/asm/fuzz4/emit.lean`
-- writes $OUT/<name>.words (slots or `rec <frame>`, then the code from the current build) and
-- $OUT/<name>.cases (input hex, result hex from executed Lean, i.e. #eval of the original function)
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def next (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407
def rnds (s : UInt64) (n : Nat) (m : Nat := 256) (off : Nat := 0) : List UInt8 × UInt64 := Id.run do
  let mut s := s; let mut o := []
  for _ in [0:n] do s := next s; o := UInt8.ofNat ((s >>> 33).toNat % m + off) :: o
  return (o, s)
/-- bytes summing to exactly `T` -/
def bytesSum (T : Nat) : List UInt8 := List.replicate (T / 255) 255 ++ [UInt8.ofNat (T % 255)]
/-- byte-list inputs; `long` : also lengths around 65521 (Lean's list recursion cannot take those: Python-only) -/
def mk (seed : Nat) (maxRand : Nat) (long : Bool) : List (List UInt8) := Id.run do
  let mut s : UInt64 := seed.toUInt64 * 0x9E3779B97F4A7C15 + 1
  let mut out : List (List UInt8) := [[]]
  for b in [0,1,2,127,128,254,255] do out := [UInt8.ofNat b] :: out
  for n in [2,3,4,5,6,7,8,9,15,16,17,63,64,65,255,256,257,258,1000,4096,5551,5552,5553,5554] do
    for b in [0, 255, 1, 254, 128] do out := List.replicate n (UInt8.ofNat b) :: out
  -- Adler: prefix sums at the modulus 65521 (a = 65519..65522, 2*65521 -1..+1, 65535, 65536), then tails
  for S in [65519, 65520, 65521, 65522, 65535, 65536, 131041, 131042, 131043] do
    for t in [[], [0], [1], [255], [0,0], [0,0,0,0,0,0,0,0], [1,1], [255,255,255], [1,0,255]] do
      out := (bytesSum S ++ t) :: out
      out := (t ++ bytesSum S) :: out
  if long then
    for n in [65520, 65521, 65522, 70000] do
      for b in [0, 255] do out := List.replicate n (UInt8.ofNat b) :: out
  for i in [0:600] do
    s := next s
    let n := (s >>> 33).toNat % (if i % 20 = 0 then maxRand else if i % 5 = 0 then 300 else 20)
    let (l, s') := match i % 4 with
      | 0 => rnds s n | 1 => rnds s n 2 | 2 => rnds s n 2 254 | _ => rnds s n 4 252
    s := s'; out := (if i % 4 = 1 then l.map (fun b => if b = 0 then 0 else 255) else l) :: out
  if long then
    for k in [0:3] do let (l, s') := rnds s (65521 + k); s := s'; out := l :: out
  return out.reverse
/-- inputs for the entry points that read the first few bytes: all lengths 0..10, boundary and random bytes -/
def mkSmall (seed : Nat) : List (List UInt8) := Id.run do
  let mut s : UInt64 := seed.toUInt64 * 0xD1B54A32D192ED03 + 7
  let mut out : List (List UInt8) := []
  for n in [0:11] do for b in [0, 255, 1, 15, 16, 17, 127, 128, 254] do out := List.replicate n (UInt8.ofNat b) :: out
  for i in [0:700] do
    s := next s; let n := (s >>> 33).toNat % (if i % 50 = 0 then 3000 else 12)
    let (l, s') := (match i % 3 with | 0 => rnds s n | 1 => rnds s n 4 | _ => rnds s n 3 126); s := s'
    out := l :: out
  return out.reverse
def emitW (dir name hdr : String) (code : List (BitVec 32)) (ins : List (List UInt8)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.writeFile s!"{dir}/{name}.words" (String.intercalate "\n" (hdr :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"{dir}/{name}.cases" (String.join (ins.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)
def run : IO Unit := do
  let seed := (← IO.getEnv "SEED").getD "1" |>.toNat!
  let dir := (← IO.getEnv "OUT").getD "/tmp/fuzz4"
  IO.FS.createDirAll dir
  let ad := mk seed 3000 true; let nt := mk seed 3000 false; let sm := mkSmall seed
  emitW dir "adlere" s!"{adlerE.slots}" adlerE.code ad (enc adlerE)
  emitW dir "adlerstatee" s!"{adlerStateE.slots}" adlerStateE.code ad (fun xs => adlerStateE.enc (adlerStateE xs))
  emitW dir "replacexe" s!"{replaceXE.slots}" replaceXE.code sm (fun xs => replaceXE.enc (replaceXE xs))
  emitW dir "fromoptione" s!"{fromOptionE.slots}" fromOptionE.code sm (enc fromOptionE)
  emitW dir "smalle" s!"{smallE.slots}" smallE.code sm (enc smallE)
  emitW dir "swape" s!"{swapE.slots}" swapE.code sm (fun xs => swapE.enc (swapE xs))
  emitW dir "addpointse" s!"{addPointsE.slots}" addPointsE.code sm (fun xs => addPointsE.enc (addPointsE xs))
  emitW dir "zeroxe" s!"{zeroXE.slots}" zeroXE.code sm (fun xs => zeroXE.enc (zeroXE xs))
  emitW dir "neste" s!"{nestE.slots}" nestE.code sm (fun xs => nestE.enc (nestE xs))
  emitW dir "nontailsumrec" "rec 88" BookList.nonTailSumRec.code nt (enc BookList.nonTailSumRec)
  emitW dir "nontaillengthrec" "rec 80" BookList.nonTailLengthRec.code nt (enc BookList.nonTailLengthRec)
  emitW dir "fiblen" "rec 96" RecEx.fibLen.code ((List.range 30).map fun n => (rnds (seed.toUInt64 + n.toUInt64) n).1) (enc RecEx.fibLen)
  IO.println s!"{ad.length} {nt.length} {sm.length} inputs"
#eval run
