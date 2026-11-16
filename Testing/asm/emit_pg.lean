/- Words and cases of the paged-array programs (`Riscv/Frontx/WpEx.lean`, NOTES section 30) for `frontx_test.py`:
`pg_<name>.words` (first line `pg 1`: byte-list result, length in `a1`), `pg_<name>.cases` (input, result bytes computed
by Lean, work bytes, `oom`): per input the work block of exactly `memoryNeeded` bytes (the pages of the run, one page for
the frame; `oom = 0`: the code returns the result) and one page less (`oom = 1`: `a1 = 2^64 - 1`, output untouched).
Run: `lake env lean Testing/asm/emit_pg.lean`. -/
import Riscv.Frontx.WpEx
open Proven Proven.WA Proven.WA.PgEx
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
/-- input lengths around the page boundaries (1024 elements per page, 1024 pages per table) -/
def lens : List Nat := [0, 1, 2, 7, 100, 1022, 1023, 1024, 1025, 1026, 2047, 2048, 2049, 3000, 4095, 4096, 4097, 20000,
  70000]
def inputs : List (List UInt8) :=
  ([[0], [255], [3, 3], [9, 200], [10], [1, 2, 3, 4, 5, 6, 7]] : List (List UInt8)) ++
  lens.map (fun n => (List.range n).map fun j => UInt8.ofNat (rnd n j % 256)) ++
  (List.range 30).map fun i =>
    let L := if i % 7 = 0 then rnd i 7 % 5000 else rnd i 99 % 90
    (List.range L).map fun j => UInt8.ofNat (match i % 4 with
      | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | _ => 255 - rnd i j % 5)
/-- the least work block (in whole pages of 8192 bytes) in which the run fits -/
def minWork (fits : ByteArray → Nat → Prop) [∀ xs L, Decidable (fits xs L)] (xs : ByteArray) : Nat :=
  ((List.range 100000).find? fun q => decide (fits xs (8192 * q))).getD 0 * 8192
instance (xs : ByteArray) (L : Nat) : Decidable (copyFits xs L) := by unfold copyFits; infer_instance
def emit (name : String) (hdr : String) (code : List (BitVec 32)) (f : ByteArray → List UInt8)
    (fits : ByteArray → Nat → Prop) [∀ xs L, Decidable (fits xs L)] : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/pg_{name}.words" (String.intercalate "\n" (hdr :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/pg_{name}.cases"
    (String.join (inputs.map fun xs =>
      let a : ByteArray := ⟨xs.toArray⟩
      let W := minWork fits a
      s!"{hx xs} {hx (f a)} {W} 0\n{hx xs} {hx (f a)} {W - 8192} 1\n{hx xs} {hx (f a)} {W - 1} 1\n"))
#eval emit "copy" "pg 1" (pgCodeA copyPg) (fun xs => encArr .ba (copyE xs)) copyFits
