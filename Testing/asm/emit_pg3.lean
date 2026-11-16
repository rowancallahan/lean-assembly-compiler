/- Words and cases of the paged front end's lean-zip ARR entries (`Riscv/Frontx/WpLeanZip3.lean`, NOTES section 35) for
`frontx_test.py`: `pgs_<name>.words` (first line `pgs 1`, `pgs 0` for a scalar result: the entry stub and the paged code, `f.pg.code`; byte-list
result, length in `a1`, status in `a0`), `pgs_<name>.cases` (input, result bytes computed by Lean, work bytes, `oom`):
per input the work block of exactly `memoryNeeded` bytes (`8192 * (pk 0 E + 1)`, `E` the run's page events computed
by `Pg.evRun`, equal to `memoryNeeded` by `memoryNeeded_eval`; `oom = 0`: the result, `a0 = 0`) and one page less
(`oom = 1`: `a0 = a1 = 2^64 - 1`, output untouched).  Run: `lake env lean Testing/asm/emit_pg3.lean`. -/
import Riscv.Frontx.WpLeanZip3
import Riscv.Frontx.WpRun
open Proven Proven.WA Proven.WA.LeanZip3 Proven.Top.Alloc
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
/-- input lengths around the page boundaries (1024 elements per page) -/
def lens : List Nat := [0, 1, 2, 7, 100, 511, 512, 513, 1022, 1023, 1024, 1025, 2047, 2048, 2049, 3000, 4095, 4096, 4097]
def inputs : List (List UInt8) :=
  ([[0], [255], [3, 3], [9, 200], [10], [1, 2, 3, 4, 5, 6, 7]] : List (List UInt8)) ++
  lens.map (fun n => (List.range n).map fun j => UInt8.ofNat (rnd n j % 256)) ++
  (List.range 32).map fun i =>
    let L := if i % 7 = 0 then rnd i 7 % 5000 else rnd i 99 % 90
    (List.range L).map fun j => UInt8.ofNat (match i % 4 with
      | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | _ => 255 - rnd i j % 5)
/-- `memoryNeeded` of the compiled program on an input, from the computed events -/
def need (q : PgProg) (xs : List UInt8) : Nat :=
  match q.p.evRun [inLocP] 9 10000000 (inArr xs, ()) with
  | some (_, E) => 8192 * (pk 0 E + 1)
  | none => 0
def emit (name : String) (q : PgProg) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/pgs_{name}.words" (String.intercalate "\n" ((if q.R matches .ar _ then "pgs 1" else "pgs 0") :: q.code.map hex8) ++ "\n")
  let mut out := ""
  for xs in inputs do
    let a : ByteArray := ⟨xs.toArray⟩
    let W := need q xs
    if W = 0 then throw (IO.userError s!"no run for an input of {xs.length} bytes")
    out := out ++ s!"{hx xs} {hx (f a)} {W} 0\n{hx xs} {hx (f a)} {W - 8192} 1\n"
  IO.FS.writeFile s!"Testing/asm/frontx-words/pgs_{name}.cases" out
  IO.println s!"{name}: {q.code.length} words, {inputs.length} inputs"
#eval emit "kraft" kraftPE.pg (fun xs => outEnc (.sc .nat) (kraftPE xs))
#eval emit "nextcodes" nextCodesPE.pg (fun xs => encArr (.arr .u32) (nextCodesPE xs))
#eval emit "longcodes" longCodesE.pg (fun xs => outEnc (.sc .nat) (longCodesE xs))
#eval emit "specnextcodes" specNextCodesE.pg (fun xs => encArr (.arr .nat) (specNextCodesE xs))
