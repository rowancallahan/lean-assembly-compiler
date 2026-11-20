/- FUZZ10 reference: executes the Lean entries (the same `f` the emitters in Testing/asm/emit_{int,struct,wa,frontx}.lean
apply to the same inputs) on stdin lines `name hex` (`-` = empty input), prints the result bytes as hex (`-` = empty).
Run: lean --run Testing/asm/fuzz10/ref10.lean < in.txt -/
import Legacy.Riscv.Frontx.IntExamples
import Legacy.Riscv.Frontx.WaInt
import Legacy.Riscv.Frontx.StructExamples
import Legacy.Riscv.Frontx.WaStruct
import Legacy.Riscv.Frontx.MonadExamples
import Legacy.Riscv.Frontx.MixHash
import Legacy.Riscv.Frontx.WaMul
open Proven Proven.Frontx Proven.Frontx.IntEx
open Proven.Frontx.Mon
open Proven.WA.MixHash
open Proven.Frontx.Structs Proven.WA Proven.WA.Struct

def enc {β : Type} [Frontx.Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Frontx.Res.enc (f xs)
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def nib (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
partial def unhexL (acc : Array UInt8) : List Char → Array UInt8
  | a :: b :: r => unhexL (acc.push (UInt8.ofNat (nib a * 16 + nib b))) r
  | _ => acc
def unhex (s : String) : Array UInt8 := if s == "-" then #[] else unhexL #[] s.toList

def run (name : String) (xs : ByteArray) : List UInt8 :=
  match name with
  | "int_clamp" => enc clampE xs | "int_inrange" => enc inRangeE xs | "int_ofnat" => enc ofNatE xs
  | "int_mul" => enc mulE xs | "int_floor" => enc floorE xs | "int_ceil" => enc ceilE xs
  | "int_round" => enc roundE xs | "int_abs" => enc absE xs | "int_min" => enc minE xs
  | "int_max" => enc maxE xs | "int_scale16" => enc scale16E xs | "int_clamplin" => enc clampLinE xs
  | "int_lininrange" => enc linInRangeE xs | "int_clampix" => enc clampIxE xs | "int_round32" => enc round32E xs
  | "int_fitsi16" => enc fitsI16E xs | "int_insidew" => enc insideWE xs | "int_norm2" => enc norm2E xs
  | "int_clampto" => enc clampToE xs | "int_morphceil" => enc morphCeilE xs
  | "wa_int_iops" => Frontx.Res.enc (WA.IntOps.iopsE xs)
  | "wa_int_icmp" => Frontx.Res.enc (WA.IntOps.icmpE xs)
  | "wa_int_fxrounds" => Frontx.Res.enc (WA.IntOps.fxRoundsE xs)
  | "wa_int_sumdev" => Frontx.Res.enc (WA.IntOps.sumDevE xs)
  | "st_rgba" => rgbaE.enc (rgbaE xs) | "st_hdr" => hdrE.enc (hdrE xs)
  | "st_rgbag" => enc rgbaGE xs | "st_interlace" => enc interlaceE xs | "st_canvash" => enc canvasHE xs
  | "st_compoundvalid" => enc compoundValidE xs | "st_setlig" => setLigE.enc (setLigE xs)
  | "st_lignumcomps" => enc ligNumCompsE xs | "st_isignorable" => enc isIgnorableE xs
  | "st_rgbahdr" => rgbaHdrE.enc (rgbaHdrE xs)
  | "wa_entryat" => enc entryAtE xs | "wa_lenat" => enc lenAtE xs | "wa_symat" => enc symAtE xs
  | "wa_mixhash" => Frontx.Res.enc (mixHashE xs)
  | "mon_countgt3" => countGt3.enc (countGt3 xs)
  | "mon_countnotgt3" => countNotGt3.enc (countNotGt3 xs)
  | "mon_countgt3exc" => countGt3Exc.enc (countGt3Exc xs)
  | "mon_sumnze" => sumNZE.enc (sumNZE xs)
  | "mon_countzerose" => countZerosE.enc (countZerosE xs)
  | "mon_countabovere" => countAboveRE.enc (countAboveRE xs)
  | "mon_maxste" => maxStE.enc (maxStE xs)
  | "mon_splite" => splitE.enc (splitE xs)
  | "mon_firstbige" => firstBigE.enc (firstBigE xs)
  | "mon_trysube" => trySubE.enc (trySubE xs)
  | "mon_desfindgt3" => enc desFindGt3 xs | "mon_loopfindgt3" => enc loopFindGt3 xs
  | "mon_contfindgt3" => enc contFindGt3 xs | "mon_loopcountsp" => enc loopCountSp xs
  | "mon_twoe" => enc twoE xs | "mon_threee" => enc threeE xs | "mon_sixe" => enc sixE xs
  | _ => panic! s!"unknown entry {name}"

def fzMain : IO Unit := do
  let inp ← IO.FS.readFile ((← IO.getEnv "FZ_IN").getD (panic! "FZ_IN unset"))
  let out ← IO.FS.Handle.mk ((← IO.getEnv "FZ_OUT").getD (panic! "FZ_OUT unset")) .write
  for line in inp.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " " with
    | [name, x] => out.putStrLn (hx (run name ⟨unhex x⟩))
    | _ => panic! s!"bad line {line}"
  out.flush
#eval fzMain
