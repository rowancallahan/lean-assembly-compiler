import Nano.Run.NatEnc
import Nano.Codegen.JArm
/- spec_cmp.lean F...: for each file F (Gen's RISC-V code bytes): decode the words to J (checked: `encG` gives the
words back), then `natEncJ Cj` (the spec) must equal the translator `C.e45` byte for byte, or both reject. -/
open CallProbe
def sx (v w : Nat) : Int := if v < 2 ^ (w - 1) then v else (v : Int) - 2 ^ w
def dec (v : Nat) : Option J :=
  let p := v % 128; let rd := v / 2^7 % 32; let f := v / 2^12 % 8; let r1 := v / 2^15 % 32; let r2 := v / 2^20 % 32
  let ii := sx (v / 2^20) 12; let si := sx (v / 2^25 * 32 + v / 2^7 % 32) 12
  let bo := sx (v / 2^31 * 4096 + v / 2^7 % 2 * 2048 + v / 2^25 % 64 * 32 + v / 2^8 % 16 * 2) 13
  let jo := sx (v / 2^31 * 2^20 + v / 2^12 % 256 * 2^12 + v / 2^20 % 2 * 2^11 + v / 2^21 % 1024 * 2) 21
  let f7 := v / 2^25
  if p = 19 then (if f = 0 then some (.addi rd r1 ii) else if f = 1 then some (.slli rd r1 (v / 2^20 % 64))
    else if f = 5 then some (.srli rd r1 (v / 2^20 % 64)) else none)
  else if p = 3 then (if f = 3 then some (.ld rd r1 ii) else if f = 4 then some (.lbu rd r1 ii) else none)
  else if p = 35 then (if f = 3 then some (.sd r2 r1 si) else if f = 0 then some (.sb r2 r1 si) else none)
  else if p = 51 then
    let op := if f7 = 0 then (if f = 0 then 1 else if f = 7 then 4 else if f = 6 then 5 else if f = 1 then 6
      else if f = 5 then 7 else if f = 4 then 8 else 0) else if f7 = 32 ∧ f = 0 then 2 else if f7 = 1 ∧ f = 0 then 3 else 0
    if op = 0 then none else some (.alu op rd r1 r2)
  else if p = 99 then (if f = 0 then some (.beq r1 r2 (bo / 4)) else if f = 1 then some (.bne r1 r2 (bo / 4))
    else if f = 6 then some (.bltu r1 r2 (bo / 4)) else if f = 7 then some (.bgeu r1 r2 (bo / 4)) else none)
  else if p = 111 then some (.jal rd (jo / 4))
  else if p = 103 then some (.jalr rd r1) else none
def words (b : ByteArray) : List Nat :=
  (List.range (b.size / 4)).map fun i => b[4*i]!.toNat + b[4*i+1]!.toNat * 256 + b[4*i+2]!.toNat * 65536 + b[4*i+3]!.toNat * 16777216
def main (args : List String) : IO UInt32 := do
  let mut same := 0; let mut rej := 0; let mut bad := 0; let mut nodec := 0
  for f in args do
    let b ← IO.FS.readBinFile f
    let ws := words b
    match ws.mapM dec with
    | none => nodec := nodec + 1; IO.println s!"NODECODE {f}"
    | some cj =>
      if cj.map (fun j => (encG j).toNat) != ws then nodec := nodec + 1; IO.println s!"NOROUNDTRIP {f}"; continue
      let mine := C.e45 b.toList
      let ok := match JT.natEncJ cj with
        | some s => s == mine && mine != []
        | none => mine == []
      if ok then
        if mine == [] then rej := rej + 1 else same := same + 1
      else
        bad := bad + 1
        IO.println s!"*** MISMATCH {f}: spec {(JT.natEncJ cj).map List.length} B, translator {mine.length} B"
  IO.println s!"spec_cmp: {args.length} files: byte-identical {same}, both reject {rej}, MISMATCH {bad}, undecodable {nodec}"
  return (if bad + nodec == 0 then 0 else 1)
