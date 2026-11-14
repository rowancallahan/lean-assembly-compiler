/- VERBATIM copy of `AState` / `armStep` from `Arm/proofs/Arm/Small.lean` (our own file; that file also imports the
Sail model, which is not available in this Lean 4.34.0 environment) and of the word list `emitted` from `Arm/proofs/Arm/Words.lean`. -/
namespace Proven.Arm
structure AState where
  x : Nat → BitVec 64
  n : Bool
  z : Bool
  c : Bool
  v : Bool

namespace AState
/-- read `x r`; `31` is `xzr` in every instruction modelled here -/
def rd (a : AState) (r : Nat) : BitVec 64 := if r = 31 then 0 else a.x r
/-- write `x d`; writes to `31` (`xzr`) are dropped -/
def setX (a : AState) (d : Nat) (v : BitVec 64) : AState :=
  if d = 31 then a else { a with x := fun i => if i = d then v else a.x i }
/-- NZCV as set by `subs _, x, y` -/
def setSub (a : AState) (x y : BitVec 64) : AState :=
  { a with n := (x - y).msb, z := x - y = 0, c := y.toNat ≤ x.toNat, v := (x - y).toInt ≠ x.toInt - y.toInt }
/-- the A64 condition `c` (ARM ARM `ConditionHolds`) -/
def cond (a : AState) (c : BitVec 4) : Bool :=
  let r := match (c >>> 1).toNat with
    | 0 => a.z | 1 => a.c | 2 => a.n | 3 => a.v | 4 => a.c && !a.z | 5 => a.n == a.v
    | 6 => a.n == a.v && !a.z | _ => true
  if c.getLsbD 0 && c != 15 then !r else r
end AState

/-- One instruction of the small machine. Covers the instructions `Arm.compile` emits (except `ret`);
any other word leaves the state unchanged (not modelled). -/
def armStep (w : BitVec 32) (a : AState) : AState :=
  let d := (w.extractLsb' 0 5).toNat
  let n := (w.extractLsb' 5 5).toNat
  let m := (w.extractLsb' 16 5).toNat
  let X := a.rd
  let imm12 : BitVec 64 := (w.extractLsb' 10 12).setWidth 64
  let is (mask v : BitVec 32) : Bool := w &&& mask == v
  if is 0xFFE0FC00 0x8B000000 then a.setX d (X n + X m)                                  -- add  xd, xn, xm
  else if is 0xFFE0FC00 0xCB000000 then a.setX d (X n - X m)                             -- sub  xd, xn, xm
  else if is 0xFFE0FC00 0xEB000000 then (a.setSub (X n) (X m)).setX d (X n - X m)        -- subs xd, xn, xm
  else if is 0xFFE0FC00 0x8A000000 then a.setX d (X n &&& X m)                           -- and  xd, xn, xm
  else if is 0xFFE0FC00 0xAA000000 then a.setX d (X n ||| X m)                           -- orr  xd, xn, xm
  else if is 0xFFE0FC00 0xCA000000 then a.setX d (X n ^^^ X m)                           -- eor  xd, xn, xm
  else if is 0xFFE0FC00 0x9AC02000 then a.setX d (X n <<< ((X m).toNat % 64))            -- lslv xd, xn, xm
  else if is 0xFFE0FC00 0x9AC02400 then a.setX d (X n >>> ((X m).toNat % 64))            -- lsrv xd, xn, xm
  else if is 0xFFE0FC00 0x9AC02800 then a.setX d ((X n).sshiftRight ((X m).toNat % 64))  -- asrv xd, xn, xm
  else if is 0xFFE00C00 0x9A800000 then                                                  -- csel  xd, xn, xm, c
    a.setX d (if a.cond (w.extractLsb' 12 4) then X n else X m)
  else if is 0xFFE00C00 0x9A800400 then                                                  -- csinc xd, xn, xm, c
    a.setX d (if a.cond (w.extractLsb' 12 4) then X n else X m + 1)
  else if is 0xFFE00000 0xD2800000 then a.setX d ((w.extractLsb' 5 16).setWidth 64)      -- movz xd, #imm16
  else if is 0xFFC00000 0x91000000 && n != 31 && d != 31 then a.setX d (X n + imm12)     -- add  xd, xn, #imm12
  else if is 0xFFC00000 0xF1000000 && n != 31 then                                       -- subs xd, xn, #imm12
    (a.setSub (X n) imm12).setX d (X n - imm12)
  else a

def emitted : List (BitVec 32) := [0x8B0A0129#32, 0x8B0B014A#32, 0x8B0C016B#32, 0x8B0D018C#32, 0x8B0E01AD#32, 0x8B0F01CE#32, 0x8B0401EF#32, 0x8B050084#32, 0x8B0600A5#32, 0x8B0700C6#32, 0xCB0A0129#32, 0xCB0B014A#32, 0xCB0C016B#32, 0xCB0D018C#32, 0xCB0E01AD#32, 0xCB0F01CE#32, 0xCB0401EF#32, 0xCB050084#32, 0xCB0600A5#32, 0xCB0700C6#32, 0x8A0A0129#32, 0x8A0B014A#32, 0x8A0C016B#32, 0x8A0D018C#32, 0x8A0E01AD#32, 0x8A0F01CE#32, 0x8A0401EF#32, 0x8A050084#32, 0x8A0600A5#32, 0x8A0700C6#32, 0xAA0A0129#32, 0xAA0B014A#32, 0xAA0C016B#32, 0xAA0D018C#32, 0xAA0E01AD#32, 0xAA0F01CE#32, 0xAA0401EF#32, 0xAA050084#32, 0xAA0600A5#32, 0xAA0700C6#32, 0xCA0A0129#32, 0xCA0B014A#32, 0xCA0C016B#32, 0xCA0D018C#32, 0xCA0E01AD#32, 0xCA0F01CE#32, 0xCA0401EF#32, 0xCA050084#32, 0xCA0600A5#32, 0xCA0700C6#32, 0x9ACA2129#32, 0x9ACB214A#32, 0x9ACC216B#32, 0x9ACD218C#32, 0x9ACE21AD#32, 0x9ACF21CE#32, 0x9AC421EF#32, 0x9AC52084#32, 0x9AC620A5#32, 0x9AC720C6#32, 0x9ACA2529#32, 0x9ACB254A#32, 0x9ACC256B#32, 0x9ACD258C#32, 0x9ACE25AD#32, 0x9ACF25CE#32, 0x9AC425EF#32, 0x9AC52484#32, 0x9AC624A5#32, 0x9AC724C6#32, 0x9ACA2929#32, 0x9ACB294A#32, 0x9ACC296B#32, 0x9ACD298C#32, 0x9ACE29AD#32, 0x9ACF29CE#32, 0x9AC429EF#32, 0x9AC52884#32, 0x9AC628A5#32, 0x9AC728C6#32, 0xEB0A013F#32, 0x9A9F27E9#32, 0x9A9FA7E9#32, 0x9A9F17E9#32, 0xEB0B015F#32, 0x9A9F27EA#32, 0x9A9FA7EA#32, 0x9A9F17EA#32, 0xEB0C017F#32, 0x9A9F27EB#32, 0x9A9FA7EB#32, 0x9A9F17EB#32, 0xEB0D019F#32, 0x9A9F27EC#32, 0x9A9FA7EC#32, 0x9A9F17EC#32, 0xEB0E01BF#32, 0x9A9F27ED#32, 0x9A9FA7ED#32, 0x9A9F17ED#32, 0xEB0F01DF#32, 0x9A9F27EE#32, 0x9A9FA7EE#32, 0x9A9F17EE#32, 0xEB0401FF#32, 0x9A9F27EF#32, 0x9A9FA7EF#32, 0x9A9F17EF#32, 0xEB05009F#32, 0x9A9F27E4#32, 0x9A9FA7E4#32, 0x9A9F17E4#32, 0xEB0600BF#32, 0x9A9F27E5#32, 0x9A9FA7E5#32, 0x9A9F17E5#32, 0xEB0700DF#32, 0x9A9F27E6#32, 0x9A9FA7E6#32, 0x9A9F17E6#32, 0xF100013F#32, 0x9A8B1149#32, 0xF100015F#32, 0x9A8C116A#32, 0xF100017F#32, 0x9A8D118B#32, 0xF100019F#32, 0x9A8E11AC#32, 0xF10001BF#32, 0x9A8F11CD#32, 0xF10001DF#32, 0x9A8411EE#32, 0xF10001FF#32, 0x9A85108F#32, 0xF100009F#32, 0x9A8610A4#32, 0xF10000BF#32, 0x9A8710C5#32, 0xAA0003E9#32, 0xAA0103E9#32, 0xAA0203E9#32, 0xAA0303E9#32, 0xD2800009#32, 0x8B090129#32, 0x91000529#32, 0xAA0003EA#32, 0xAA0103EA#32, 0xAA0203EA#32, 0xAA0303EA#32, 0xD280000A#32, 0x8B0A014A#32, 0x9100054A#32, 0xAA0003EB#32, 0xAA0103EB#32, 0xAA0203EB#32, 0xAA0303EB#32, 0xD280000B#32, 0x8B0B016B#32, 0x9100056B#32, 0xAA0003EC#32, 0xAA0103EC#32, 0xAA0203EC#32, 0xAA0303EC#32, 0xD280000C#32, 0x8B0C018C#32, 0x9100058C#32, 0xAA0003ED#32, 0xAA0103ED#32, 0xAA0203ED#32, 0xAA0303ED#32, 0xD280000D#32, 0x8B0D01AD#32, 0x910005AD#32, 0xAA0003EE#32, 0xAA0103EE#32, 0xAA0203EE#32, 0xAA0303EE#32, 0xD280000E#32, 0x8B0E01CE#32, 0x910005CE#32, 0xAA0003EF#32, 0xAA0103EF#32, 0xAA0203EF#32, 0xAA0303EF#32, 0xD280000F#32, 0x8B0F01EF#32, 0x910005EF#32, 0xAA0003E4#32, 0xAA0103E4#32, 0xAA0203E4#32, 0xAA0303E4#32, 0xD2800004#32, 0x8B040084#32, 0x91000484#32, 0xAA0003E5#32, 0xAA0103E5#32, 0xAA0203E5#32, 0xAA0303E5#32, 0xD2800005#32, 0x8B0500A5#32, 0x910004A5#32, 0xAA0003E6#32, 0xAA0103E6#32, 0xAA0203E6#32, 0xAA0303E6#32, 0xD2800006#32, 0x8B0600C6#32, 0x910004C6#32, 0xAA0003E7#32, 0xAA0103E7#32, 0xAA0203E7#32, 0xAA0303E7#32, 0xD2800007#32, 0x8B0700E7#32, 0x910004E7#32, 0xAA0903E0#32]
end Proven.Arm
