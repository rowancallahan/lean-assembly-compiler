import Proven.CompilerArmFast
open Proven
def r (i : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + 0xD1B54A32D192ED03 * (i * i + 1) + (i >>> 3) * 0x2545F4914F6CDD1D) % 2^64
#eval show IO Unit from do
  let n := 20000
  let rv := (List.range n).foldl (fun a i => a + (Fast.li 8 5 (BitVec.ofNat 64 (r i)).toInt).length) 0
  let arm := (List.range n).foldl (fun a i => a + (Arm.Fast.liArm 9 (r i)).length) 0
  let rvmax := (List.range n).foldl (fun a i => max a (Fast.li 8 5 (BitVec.ofNat 64 (r i)).toInt).length) 0
  IO.println s!"uniform 64-bit constant: RV64 avg {rv * 100 / n}/100 words (max {rvmax}), AArch64 avg {arm * 100 / n}/100 words; std backends ~ bit length*1.5 (avg ~96 + )"
  let std := (List.range n).foldl (fun a i => a + (genConst 0 (r i)).length) 0
  IO.println s!"std genConst avg {std * 100 / n}/100 words"
