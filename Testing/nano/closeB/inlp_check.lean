import Nano.InlP
open Nano Nano.IP Nano.U
-- random micro-op streams with defs and calls, compare inlP with inlB
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def gen (n : Nat) (seed : Nat) : List UInt8 := Id.run do
  let mut s := seed
  let mut out : List UInt8 := []
  let mut defs := 0
  for _ in [0:n] do
    s := lcg s
    let r := (s / 65536) % 100
    if r < 10 then
      s := lcg s; out := out ++ [13, ((s / 65536) % 4).toUInt8]; defs := defs + 1
    else if r < 25 && defs > 0 then
      s := lcg s; let j := (s / 65536) % (defs + 1)
      out := out ++ [14, (j / 256).toUInt8, 15, (j % 256).toUInt8]
    else if r < 27 then
      s := lcg s; out := out ++ [((s / 65536) % 256).toUInt8]
    else
      s := lcg s; out := out ++ [((s / 65536) % 13).toUInt8, ((s / 1000) % 256).toUInt8]
  return out
#eval! show IO Unit from do
  let mut bad := 0
  let mut tot := 0
  for k in [0:400] do
    let x := gen (k % 60) (k * 7919 + 3)
    let a := inlB x
    if a.length < 100000 then
      tot := tot + 1
      let b := (inlP (ByteArray.mk x.toArray)).data.toList
      if a != b then
        bad := bad + 1
        if bad ≤ 3 then IO.println s!"MISMATCH {x} \n {a} \n {b}"
  IO.println s!"{tot} tested, {bad} mismatches"
