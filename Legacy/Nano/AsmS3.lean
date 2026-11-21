/- The assembler `Nano.asm` in the form the S3 front end accepts (branch nano-s3-all): the S3 front end has no `UInt8`
arithmetic, so every output byte is computed as a word (`UInt64`) and truncated (`toUInt8`); the case split on the op
byte is the original one (`UInt8` comparisons). Each single-byte piece (`p7` …) is checked against the original
byte expression on all 256 inputs (`decide +kernel`); the bridge `asmS_eq : asmS xs = asm xs` holds on EVERY input. -/
import Legacy.Nano.Asm

namespace Nano.AS
open Nano

/-! single-byte pieces: word form, and the original byte expression on every byte -/
def p7 (a : UInt8) : UInt64 := (a.toUInt64 &&& 1) <<< 7
def p2c (c : UInt8) : UInt64 := (c.toUInt64 &&& 3) <<< 2
def pc1f (c : UInt8) : UInt64 := (c.toUInt64 >>> 1) &&& 15
def psr1 (a : UInt8) : UInt64 := a.toUInt64 >>> 1
def psr4 (a : UInt8) : UInt64 := a.toUInt64 >>> 4
def pop4 (o : UInt8) : UInt64 := (o.toUInt64 &&& 7) <<< 4
def p15 (a : UInt8) : UInt64 := (a.toUInt64 &&& 15) <<< 4
def psg (c : UInt8) : UInt64 := if c < 128 then 0 else 0xF0
def pc2 (c : UInt8) : UInt64 := (c.toUInt64 >>> 2) <<< 1

theorem u8_all {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n)) : ∀ a, P a := fun a => by
  have := h a.toNat a.toNat_lt; rwa [UInt8.ofNat_toNat] at this

set_option maxRecDepth 10000 in
theorem p7_eq : ∀ a : UInt8, (p7 a).toUInt8 = ((a &&& 1).toUInt64 <<< 7).toUInt8 :=
  u8_all (by decide +kernel)
set_option maxRecDepth 10000 in
theorem p2c_eq : ∀ c : UInt8, (p2c c).toUInt8 = ((c &&& 3).toUInt64 <<< 2).toUInt8 :=
  u8_all (by decide +kernel)
set_option maxRecDepth 10000 in
theorem pc1f_eq : ∀ c : UInt8, (pc1f c).toUInt8 = ((c >>> 1) &&& (15 : UInt8)) :=
  u8_all (by decide +kernel)
set_option maxRecDepth 10000 in
theorem psr1_eq : ∀ a : UInt8, (psr1 a).toUInt8 = a >>> 1 :=
  u8_all (by decide +kernel)
set_option maxRecDepth 10000 in
theorem psr4_eq : ∀ a : UInt8, (psr4 a).toUInt8 = a >>> 4 :=
  u8_all (by decide +kernel)
set_option maxRecDepth 10000 in
theorem pop4_eq : ∀ o : UInt8, (pop4 o).toUInt8 = ((o &&& 7).toUInt64 <<< 4).toUInt8 :=
  u8_all (by decide +kernel)
set_option maxRecDepth 10000 in
theorem p15_eq : ∀ a : UInt8, (p15 a).toUInt8 = ((a &&& 15).toUInt64 <<< 4).toUInt8 :=
  u8_all (by decide +kernel)
set_option maxRecDepth 10000 in
theorem psg_eq : ∀ c : UInt8, (psg c).toUInt8 = (if c < 128 then (0 : UInt8) else 0xF0) :=
  u8_all (by decide +kernel)
set_option maxRecDepth 10000 in
theorem pc2_eq : ∀ c : UInt8, (pc2 c).toUInt8 = ((c >>> 2).toUInt64 <<< 1).toUInt8 :=
  u8_all (by decide +kernel)

/-! the four bytes of a record, as words (same case split as `X0` … `X3`) -/
def y0 (op a c : UInt8) : UInt64 :=
  if op == 3 || op == 4 then p7 a ||| 3
  else if op == 0 || op == 1 || op == 5 || op == 6 || op == 8 then p7 a ||| 0x13
  else if op == 11 then 0x23
  else if op == 16 then p7 c ||| 0x23
  else if op == 14 || op == 24 || op == 32 || op == 40 then p7 a ||| 0x33
  else if op == 7 then 0x63
  else if op == 48 then p7 a ||| 0x67
  else 0x13
def y1 (op a b c : UInt8) : UInt64 :=
  if op == 11 then p2c c ||| 0x30 ||| p7 b
  else if op == 16 then pc1f c ||| p7 b
  else if op == 7 then 0x76 ||| p7 b
  else psr1 a ||| pop4 op ||| p7 b
def y2 (op a b c : UInt8) : UInt64 :=
  if op == 3 || op == 8 then psr1 b ||| p7 c
  else if op == 11 || op == 16 then psr1 b ||| p15 a
  else psr1 b ||| p15 c
def y3 (op a c : UInt8) : UInt64 :=
  if op == 3 || op == 8 then psr1 c
  else if op == 0 then psr4 c ||| psg c
  else if op == 11 then pc2 c ||| psr4 a
  else if op == 16 then psr4 a
  else if op == 32 then psr4 c ||| 0x40
  else if op == 40 then psr4 c ||| 2
  else psr4 c

def asmS : List UInt8 → List UInt8
  | op :: a :: b :: c :: rest =>
    (y0 op a c).toUInt8 :: (y1 op a b c).toUInt8 :: (y2 op a b c).toUInt8 :: (y3 op a c).toUInt8 :: asmS rest
  | _ => []

theorem asmS_eq : ∀ xs : List UInt8, asmS xs = asm xs
  | op :: a :: b :: c :: rest => by
    rw [asmS, asm, asmS_eq rest]
    simp only [y0, y1, y2, y3, apply_ite UInt64.toUInt8, UInt64.toUInt8_or, p7_eq, p2c_eq, pc1f_eq, psr1_eq,
      psr4_eq, pop4_eq, p15_eq, psg_eq, pc2_eq]
    rfl
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl

end Nano.AS
