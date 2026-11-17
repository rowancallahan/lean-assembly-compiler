/- B₁: the v2 assembler `asmV` (Nano/V2/Asm.lean) in S3 form (Nano/V2Boot/Prelude.lean) and the bridge
`asmVS_eq : asmVS xs = asmV xs` (inputs of length < 2^64). `ax0..ax3` are the v2 originals. -/
import Nano.V2S.Asm
import Nano.V2Boot.Prelude

namespace Nano.V2B
open Nano.V2S

/-- the sign fill of `ax3` without a comparison (S3's certificate search does not split a word `if` in a
non-recursive function); equal to `if c < 128 then 0 else 0xF0` on bytes -/
def sgn8 (c : UInt64) : UInt64 := ((c >>> 7) &&& 1) * 0xF0

set_option maxRecDepth 10000 in
theorem sgn8_all : ∀ n : Fin 256, sgn8 (UInt64.ofNat n) = if UInt64.ofNat n < 128 then 0 else 0xF0 := by
  decide +kernel

theorem sgn8_eq (c : UInt64) (h : c < 256) : sgn8 c = if c < 128 then 0 else 0xF0 := by
  have := sgn8_all ⟨c.toNat, by rw [UInt64.lt_iff_toNat_lt] at h; simpa using h⟩
  simpa using this

/-- `ax3` with `sgn8` -/
def ax3S (op a c : UInt64) : UInt64 :=
  if op == 3 || op == 8 then c >>> 1
  else if op == 0 then (c >>> 4) ||| sgn8 c
  else if op == 11 then ((c >>> 2) <<< 1) ||| (a >>> 4)
  else if op == 16 then a >>> 4
  else if op == 32 then (c >>> 4) ||| 0x40
  else if op == 40 then (c >>> 4) ||| 2
  else c >>> 4

theorem ax3S_eq (op a c : UInt64) (h : c < 256) : ax3S op a c = ax3 op a c := by
  simp only [ax3S, ax3, sgn8_eq c h]

def asmLS (f : UInt64) (xs : List UInt8) (i : UInt64) (o : List UInt8) : List UInt8 :=
  if h : f = 0 then o
  else if i + 4 ≤ lenS xs then
    let op := rdS xs i
    let a := rdS xs (i + 1)
    let b := rdS xs (i + 2)
    let c := rdS xs (i + 3)
    asmLS (f - 1) xs (i + 4) (putR (putR (putR (putR o (ax0 op a c)) (ax1 op a b c)) (ax2 op a b c)) (ax3S op a c))
  else o
termination_by f.toNat
decreasing_by exact dec_lt h

def asmVS (xs : List UInt8) : List UInt8 := (asmLS (lenS xs) xs 0 []).reverse

theorem asmLS_eq (xs : List UInt8) : ∀ (n : Nat) (i : UInt64) (o : List UInt8), n < 2 ^ 64 →
    asmLS n.toUInt64 xs i o.reverse = (asmL n xs i o).reverse
  | 0, i, o, _ => by rw [asmLS, dif_pos fuel_zero, asmL]
  | n + 1, i, o, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    rw [asmLS, dif_neg h1, asmL, lenS_eq]
    simp only [rdS_eq, h2, putR_rev, ax3S_eq _ _ _ (rd_lt _ _)]
    split
    · exact asmLS_eq xs n _ _ (by omega)
    · rfl

theorem asmVS_eq (xs : List UInt8) (h : xs.length < 2 ^ 64) : asmVS xs = asmV xs := by
  have := asmLS_eq xs xs.length 0 [] h
  simp only [List.reverse_nil] at this
  rw [asmVS, lenS_eq, show len xs = xs.length.toUInt64 from rfl, this, List.reverse_reverse]; rfl

end Nano.V2B
