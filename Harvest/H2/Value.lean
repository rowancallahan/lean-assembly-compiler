/- Harvest/H2/Value: what a decoded escape BECOMES.  `\xHH` and `\uHHHH` produce `Char.ofNat n` (Init/Meta/Defs.lean:1101,1107);
`String.push` then stores its UTF-8 bytes (`String.utf8EncodeChar`, total).  Two traps for a byte-oriented compiler, both proved here:
`\xHH` with HH ≥ 0x80 is the CODEPOINT U+00HH (2 UTF-8 bytes), and `\uD800`..`\uDFFF` silently become U+0000 (`Char.ofNat` default). -/
import Lean.Parser.StrInterpolation
namespace H2

/-- `\xHH`, HH < 128: the stored string byte is HH itself (1 UTF-8 byte) -/
theorem x_ascii : ∀ n : Fin 128, String.utf8EncodeChar (Char.ofNat n.val) = [UInt8.ofNat n.val] := by decide +kernel
/-- trap: `\xHH`, HH ≥ 128 is two bytes, not one -/
theorem x_high : ∀ n : Fin 256, 128 ≤ n.val → (String.utf8EncodeChar (Char.ofNat n.val)).length = 2 := by decide +kernel

/-- (a 16-bit statement is split into high and low bytes: the kernel recursion depth stays at 256) -/
theorem all16 {p : Nat → Prop} (h : ∀ hi lo : Fin 256, p (hi.val * 256 + lo.val)) (n : Fin 65536) : p n.val := by
  have := h ⟨n.val / 256, by omega⟩ ⟨n.val % 256, by omega⟩
  have e : n.val / 256 * 256 + n.val % 256 = n.val := by omega
  rwa [e] at this

/-- `\uHHHH` is the codepoint itself unless it is a surrogate -/
theorem u_val : ∀ n : Fin 65536, ¬ (0xD800 ≤ n.val ∧ n.val ≤ 0xDFFF) → (Char.ofNat n.val).val.toNat = n.val := fun n =>
  all16 (p := fun m => ¬ (0xD800 ≤ m ∧ m ≤ 0xDFFF) → (Char.ofNat m).val.toNat = m) (by decide +kernel) n
/-- trap: a surrogate silently becomes NUL; nano must reject `\uD800`..`\uDFFF` (there is no Lean error) -/
theorem u_surrogate : ∀ n : Fin 65536, (0xD800 ≤ n.val ∧ n.val ≤ 0xDFFF) → Char.ofNat n.val = '\x00' := fun n =>
  all16 (p := fun m => (0xD800 ≤ m ∧ m ≤ 0xDFFF) → Char.ofNat m = '\x00') (by decide +kernel) n

/-- UTF-8 length of `\uHHHH` by range (1/2/3 bytes), so a nano string emitter can size the data -/
theorem u_len : ∀ n : Fin 65536, ¬ (0xD800 ≤ n.val ∧ n.val ≤ 0xDFFF) →
    (String.utf8EncodeChar (Char.ofNat n.val)).length = if n.val < 0x80 then 1 else if n.val < 0x800 then 2 else 3 := fun n =>
  all16 (p := fun m => ¬ (0xD800 ≤ m ∧ m ≤ 0xDFFF) → (String.utf8EncodeChar (Char.ofNat m)).length = if m < 0x80 then 1 else if m < 0x800 then 2 else 3) (by decide +kernel) n
