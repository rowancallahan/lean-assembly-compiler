/- How Lean values are laid out as bytes. This file IS the output format of the spec: review it.
   Pure Lean, no machine model. Little-endian throughout. -/
namespace Proven

/-- `enc a` = the bytes written to the output block for the value `a`. -/
class Bytes (α : Type) where
  enc : α → List UInt8

export Bytes (enc)

/-- 8 little-endian bytes of a 64-bit word -/
def le64 (w : BitVec 64) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat ((w.toNat >>> (8 * i)) % 256)

instance : Bytes UInt8 := ⟨fun b => [b]⟩                    -- 1 byte
instance : Bytes (BitVec 64) := ⟨le64⟩                      -- 8 bytes
instance : Bytes Bool := ⟨fun b => [if b then 1 else 0]⟩    -- 1 byte: 0 or 1
instance : Bytes (List UInt8) := ⟨id⟩                       -- raw bytes, length known separately
/-- tag byte 0 = none, 1 = some, then the value -/
instance [Bytes α] : Bytes (Option α) := ⟨fun | none => [0] | some a => 1 :: enc a⟩
/-- fields one after another, no padding -/
instance [Bytes α] [Bytes β] : Bytes (α × β) := ⟨fun (a, b) => enc a ++ enc b⟩
/-- 8-byte length, then the elements one after another -/
instance (priority := low) [Bytes α] : Bytes (List α) :=
  ⟨fun xs => le64 (BitVec.ofNat 64 xs.length) ++ xs.flatMap enc⟩

example : enc (0x0102030405060708#64) = [8, 7, 6, 5, 4, 3, 2, 1] := by decide
example : enc (some (5 : UInt8)) = [1, 5] := rfl
example : enc (none : Option UInt8) = [0] := rfl
example : enc ((7 : UInt8), true) = [7, 1] := rfl
example : enc ([1, 2, 3] : List UInt8) = [1, 2, 3] := rfl
example : enc [(1 : UInt8, true), (2, false)] = [2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0] := by decide

end Proven
