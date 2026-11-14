/- How Lean values are laid out as bytes, and back. This file IS the input/output format of the spec.
   Pure Lean, no machine model. Little-endian throughout. Every format has `dec (enc a ++ rest) = some (a, rest)`. -/
namespace Proven

/-- `enc a` = bytes for `a`; `dec` reads one value off the front and returns the remaining bytes. -/
class Bytes (α : Type) where
  enc : α → List UInt8
  dec : List UInt8 → Option (α × List UInt8)
  dec_enc : ∀ a rest, dec (enc a ++ rest) = some (a, rest)

export Bytes (enc dec dec_enc)

/-- decode a whole input: all bytes must be used -/
def decAll [Bytes α] (bs : List UInt8) : Option α :=
  match dec bs with | some (a, []) => some a | _ => none

theorem decAll_enc [Bytes α] (a : α) : decAll (enc a) = some a := by
  have := dec_enc a []; simp at this; simp [decAll, this]

/-! ## numbers: `k` little-endian bytes -/
def leN : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: leN k (n / 256)
def unle : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * unle bs

theorem leN_length (k n : Nat) : (leN k n).length = k := by
  induction k generalizing n <;> simp [leN, *]
theorem unle_leN (k n : Nat) : unle (leN k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [leN, unle, Nat.mod_one]
  | succ k ih =>
    have h : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      rw [UInt8.toNat_ofNat']; exact Nat.mod_mod_of_dvd _ (by decide)
    simp only [leN, unle, ih, h]
    rw [Nat.pow_succ', Nat.mod_mul]

instance : Bytes UInt8 := ⟨fun b => [b], fun | b :: r => some (b, r) | [] => none, fun _ _ => rfl⟩

/-- 64-bit word: 8 bytes, little-endian -/
instance : Bytes (BitVec 64) where
  enc w := leN 8 w.toNat
  dec bs := if bs.length < 8 then none else some (BitVec.ofNat 64 (unle (bs.take 8)), bs.drop 8)
  dec_enc w rest := by
    have h := leN_length 8 w.toNat
    simp [h, unle_leN]
    apply BitVec.eq_of_toNat_eq; simp; omega

/-- 1 byte: 0 = false, 1 = true; anything else does not decode -/
instance : Bytes Bool where
  enc b := [if b then 1 else 0]
  dec | 0 :: r => some (false, r) | 1 :: r => some (true, r) | _ => none
  dec_enc b rest := by cases b <;> rfl

/-- tag byte 0 = none, 1 = some, then the value -/
instance [Bytes α] : Bytes (Option α) where
  enc | none => [0] | some a => 1 :: enc a
  dec | 0 :: r => some (none, r)
      | 1 :: r => (dec r).map fun (a, r') => (some a, r')
      | _ => none
  dec_enc a rest := by cases a <;> simp [dec_enc]

/-- fields one after another, no padding -/
instance [Bytes α] [Bytes β] : Bytes (α × β) where
  enc p := enc p.1 ++ enc p.2
  dec bs := (dec bs).bind fun (a, r) => (dec r).map fun (b, r') => ((a, b), r')
  dec_enc p rest := by simp [List.append_assoc, dec_enc]

def encs [Bytes α] : List α → List UInt8 | [] => [] | a :: as => enc a ++ encs as
def decs [Bytes α] : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => (dec bs).bind fun (a, r) => (decs n r).map fun (as, r') => (a :: as, r')
theorem decs_encs [Bytes α] (xs : List α) (rest : List UInt8) : decs xs.length (encs xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [encs, decs, List.append_assoc, dec_enc, ih]

/-- a list shorter than 2^64: 8-byte length, then the elements one after another -/
structure LList (α : Type) where
  xs : List α
  short : xs.length < 2 ^ 64

instance [Bytes α] : Bytes (LList α) where
  enc l := enc (BitVec.ofNat 64 l.xs.length) ++ encs l.xs
  dec bs := (dec (α := BitVec 64) bs).bind fun (n, r) => (decs n.toNat r).bind fun (xs, r') =>
    if h : xs.length < 2 ^ 64 then some (⟨xs, h⟩, r') else none
  dec_enc l rest := by
    obtain ⟨xs, h⟩ := l
    simp [List.append_assoc, dec_enc, Nat.mod_eq_of_lt h, decs_encs, h]

/-- raw bytes with the length passed separately (the format of all byte-list theorems so far): identity both ways -/
def encRaw (bs : List UInt8) : List UInt8 := bs
def decRaw (bs : List UInt8) : List UInt8 := bs
theorem decRaw_encRaw (bs : List UInt8) : decRaw (encRaw bs) = bs := rfl

example : enc (0x0102030405060708#64) = [8, 7, 6, 5, 4, 3, 2, 1] := by decide
example : enc (some (5 : UInt8)) = [1, 5] := rfl
example : enc ((7 : UInt8), true) = [7, 1] := rfl
example : enc (⟨[((1 : UInt8), true), (2, false)], by decide⟩ : LList (UInt8 × Bool)) = [2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0] := by decide
example : decAll (α := Option UInt8) [1, 5] = some (some 5) := by decide
example : decAll (α := Bool) [2] = none := by decide

end Proven
