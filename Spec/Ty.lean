/- A universe of types with ONE recursive byte format. Pure Lean, no machine model.
   A type is a code `Ty` (itself one tag byte per constructor); a value of type `t.denote` is encoded by recursion on `t`.
   Every format satisfies `dec (enc a ++ rest) = some (a, rest)`, proved once by recursion on the code.
   Formats are simple, not compact: a program may use any internal representation below the spec. -/
import Spec.Encode
namespace Proven

/-! ## natural numbers of any size: 7 bits per byte, low group first; high bit set = more bytes follow -/
def encNat (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (n % 128 + 128) :: encNat (n / 128)
decreasing_by omega

def decNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs => if b.toNat < 128 then some (b.toNat, bs)
               else (decNat bs).map fun (m, r) => (b.toNat - 128 + 128 * m, r)

theorem decNat_encNat (n : Nat) (rest : List UInt8) : decNat (encNat n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [encNat]; split
    · next h =>
      have : (UInt8.ofNat n).toNat = n := by rw [UInt8.toNat_ofNat']; omega
      simp [decNat, this, h]
    · next h =>
      have e : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by rw [UInt8.toNat_ofNat']; omega
      simp only [List.cons_append, decNat, e]
      rw [ih (n / 128) (by omega)]
      have hb : ¬ (n % 128 + 128 < 128) := by omega
      simp only [hb, ↓reduceIte, Option.map_some]
      simp; omega

instance : Bytes Nat := ⟨encNat, decNat, decNat_encNat⟩

/-- tag byte 0 = left, 1 = right, then the value -/
instance [Bytes α] [Bytes β] : Bytes (α ⊕ β) where
  enc | .inl a => 0 :: enc a | .inr b => 1 :: enc b
  dec | 0 :: r => (dec r).map fun (a, r') => (.inl a, r')
      | 1 :: r => (dec r).map fun (b, r') => (.inr b, r')
      | _ => none
  dec_enc s rest := by cases s <;> simp [dec_enc]

/-- a list of any length: its length as a `Nat`, then the elements one after another -/
instance (priority := low) instBytesList [Bytes α] : Bytes (List α) where
  enc xs := encNat xs.length ++ encs xs
  dec bs := (decNat bs).bind fun (n, r) => decs n r
  dec_enc xs rest := by simp [List.append_assoc, decNat_encNat, decs_encs]

/-! ## type codes -/
inductive Ty where
  | u8 | u64 | bool | nat
  | opt (t : Ty) | prod (a b : Ty) | sum (a b : Ty) | list (t : Ty)
  deriving DecidableEq, Repr

/-- the Lean type a code stands for -/
def Ty.denote : Ty → Type
  | .u8 => UInt8 | .u64 => BitVec 64 | .bool => Bool | .nat => Nat
  | .opt t => Option t.denote | .prod a b => a.denote × b.denote
  | .sum a b => a.denote ⊕ b.denote | .list t => List t.denote

/-- the byte format of every coded type, by recursion on the code -/
@[reducible] def Ty.bytes : (t : Ty) → Bytes t.denote
  | .u8 => inferInstanceAs (Bytes UInt8) | .u64 => inferInstanceAs (Bytes (BitVec 64))
  | .bool => inferInstanceAs (Bytes Bool) | .nat => inferInstanceAs (Bytes Nat)
  | .opt t => let _ := t.bytes; inferInstanceAs (Bytes (Option t.denote))
  | .prod a b => let _ := a.bytes; let _ := b.bytes; inferInstanceAs (Bytes (a.denote × b.denote))
  | .sum a b => let _ := a.bytes; let _ := b.bytes; inferInstanceAs (Bytes (a.denote ⊕ b.denote))
  | .list t => let _ := t.bytes; instBytesList

instance (t : Ty) : Bytes t.denote := t.bytes

/-- round trip for EVERY coded type (it is a field of `Bytes`; restated for reading) -/
theorem Ty.dec_enc (t : Ty) (a : t.denote) (rest : List UInt8) : dec (enc a ++ rest) = some (a, rest) :=
  Bytes.dec_enc a rest

/-! ## the type code itself as bytes: one tag byte per constructor, arguments follow -/
def Ty.code : Ty → List UInt8
  | .u8 => [0] | .u64 => [1] | .bool => [2] | .nat => [3]
  | .opt t => 4 :: t.code | .prod a b => 5 :: (a.code ++ b.code)
  | .sum a b => 6 :: (a.code ++ b.code) | .list t => 7 :: t.code

/-- read a type code; `fuel` bounds the nesting (the input length always suffices) -/
def Ty.read : Nat → List UInt8 → Option (Ty × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, b :: r =>
    if b = 0 then some (.u8, r) else if b = 1 then some (.u64, r) else if b = 2 then some (.bool, r)
    else if b = 3 then some (.nat, r)
    else if b = 4 then (Ty.read f r).map fun (t, r') => (.opt t, r')
    else if b = 5 then (Ty.read f r).bind fun (a, r') => (Ty.read f r').map fun (b', r'') => (.prod a b', r'')
    else if b = 6 then (Ty.read f r).bind fun (a, r') => (Ty.read f r').map fun (b', r'') => (.sum a b', r'')
    else if b = 7 then (Ty.read f r).map fun (t, r') => (.list t, r')
    else none

theorem Ty.read_code (t : Ty) : ∀ (fuel : Nat) (rest : List UInt8), t.code.length ≤ fuel →
    Ty.read fuel (t.code ++ rest) = some (t, rest) := by
  induction t with
  | u8 | u64 | bool | nat => intro fuel rest h; cases fuel <;> simp_all [Ty.code, Ty.read]
  | opt t ih | list t ih =>
    intro fuel rest h; cases fuel with
    | zero => simp [Ty.code] at h
    | succ f => simp [Ty.code] at h; simp [Ty.code, Ty.read, ih f rest (by omega)]
  | prod a b iha ihb | sum a b iha ihb =>
    intro fuel rest h; cases fuel with
    | zero => simp [Ty.code] at h
    | succ f =>
      simp [Ty.code] at h
      simp [Ty.code, Ty.read, List.append_assoc, iha f (b.code ++ rest) (by omega), ihb f rest (by omega)]

/-- a self-describing value: its type code, then the value -/
def encAny (t : Ty) (a : t.denote) : List UInt8 := t.code ++ enc a
def decAny (bs : List UInt8) : Option ((t : Ty) × t.denote × List UInt8) :=
  (Ty.read bs.length bs).bind fun (t, r) => (dec (α := t.denote) r).map fun (a, r') => ⟨t, a, r'⟩
theorem decAny_encAny (t : Ty) (a : t.denote) (rest : List UInt8) :
    decAny (encAny t a ++ rest) = some ⟨t, a, rest⟩ := by
  have h := Ty.read_code t (encAny t a ++ rest).length (enc a ++ rest) (by simp [encAny])
  simp only [encAny, List.append_assoc, List.length_append] at h ⊢
  simp [decAny, h, dec_enc]

/-! ## shorthands for compound types are ordinary definitions -/
abbrev Ty.bytesT : Ty := .list .u8                 -- a byte string
abbrev Ty.point : Ty := .prod .u64 .u64            -- example: a pair of words

example : enc (300 : Nat) = [172, 2] := by simp [Bytes.enc, encNat]
example : (Ty.list (.prod .u8 .bool)).code = [7, 5, 0, 2] := rfl
example : decAny (encAny (.opt .nat) (show Option Nat from some 5)) = some ⟨.opt .nat, (show Option Nat from some 5), []⟩ := by
  simpa using decAny_encAny (.opt .nat) (show Option Nat from some 5) []

end Proven
