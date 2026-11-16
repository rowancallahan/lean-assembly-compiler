/- `String`s in the inductive path (NOTES sections 23, 28).

**Byte format** of a `String` (`encString`, the owner's layout; `Bytes LString` below, as `LList UInt8` in
`Spec/Encode.lean`): its length in bytes `n`, 8 bytes little-endian, then its `n` UTF-8 bytes.  E.g. `"aλ"` is
`03 00 00 00 00 00 00 00 61 ce bb`, `""` is eight `00`.  A `String` field of a `frontx_ind_type` is a field `Fld.sl` /
`Fld.sr` of the shape, whose bytes are `C.senc` (`Compiler/Ind.lean`); `senc_ofString` says they are
`encString s`.

**In memory** a string is a chain of cells `Bytes8` (one byte per cell, the `UInt8` field a 1-byte scalar `Fld.b`),
`Bytes8.ofString s`, with the shape's last two tags (`sTag`: `nil`, then `cons`); the decoder builds it from the
length and the bytes (`dStr`), the encoder counts it and writes it back (`eStr`, `Compiler/IndStrOk.lean`).  Equality
of strings is `Bytes8.eqb` on the chains (`eqb_ofString`). -/
import Riscv.Frontx.Ind

namespace Proven.Frontx.Ind
open Proven.Mach.Ind (C str_sb)

/-- the bytes of a string, one per cell -/
inductive Bytes8 where
  | nil
  | cons (b : UInt8) (rest : Bytes8)

def Bytes8.ofList : List UInt8 → Bytes8
  | [] => .nil
  | b :: bs => .cons b (ofList bs)

/-- a string as the chain of its UTF-8 bytes -/
def Bytes8.ofString (s : String) : Bytes8 := ofList s.toUTF8.data.toList

/-- equality of byte chains (compiled with the program when a function compares strings) -/
def Bytes8.eqb : Bytes8 → Bytes8 → Bool
  | .nil, .nil => true
  | .cons a r, .cons b s => a == b && eqb r s
  | _, _ => false

theorem Bytes8.eqb_ofList : ∀ (a b : List UInt8), Bytes8.eqb (ofList a) (ofList b) = decide (a = b)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [ofList, eqb, eqb_ofList xs ys, List.cons.injEq]
    by_cases h : x = y <;> by_cases h' : xs = ys <;> simp [h, h']

theorem toUTF8_list_inj {s t : String} (h : s.toUTF8.data.toList = t.toUTF8.data.toList) : s = t := by
  have h1 : s.toUTF8 = t.toUTF8 := by
    cases hs : s.toUTF8; cases ht : t.toUTF8
    rw [hs, ht] at h; simp only at h; rw [Array.toList_inj] at h; rw [h]
  obtain ⟨a, ha⟩ := s; obtain ⟨b, hb⟩ := t
  have : a = b := h1
  subst this; rfl

@[simp] theorem Bytes8.eqb_ofString (s t : String) :
    Bytes8.eqb (ofString s) (ofString t) = decide (s = t) := by
  unfold ofString; rw [eqb_ofList]
  by_cases h : s = t
  · subst h; simp
  · have : s.toUTF8.data.toList ≠ t.toUTF8.data.toList := fun e => h (toUTF8_list_inj e)
    rw [decide_eq_false this, decide_eq_false h]

/-! ## the byte format -/

open Proven in
/-- **The byte format of a `String`**: its length in bytes (8 bytes, little-endian), then its UTF-8 bytes -/
def encString (s : String) : List UInt8 := enc (BitVec.ofNat 64 s.utf8ByteSize) ++ s.toUTF8.data.toList

/-- a string of fewer than `2^64` bytes (the strings that `encString` can describe; cf. `LList`) -/
structure LString where
  s : String
  short : s.utf8ByteSize < 2 ^ 64

open Proven in
/-- the format of strings in the style of `Spec/Encode.lean`, with its decoder: the length, then that many bytes
that are valid UTF-8 -/
instance : Bytes LString where
  enc l := encString l.s
  dec bs := (dec (α := BitVec 64) bs).bind fun (n, r) =>
    if h : n.toNat ≤ r.length ∧ (ByteArray.mk (r.take n.toNat).toArray).IsValidUTF8 then
      if h' : (String.ofByteArray _ h.2).utf8ByteSize < 2 ^ 64 then some (⟨String.ofByteArray _ h.2, h'⟩, r.drop n.toNat)
      else none
    else none
  dec_enc l rest := by
    obtain ⟨s, h⟩ := l
    have hs : s.toUTF8.data.toList.length = s.utf8ByteSize := by simp [String.size_toByteArray]
    simp only [encString, List.append_assoc, dec_enc, Option.bind_some]
    have hn : (BitVec.ofNat 64 s.utf8ByteSize).toNat = s.utf8ByteSize := by simp [Nat.mod_eq_of_lt h]
    simp only [hn]
    have ht : (s.toUTF8.data.toList ++ rest).take s.utf8ByteSize = s.toUTF8.data.toList := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have hd : (s.toUTF8.data.toList ++ rest).drop s.utf8ByteSize = rest := by
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
    have hb : ByteArray.mk (s.toUTF8.data.toList.toArray) = s.toByteArray := by simp
    simp only [ht, hd, hb]
    rw [dif_pos ⟨by simp, s.isValidUTF8⟩]; exact dif_pos h

example : encString "" = [0, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
example : encString "ab" = [2, 0, 0, 0, 0, 0, 0, 0, 0x61, 0x62] := by decide +kernel
-- NUL, 2-, 3- and 4-byte UTF-8
example : encString "\x00λ∀𝔸" = [10, 0, 0, 0, 0, 0, 0, 0, 0, 0xce, 0xbb, 0xe2, 0x88, 0x80, 0xf0, 0x9d, 0x94, 0xb8] := by
  decide +kernel

/-- the cells of `Bytes8.ofList L` under an embedding with the equations of `T.Nk.emb` (tag `off`: `nil`) -/
theorem emb_ofList (emb : Bytes8 → C) (off : Nat) (h0 : emb .nil = .c off 0 .z .z)
    (h1 : ∀ b r, emb (.cons b r) = .c (off + 1) (BitVec.ofNat 64 b.toNat) (emb r) .z) :
    ∀ L, emb (Bytes8.ofList L) = C.str off L
  | [] => h0
  | b :: L => by rw [Bytes8.ofList, h1, emb_ofList emb off h0 h1 L]; rfl

/-- the bytes of a string's cells are `encString` -/
theorem senc_ofString (st : Nat) (s : String) : (C.str st s.toUTF8.data.toList).senc = encString s := by
  simp only [C.senc, str_sb, encString, Proven.enc, Bytes.enc, BitVec.toNat_ofNat]
  rw [show (2 : Nat) ^ 64 = 256 ^ 8 from rfl, leN_mod]; congr 2

@[simp] theorem bw_eqz (c : Bool) : Op.eval .eq (bw c) 0#64 = bw (!c) := by cases c <;> rfl

/-- a byte as a word -/
theorem u8_eq (x y : UInt8) :
    Op.eval .eq (BitVec.ofNat 64 x.toNat) (BitVec.ofNat 64 y.toNat) = bw (decide (x = y)) := by
  have e : BitVec.ofNat 64 x.toNat = BitVec.ofNat 64 y.toNat ↔ x = y := by
    constructor
    · intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by have := x.toNat_lt; omega), Nat.mod_eq_of_lt (by have := y.toNat_lt; omega)] at this
      exact UInt8.toNat_inj.1 this
    · intro h; rw [h]
  simp only [Op.eval, bw]
  by_cases h : x = y <;> simp [h, e]

@[simp] theorem u8_lt' (x : UInt8) : x.toNat < 256 := x.toNat_lt

theorem u8_lt (x : UInt8) : (BitVec.ofNat 64 x.toNat).toNat < 256 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.toNat_lt; omega)]; exact x.toNat_lt

end Proven.Frontx.Ind
