/- Harvest/H2/Mirror: `decodeQuotedChar` (Init/Meta/Defs.lean:1089) is total but reads the string via the opaque `String.Internal.get`,
so the kernel cannot unfold it.  Route: (1) a list-of-chars transliteration `mirror` of Lean's code, (2) a nano-style byte decoder
`dec` proved equal to `mirror` (kernel), (3) `#guard` differential tests of `mirror` against the REAL `decodeQuotedChar` (compiled
evaluation, NOT a kernel proof: this is the remaining trust gap = fidelity of the transliteration). -/
import Harvest.H2.Escape
namespace H2
open Lean Lean.Syntax

/-- Lean's `decodeHexDigit` (private) on a list -/
def mHex (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat) else none

/-- the six one-char escapes of `decodeQuotedChar` -/
def mHead (c : Char) : Option (Char × Nat) :=
  if c == '\\' then some ('\\', 1) else if c = '\"' then some ('\"', 1) else if c = '\'' then some ('\'', 1)
  else if c = 'r' then some ('\r', 1) else if c = 'n' then some ('\n', 1) else if c = 't' then some ('\t', 1) else none

/-- transliteration of `decodeQuotedChar`: input = chars after the backslash; result = decoded char and chars consumed -/
def mirror : List Char → Option (Char × Nat)
  | [] => none   -- Lean: `get` at end returns the default char 'A', which falls to `none`
  | c :: r =>
    match mHead c with
    | some p => some p
    | none =>
    if c = 'x' then match r with
      | a :: b :: _ => do let d₁ ← mHex a; let d₂ ← mHex b; pure (Char.ofNat (16*d₁ + d₂), 3)
      | _ => none
    else if c = 'u' then match r with
      | a :: b :: c :: d :: _ => do
          let d₁ ← mHex a; let d₂ ← mHex b; let d₃ ← mHex c; let d₄ ← mHex d
          pure (Char.ofNat (16*(16*(16*d₁ + d₂) + d₃) + d₄), 5)
      | _ => none
    else none

/-- nano candidate: bytes after the backslash → (byte value, consumed).  Only values < 128 (so the UTF-8 byte is the value). -/
def dec : List UInt8 → Option (UInt8 × Nat)
  | c :: r =>
    match esc c with
    | some v => some (v, 1)
    | none => if c == 120 then match r with
        | a :: b :: _ => do
            let x ← hexv a; let y ← hexv b
            if 16*x + y < 128 then some (UInt8.ofNat (16*x + y), 3) else none
        | _ => none
      else none
  | [] => none

theorem mHex_eq : ∀ b : UInt8, mHex (ch b) = hexv b := all_bytes (by decide +kernel)

theorem head_eq : ∀ b : UInt8, mHead (ch b) = (esc b).map fun v => (ch v, 1) := all_bytes (by decide +kernel)
theorem ofNat_eq : ∀ n : Fin 128, Char.ofNat n.val = ch (UInt8.ofNat n.val) := by decide +kernel

/-- every `dec` result is the mirror's result on the same bytes (subset form: `dec` may reject more) -/
theorem dec_sub_mirror (l : List UInt8) v n (h : dec l = some (v, n)) : mirror (l.map ch) = some (ch v, n) := by
  match l with
  | [] => simp [dec] at h
  | c :: r =>
    simp only [dec] at h
    simp only [List.map, mirror, head_eq]
    cases he : esc c with
    | some w => simp_all
    | none =>
      simp only [he] at h ⊢
      by_cases hx : c = 120
      · subst hx
        match r, h with
        | a :: b :: _, h =>
          have hc : ch 120 = 'x' := by decide
          simp only [List.map, mHex_eq, hc, ite_true]
          cases ha : hexv a with
          | none => simp [ha] at h
          | some x =>
          cases hb : hexv b with
          | none => simp [ha, hb] at h
          | some y =>
            simp only [ha, hb] at h ⊢
            by_cases hlt : 16 * x + y < 128
            · simp [hlt] at h
              obtain ⟨rfl, rfl⟩ := h
              simp [ofNat_eq ⟨16 * x + y, hlt⟩]
            · simp [hlt] at h
        | [], h | [_], h => simp at h
      · simp [hx] at h
-- differential tests against the real Lean function (single-char escapes, \x pairs)
#guard (List.range 128).all fun i =>
  let c := Char.ofNat i
  c == 'x' || c == 'u' ||
  decodeQuotedChar (String.singleton c) ⟨0⟩ == (mirror [c]).map (fun (a, n) => (a, ⟨n⟩))
#guard (List.range 128).all fun i => (List.range 128).all fun j =>
  let a := Char.ofNat i; let b := Char.ofNat j
  decodeQuotedChar (String.ofList ['x', a, b]) ⟨0⟩ == (mirror ['x', a, b]).map (fun (a, n) => (a, ⟨n⟩))
#guard ['0','9','a','f','A','F','g','G','/',':','@','`'].all fun a => ['0','5','f','F','z'].all fun b =>
  ['0','7','d','z'].all fun c => ['0','A','e','!'].all fun d =>
  decodeQuotedChar (String.ofList ['u', a, b, c, d]) ⟨0⟩ == (mirror ['u', a, b, c, d]).map (fun (a, n) => (a, ⟨n⟩))
