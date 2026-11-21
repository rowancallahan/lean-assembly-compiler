/- Harvest/H1/Lit: leaf proofs for numeric / char literal features nano does not lex yet (hex 0x, bin 0b, oct 0o,
`_` separators, char literals).  Candidate rules are nano-style byte-list functions; each theorem says candidate
accepts => Lean's own total function agrees.  Lean's decoders `decodeNatLitVal?`, `decodeQuotedChar`, `decodeCharLit`
are NOT usable: they are `partial` or read strings through the `opaque` `String.Internal.get/next`
(Init/Meta/Defs.lean:923-1180), so the kernel cannot unfold them.  We therefore anchor to the total Lean pieces:
`Char.isHexDigit`, `Char.isDigit`, `Nat.digitChar`, `Nat.toDigits`, `String.toNat?`, `Char.ofNat`, `Char.utf8Size`,
`Lean.Parser.isQuotableCharDefault`.  Imports only Init/Std. -/
import Std.Data.String.ToNat
import Lean.Parser.Basic
namespace Harvest.H1

/-- the Lean character of a byte -/
abbrev ch (b : UInt8) : Char := Char.ofNat b.toNat

theorem all_bytes {p : UInt8 → Prop} (h : ∀ i : Fin 256, p (UInt8.ofNat i.val)) (b : UInt8) : p b := by
  have := h ⟨b.toNat, b.toNat_lt⟩
  simpa using this

/-! ### digit classes (candidate rules) -/
def isD (b : UInt8) : Bool := 48 ≤ b && b ≤ 57
def isBin (b : UInt8) : Bool := b == 48 || b == 49
def isOct (b : UInt8) : Bool := 48 ≤ b && b ≤ 55
def isHex (b : UInt8) : Bool := isD b || (97 ≤ b && b ≤ 102) || (65 ≤ b && b ≤ 70)
/-- value of a hex digit byte -/
def hexVal (b : UInt8) : Nat := if b ≤ 57 then b.toNat - 48 else if 97 ≤ b then b.toNat - 87 else b.toNat - 55

/-- H1-1: nano's hex digit class is `Char.isHexDigit` (Init/Data/Char/Basic.lean:137) -/
theorem isHex_eq_lean : ∀ b, isHex b = (ch b).isHexDigit := all_bytes (by decide +kernel)
/-- H1-2: decimal digits are `Char.isDigit` -/
theorem isD_eq_lean : ∀ b, isD b = (ch b).isDigit := all_bytes (by decide +kernel)
/-- H1-3: class inclusion bin ⊆ oct ⊆ dec ⊆ hex, in Lean's terms -/
theorem bin_oct_dec_hex : ∀ b, (isBin b = true → isOct b = true) ∧ (isOct b = true → (ch b).isDigit = true) ∧
    ((ch b).isDigit = true → (ch b).isHexDigit = true) := all_bytes (by decide +kernel)
/-- H1-4: the value of a hex digit is the index of Lean's lowercase digit char (`Nat.digitChar`) -/
theorem hexVal_digitChar : ∀ b, isHex b = true → Nat.digitChar (hexVal b) = (ch b).toLower ∧ hexVal b < 16 :=
  all_bytes (by decide +kernel)

/-! ### digit runs with `_` separators -/
/-- value of a digit run in base `r`, `_` skipped (Lean's decoders skip `_`) -/
def runVal (r : Nat) (w : List UInt8) : Nat := w.foldl (fun a b => if b == 95 then a else r * a + hexVal b) 0

/-- no two adjacent `_` -/
def noRep : List UInt8 → Bool
  | a :: b :: t => !(a == 95 && b == 95) && noRep (b :: t)
  | _ => true

/-- decimal run with separators, the strict shape: digits and `_`, non-empty, no leading/trailing/double `_`.
(Lean's tokenizer `takeDigitsFn` is looser: it allows `1__2`; Lean's reader `String.toNat?` is this strict one.) -/
def decUs (w : List UInt8) : Bool :=
  !w.isEmpty && w.all (fun b => isD b || b == 95) && w.head? != some 95 && w.getLast? != some 95 && noRep w

theorem ch_toNat (b : UInt8) : (ch b).toNat = b.toNat := by
  have := b.toNat_lt
  simp [ch, Char.ofNat, Nat.isValidChar, show b.toNat < 55296 by omega, Char.ofNatAux, Char.toNat]

theorem ch_us (b : UInt8) : ch b = '_' ↔ b = 95 := by
  constructor
  · intro h; have := congrArg Char.toNat h; rw [ch_toNat] at this
    exact UInt8.toNat_inj.mp (by simpa using this)
  · rintro rfl; rfl

theorem noRep_infix : ∀ w : List UInt8, noRep w = true → ¬ (['_', '_'] <:+: w.map ch)
  | [], _ => fun h => by have := h.length_le; simp at this
  | [a], _ => fun h => by have := h.length_le; simp at this
  | a :: b :: t, h => by
    have h' : (!(a == 95 && b == 95)) = true ∧ noRep (b :: t) = true := by simpa [noRep] using h
    have ih := noRep_infix (b :: t) h'.2
    intro hi
    rw [List.map_cons, List.infix_cons_iff] at hi
    rcases hi with hp | hi
    · have hp' : '_' = ch a ∧ '_' = ch b := by simpa using hp
      have := h'.1
      have e1 : a = 95 := (ch_us a).mp hp'.1.symm
      have e2 : b = 95 := (ch_us b).mp hp'.2.symm
      subst e1; subst e2; simp at this
    · exact ih (by simpa using hi)

theorem ofDigitChars_runVal (w : List UInt8) (hw : ∀ b ∈ w, isD b = true ∨ b = 95) : ∀ a : Nat,
    Nat.ofDigitChars 10 ((w.map ch).filter (· != '_')) a = w.foldl (fun a b => if b == 95 then a else 10 * a + hexVal b) a := by
  induction w with
  | nil => intro a; simp
  | cons b w ih =>
    intro a
    have hb := hw b (by simp)
    have ih := ih (fun x hx => hw x (by simp [hx]))
    by_cases h95 : b = 95
    · subst h95; simp [ih, ch]
    · have hd : isD b = true := hb.resolve_right h95
      have hne : ch b ≠ '_' := by
        intro h; apply h95; have := congrArg Char.toNat h; rw [ch_toNat] at this
        have h2 : b.toNat = 95 := by simpa using this
        exact UInt8.toNat_inj.mp h2
      have hv : hexVal b = b.toNat - 48 := by
        have : b ≤ 57 := by simp [isD] at hd; exact hd.2
        simp [hexVal, this]
      simp [List.filter_cons, hne, Nat.ofDigitChars_cons, ih, ch_toNat, hv, h95]

/-- H1-5: a decimal run `decUs` accepts is read by Lean's `String.toNat?` (which allows `_` between digits only)
with value `runVal 10`.  Subset form; extends `LeanEquiv.numeral_sub_toNat?` to separators. -/
theorem decUs_toNat? (w : List UInt8) (h : decUs w = true) :
    (String.ofList (w.map ch)).toNat? = some (runVal 10 w) := by
  simp only [decUs, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hne, hall⟩, hhd⟩, hlast⟩, hrep⟩ := h
  have hall' : ∀ b ∈ w, isD b = true ∨ b = 95 := by
    intro b hb; have := hall b hb; simpa using this
  have hnat : (String.ofList (w.map ch)).isNat = true := by
    rw [← String.isNat_toSlice, String.Slice.isNat_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp; intro e; simp [e] at hne
    · intro c hc
      simp at hc
      obtain ⟨b, hb, rfl⟩ := hc
      rcases hall' b hb with hd | h95
      · left; rw [← isD_eq_lean]; exact hd
      · right; subst h95; rfl
    · simp
      intro hi
      exact noRep_infix w hrep hi
    · simp [List.head?_map]
      intro x hx e; rw [ch_us] at e; subst e; exact hhd (by simpa [hx])
    · simp [List.getLast?_map]
      intro x hx e; rw [ch_us] at e; subst e; exact hlast (by simpa [hx])
  rw [String.toNat?_eq_some_ofDigitChars hnat]
  simp only [String.toList_ofList]
  rw [ofDigitChars_runVal w hall' 0]
  rfl

/-! ### char literals -/
/-- single-byte escape letters of a char literal, the table of `decodeQuotedChar` / `isQuotableCharDefault`
(Lean/Parser/Basic.lean:673, Init/Meta/Defs.lean:1089): `\\ \" \' \r \n \t` -/
def escVal : UInt8 → Option UInt8
  | 92 => some 92 | 34 => some 34 | 39 => some 39 | 114 => some 13 | 110 => some 10 | 116 => some 9 | _ => none

/-- candidate char-literal body decoder (bytes between the quotes): printable ASCII except `\` and `'`, a one-letter
escape, or `\xHH` -/
def litDec : List UInt8 → Option UInt8
  | [b] => if 32 ≤ b && b < 127 && b != 92 && b != 39 then some b else none
  | [92, e] => escVal e
  | [92, 120, h1, h2] => if isHex h1 && isHex h2 && 16 * hexVal h1 + hexVal h2 < 128 then some (UInt8.ofNat (16 * hexVal h1 + hexVal h2)) else none
  | _ => none

/-- H1-6: the escape letters nano accepts are exactly Lean's tokenizer's `isQuotableCharDefault` set -/
theorem escVal_eq_lean : ∀ b, (escVal b).isSome = Lean.Parser.isQuotableCharDefault (ch b) :=
  all_bytes (by decide +kernel)

/-- H1-7a: nano's decoder reads back what Lean's own printer `Char.quoteCore` writes (the text Lean shows for a char
literal), for every ASCII char the printer does not write as `\xHH`: plain, `\n \t \\ \" \'`.  (Controls use
`String.Internal.append`, opaque to the kernel: see 7b.) -/
theorem litDec_quoteCore : ∀ n : Fin 128, (n.val ≤ 31 ∧ n.val ≠ 9 ∧ n.val ≠ 10 ∨ n.val = 127) ∨
    litDec ((Char.quoteCore (ch (UInt8.ofNat n.val)) false).toList.map (fun c => c.toNat.toUInt8)) = some (UInt8.ofNat n.val) := by
  decide +kernel

/-- H1-7b: `Char.quoteCore.smallCharToHex` writes `\x` and the two `hexDigitRepr` = `Nat.digitChar` digits
(Init/Data/Repr.lean:357-373); nano's `\xHH` rule reads those back -/
theorem litDec_hex : ∀ n : Fin 128,
    litDec [92, 120, (Nat.digitChar (n.val / 16)).toNat.toUInt8, (Nat.digitChar (n.val % 16)).toNat.toUInt8]
      = some (UInt8.ofNat n.val) := by decide +kernel

/-- H1-8: a source byte is one Lean `Char` of the same code point only below 128; from 128 a `Char` of that
code point takes 2 UTF-8 bytes (so a byte-literal rule must reject bytes >= 128 inside quotes) -/
theorem utf8Size_byte : ∀ b : UInt8, ((ch b).utf8Size = 1 ↔ b < 128) := all_bytes (by decide +kernel)

/-- H1-9: `\uHHHH`: Lean decodes with `Char.ofNat`, which maps a surrogate (D800-DFFF) to `'\0'` silently; every
other 16-bit value is itself.  A nano `\u` rule must reject surrogates (value would not match the digits). -/
theorem ofNat_u16 (n : Nat) (hn : n < 65536) : ((Char.ofNat n).toNat = n) ∨
    (0xD800 ≤ n ∧ n ≤ 0xDFFF ∧ (Char.ofNat n).toNat = 0) := by
  by_cases hv : n.isValidChar
  · left
    simp only [Char.ofNat, dif_pos hv, Char.ofNatAux, Char.toNat]
    simp [UInt32.toNat, BitVec.toNat_ofNatLT]
  · right
    have h1 : 0xD800 ≤ n ∧ n ≤ 0xDFFF := by
      simp [Nat.isValidChar] at hv; omega
    refine ⟨h1.1, h1.2, ?_⟩
    simp only [Char.ofNat, dif_neg hv]; rfl

/-! ### value of a literal in `UInt64` -/
def runU (r : UInt64) (w : List UInt8) (a : UInt64) : UInt64 :=
  w.foldl (fun a b => if b == 95 then a else r * a + UInt64.ofNat (hexVal b)) a

theorem runU_eq (r : Nat) (w : List UInt8) : ∀ x : Nat,
    runU (UInt64.ofNat r) w (UInt64.ofNat x) = UInt64.ofNat (w.foldl (fun a b => if b == 95 then a else r * a + hexVal b) x) := by
  induction w with
  | nil => intro x; simp [runU]
  | cons b w ih =>
    intro x
    unfold runU at ih ⊢
    simp only [List.foldl_cons]
    by_cases h : b == 95
    · simp only [h, ite_true]; exact ih x
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      have : (UInt64.ofNat r * UInt64.ofNat x + UInt64.ofNat (hexVal b)) = UInt64.ofNat (r * x + hexVal b) := by
        apply UInt64.toNat_inj.mp
        simp [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', Nat.mul_mod, Nat.add_mod]
      rw [this, ih]

/-- H1-10: wrapping `UInt64` evaluation of a bin/oct/hex/dec digit run (with `_`) is Lean's `UInt64` literal of the
unbounded value `runVal r w` (`OfNat UInt64 n := ⟨UInt64.ofNat n⟩`, as for decimal in `LeanEquiv.numVal_eq_lean`) -/
theorem runU_lean (r : Nat) (w : List UInt8) :
    runU (UInt64.ofNat r) w 0 = (OfNat.ofNat (w.foldl (fun a b => if b == 95 then a else r * a + hexVal b) 0) : UInt64) := by
  exact runU_eq r w 0

/-! ### round trip against Lean's printer -/
def bytesOf (l : List Char) : List UInt8 := l.map (fun c => c.toNat.toUInt8)

theorem hexVal_digitChar' : ∀ d : Fin 16, hexVal (Nat.digitChar d.val).toNat.toUInt8 = d.val ∧
    ((Nat.digitChar d.val).toNat.toUInt8 == 95) = false := by decide +kernel

/-- H1-11: nano's bin/oct/dec/hex value `runVal r` reads back Lean's own digit printer: for `2 ≤ r ≤ 16`,
`runVal r (Nat.toDigits r n) = n` (Init/Data/Repr.lean:199-217).  So the `0x`/`0b`/`0o` value of the text Lean prints
for `n` is `n`. -/
theorem runVal_toDigits (r : Nat) (hr : 2 ≤ r) (hr' : r ≤ 16) : ∀ n : Nat, runVal r (bytesOf (Nat.toDigits r n)) = n := by
  have step : ∀ (l : List UInt8) (x : UInt8), (x == 95) = false → runVal r (l ++ [x]) = r * runVal r l + hexVal x := by
    intro l x hx
    have hx' : x ≠ 95 := by simpa using hx
    simp [runVal, List.foldl_append, hx']
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · rename_i h
      have := hexVal_digitChar' ⟨n, by omega⟩
      have h95 : (Nat.digitChar n).toNat.toUInt8 ≠ 95 := by simpa using this.2
      simp [bytesOf, runVal, this.1, h95]
    · rename_i h
      have h1 : n / r < n := Nat.div_lt_self (by omega) (by omega)
      have := hexVal_digitChar' ⟨n % r, by have := Nat.mod_lt n (show r > 0 by omega); omega⟩
      simp only [bytesOf, List.map_append, List.map_cons, List.map_nil] at ih ⊢
      rw [step _ _ this.2, this.1]
      have := ih (n / r) h1
      rw [this]
      exact Nat.div_add_mod n r

end Harvest.H1
