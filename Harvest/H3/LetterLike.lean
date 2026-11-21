/- Harvest/H3/LetterLike: non-ASCII identifier characters.  Lean 4.34.1 `Lean.isLetterLike`, `isSubScriptAlnum`,
`isIdFirst`, `isIdRest` (Init/Meta/Defs.lean:98-134) are total.  Candidate nano rule: a sorted, disjoint interval table
over code points (what a byte-level lexer rule would carry), proved EQUAL to Lean's predicates on every `Char`. -/
namespace H3

/-- candidate: membership in a disjoint interval table (holes of Lean's ranges already removed) -/
def inIv (ivs : List (Nat × Nat)) (n : Nat) : Bool := ivs.any fun (l, h) => decide (l ≤ n ∧ n ≤ h)

def llIv : List (Nat × Nat) :=
  [(0xc0, 0xd6), (0xd8, 0xf6), (0xf8, 0x17f),                       -- Latin-1 letters (no ×, ÷), Latin Extended-A
   (0x391, 0x39f), (0x3a1, 0x3a2), (0x3a4, 0x3a9),                  -- upper Greek (no Π, Σ)
   (0x3b1, 0x3ba), (0x3bc, 0x3fb),                                  -- lower Greek (no λ), Coptic
   (0x1f00, 0x1ffe), (0x2100, 0x214f), (0x1d49c, 0x1d59f)]          -- polytonic Greek, letterlike block, math alphabets
def subIv : List (Nat × Nat) := [(0x2080, 0x2089), (0x2090, 0x209c), (0x1d62, 0x1d6a), (0x2c7c, 0x2c7c)]

theorem letterLike_eq (c : Char) : Lean.isLetterLike c = inIv llIv c.val.toNat := by
  rw [Bool.eq_iff_iff]
  simp [Lean.isLetterLike, inIv, llIv, UInt32.le_iff_toNat_le, ← UInt32.toNat_inj]
  omega


theorem subScript_eq (c : Char) : Lean.isSubScriptAlnum c = inIv subIv c.val.toNat := by
  rw [Bool.eq_iff_iff]
  simp [Lean.isSubScriptAlnum, Lean.isNumericSubscript, inIv, subIv, UInt32.le_iff_toNat_le, ← UInt32.toNat_inj]
  omega

/-- candidate: first character of an identifier, over code points -/
def idFirstC (n : Nat) : Bool := inIv [(65, 90), (95, 95), (97, 122)] n || inIv llIv n
/-- candidate: later character of an identifier, over code points -/
def idRestC (n : Nat) : Bool := inIv [(48, 57), (65, 90), (95, 95), (97, 122), (39, 39), (33, 33), (63, 63)] n
  || inIv llIv n || inIv subIv n

theorem idFirst_eq (c : Char) : Lean.isIdFirst c = idFirstC c.val.toNat := by
  rw [Bool.eq_iff_iff]
  simp [Lean.isIdFirst, idFirstC, Char.isAlpha, Char.isUpper, Char.isLower, inIv, Char.ext_iff, llIv, List.any_cons, List.any_nil, letterLike_eq, UInt32.le_iff_toNat_le, ← UInt32.toNat_inj]
  omega

theorem idRest_eq (c : Char) : Lean.isIdRest c = idRestC c.val.toNat := by
  rw [Bool.eq_iff_iff]
  simp [Lean.isIdRest, idRestC, Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit, inIv, Char.ext_iff,
    llIv, subIv, List.any_cons, List.any_nil, letterLike_eq, subScript_eq, UInt32.le_iff_toNat_le, ← UInt32.toNat_inj]
  omega

/-- subset form for a lexer: the candidate accepting a code point means Lean accepts that `Char` -/
theorem idFirstC_imp (c : Char) (h : idFirstC c.val.toNat = true) : Lean.isIdFirst c = true := (idFirst_eq c).symm ▸ h
theorem idRestC_imp (c : Char) (h : idRestC c.val.toNat = true) : Lean.isIdRest c = true := (idRest_eq c).symm ▸ h

/-- the holes matter: `λ` (fun), `Π`, `Σ`, `×`, `÷` are never identifier characters (so `λx` is not one name) -/
theorem holes : ∀ c ∈ ['λ', 'Π', 'Σ', '×', '÷'], Lean.isIdFirst c = false ∧ Lean.isIdRest c = false := by decide +kernel

end H3
