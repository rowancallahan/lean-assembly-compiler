/- Harvest/H3/Names: «escaped» components and dotted names.  Total Lean 4.34.1 leaves: `idBeginEscape`/`idEndEscape`
(Init/Meta/Defs.lean:139-142), `Name.escapePart` (Init/Data/ToString/Name.lean:55, total when `force = true`: the
partial `needsNoEscapeAsciiRest` is never reached), `Name.toStringWithSep` (:73, structural), `Name.getRoot`
(Init/Meta/Defs.lean:144).  The reading side (`identFnAux`, `Parser/Basic.lean:975`) is `partial`: not provable. -/
import Harvest.H3.Utf8
namespace H3

/-- candidate: the bytes `C2 AB` open an escaped component, `C2 BB` close it (UTF-8 of « and ») -/
def escOpen (b0 b1 : UInt8) : Bool := b0 == 0xC2 && b1 == 0xAB
def escClose (b0 b1 : UInt8) : Bool := b0 == 0xC2 && b1 == 0xBB

theorem escOpen_lean (b0 b1 : UInt8) (h : escOpen b0 b1 = true) :
    ((ByteArray.mk #[b0, b1]).utf8DecodeChar? 0).map Lean.isIdBeginEscape = some true := by
  simp only [escOpen, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h; decide +kernel
theorem escClose_lean (b0 b1 : UInt8) (h : escClose b0 b1 = true) :
    ((ByteArray.mk #[b0, b1]).utf8DecodeChar? 0).map Lean.isIdEndEscape = some true := by
  simp only [escClose, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h; decide +kernel
/-- and the two bytes decode to nothing else: the bracket is exactly these two code points -/
theorem esc_unique : ∀ c : Char, (Lean.isIdBeginEscape c = true ↔ c.val = 0xAB) ∧ (Lean.isIdEndEscape c = true ↔ c.val = 0xBB) := by
  intro c; simp [Lean.isIdBeginEscape, Lean.isIdEndEscape, Lean.idBeginEscape, Lean.idEndEscape, Char.ext_iff]

/-- candidate: the text of an escaped component is `«` s `»` where `s` has no `»` (so the first `»` ends it) -/
def escComp (s : String) : String := "«" ++ s ++ "»"

theorem escapePart_force (s : String) (h : s.any Lean.isIdEndEscape = false) :
    Lean.Name.escapePart s true = some (escComp s) := by
  unfold Lean.Name.escapePart
  split <;> simp_all [escComp]
  all_goals rfl

theorem escapePart_force_none (s : String) (h0 : 0 < s.utf8ByteSize) (h : s.any Lean.isIdEndEscape = true) :
    Lean.Name.escapePart s true = none := by
  simp [Lean.Name.escapePart, h0, h]

/-- candidate: a dotted name is its components, each further one preceded by `.` (`.` is not an identifier char) -/
def mkName (c : String) (cs : List String) : Lean.Name := cs.foldl Lean.Name.str (Lean.Name.str .anonymous c)

private theorem foldl_str (xs : List String) (n : Lean.Name) (a : Lean.Name) (b : String) (h : n = .str a b) :
    ∃ a' b', xs.foldl Lean.Name.str n = .str a' b' := by
  induction xs generalizing n a b with
  | nil => exact ⟨a, b, h⟩
  | cons x xs ih => exact ih (.str n x) n x rfl

private theorem ts_str (a : Lean.Name) (b x : String) :
    Lean.Name.toStringWithSep "." false (.str (.str a b) x) =
      Lean.Name.toStringWithSep "." false (.str a b) ++ "." ++ x := by
  simp [Lean.Name.toStringWithSep]; rfl

/-- `.c1.c2…` : each further component preceded by a dot -/
def joinDots : List String → String
  | [] => ""
  | x :: xs => "." ++ x ++ joinDots xs

private theorem ts_fold (cs : List String) (a : Lean.Name) (b : String) :
    Lean.Name.toStringWithSep "." false (cs.foldl Lean.Name.str (.str a b)) =
      Lean.Name.toStringWithSep "." false (.str a b) ++ joinDots cs := by
  induction cs generalizing a b with
  | nil => simp [joinDots]
  | cons x cs ih =>
    rw [List.foldl_cons, ih, ts_str]
    simp [joinDots, String.append_assoc]

theorem toString_mkName (c : String) (cs : List String) :
    Lean.Name.toStringWithSep "." false (mkName c cs) = c ++ joinDots cs := by
  unfold mkName
  rw [ts_fold]
  simp [Lean.Name.toStringWithSep]; rfl

theorem getRoot_mkName (c : String) (cs : List String) : (mkName c cs).getRoot = Lean.Name.str .anonymous c := by
  unfold mkName
  suffices ∀ (cs : List String) (a : Lean.Name) (b : String), (cs.foldl Lean.Name.str (.str a b)).getRoot = (Lean.Name.str a b).getRoot by
    rw [this]; rfl
  intro cs
  induction cs with
  | nil => intros; rfl
  | cons x cs ih => intro a b; rw [List.foldl_cons, ih]; rfl

theorem dot_not_idRest : Lean.isIdRest '.' = false ∧ Lean.isIdFirst '.' = false := by decide +kernel

end H3
