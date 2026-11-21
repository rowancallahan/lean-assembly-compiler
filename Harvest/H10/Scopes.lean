/- Harvest/H10/Scopes: `namespace` / `section` / `end` balance (Lean/Elab/BuiltinCommand.lean:62-84, 130-137, 241-262).
Lean's `elabEnd` is monadic over the scope stack (`Scope.header : String`, innermost first, one extra root scope with
header "").  Its decision part is a total function of the header list and the end name; `nameOfScopes` is a `private`
total def, copied here (transcription).  Candidate nano rule: the same stack on `List String`.
nano today SKIPS these lines (`LexSpec.lineKw`) without tracking scopes: `end` alone is accepted (F3), Lean rejects. -/
import Nano.Lexer.Lex2Spec
import Lean.Data.Name
namespace H10
open Lean

/-- `nameOfScopes` (BuiltinCommand.lean:130), on the header strings -/
def nameOfScopes : List String → (n : Nat) → Name
  | _, 0 => .anonymous
  | [], _ => .anonymous
  | s :: ss, n + 1 => if s == "" then .anonymous else .str (nameOfScopes ss n) s

/-- the name `A.B.C` from its parts innermost-first, `[C, B, A]` -/
def nameOf : List String → Name
  | [] => .anonymous
  | s :: p => .str (nameOf p) s

/-- Lean's `elabEnd` decision (BuiltinCommand.lean:241): `hs` = scope headers innermost first INCLUDING the root `""`;
`hdr` = the written name, parts innermost-first; result = headers after, or none = error -/
def leanEnd (hs : List String) (hdr : Option (List String)) : Option (List String) :=
  let endSize := match hdr with | none => 1 | some n => (nameOf n).getNumParts
  if hs.length == 1 then none
  else match hdr with
    | none => if hs.head? == some "" then some (hs.drop endSize) else none
    | some h => if endSize ≥ hs.length then none
                else if nameOfScopes hs endSize == nameOf h then some (hs.drop endSize) else none

/-- candidate nano rule: pop exactly the written parts, each equal to the scope header, innermost first;
unnamed `end` pops one anonymous scope; the root is never popped -/
def nanoEnd : List String → Option (List String) → Option (List String)
  | hs, none => match hs with | "" :: t@(_ :: _) => some t | _ => none
  | hs, some h => if h ≠ [] ∧ h.length < hs.length ∧ h.all (· != "") = true ∧ hs.take h.length = h
                  then some (hs.drop h.length) else none

theorem nameOf_numParts : ∀ p : List String, (nameOf p).getNumParts = p.length := by
  intro p; induction p with
  | nil => rfl
  | cons s p ih => simp [nameOf, Name.getNumParts, ih]

theorem nameOfScopes_take : ∀ (h hs : List String), h.length < hs.length + 1 → h.all (· != "") = true →
    hs.take h.length = h → nameOfScopes hs h.length = nameOf h := by
  intro h; induction h with
  | nil => intro hs _ _ _; simp [nameOfScopes, nameOf]
  | cons s h ih =>
    intro hs hl ha ht
    cases hs with
    | nil => simp at hl
    | cons t hs =>
      simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at ht hl
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
      obtain ⟨rfl, ht2⟩ := ht
      simp only [List.length_cons, nameOfScopes, nameOf, beq_iff_eq]
      rw [if_neg ha.1, ih hs (by omega) ha.2 ht2]

/-- SOUNDNESS (subset): whenever the nano rule accepts an `end`, Lean's `elabEnd` accepts it and reaches the same scopes -/
theorem nanoEnd_sound (hs : List String) (hdr : Option (List String)) (t : List String)
    (h : nanoEnd hs hdr = some t) : leanEnd hs hdr = some t := by
  cases hdr with
  | none =>
    match hs, h with
    | [], h => simp [nanoEnd] at h
    | [_], h => simp [nanoEnd] at h
    | (a :: u :: v), h => by_cases ha : a = ""
                          · subst ha; simp [nanoEnd] at h; subst h; simp [leanEnd]
                          · simp [nanoEnd, ha] at h
  | some hh =>
    simp only [nanoEnd] at h
    split at h
    · rename_i c
      obtain ⟨c0, c1, c2, c3⟩ := c
      simp only [Option.some.injEq] at h
      subst h
      have hl : 2 ≤ hs.length := by
        cases hh with | nil => exact absurd rfl c0 | cons _ _ => simp at c1; omega
      simp only [leanEnd, nameOf_numParts]
      rw [if_neg (by simp; omega), if_neg (by omega)]
      simp [nameOfScopes_take hh hs (by omega) c2 c3]
    · simp at h

/-- F3: a stray `end` (no open scope): nano's lexer skips the line, Lean's `elabEnd` fails ("invalid 'end', insufficient scopes") -/
theorem F3_nano_accepts : (LexSpec.step ("end\n".toList.map fun c => c.toNat.toUInt8)).isSome = true := by decide +kernel
theorem F3_lean_rejects : leanEnd [""] none = none := by decide +kernel
theorem F3_nano_rule_rejects : nanoEnd [""] none = none := by decide +kernel
end H10
