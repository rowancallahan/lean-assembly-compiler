/- nano: the NON-INLINED elaboration and `inlineProg` (integration, nano-int).
The spec `nanoElab` (`Nano/Elab.lean`, unchanged) inlines every call: `Ex.call body args` carries the callee's
elaborated body, so its output can be exponentially longer than the source and a byte-level front end needs unbounded
memory to produce it.  Here the SAME parser functions are run with a def table whose bodies are index markers
(`Ex.var j` for the j-th def): a call is then `Ex.call (Ex.var j) args`, the output is linear in the source.
`nanoElab_eq : nanoElab xs = (nanoElabU xs).map inlineProg`: the spec is the non-inlined elaboration followed by
inlining (the parser treats def bodies opaquely: `par`). -/
import Legacy.Nano.Elab

namespace Nano.U
open Nano

/-- a call body: a marker `Ex.var j` stands for def `j` -/
def mkB (σ : Nat → Ex) : Ex → Ex
  | .var j => σ j
  | b => b

/-- replace the markers in call position -/
def sub (σ : Nat → Ex) : Ex → Ex
  | .num n => .num n
  | .var i => .var i
  | .add a b => .add (sub σ a) (sub σ b)
  | .sub a b => .sub (sub σ a) (sub σ b)
  | .mul a b => .mul (sub σ a) (sub σ b)
  | .let_ v b => .let_ (sub σ v) (sub σ b)
  | .call b as => .call (mkB σ b) (sub σ as)
  | .anil => .anil
  | .acons e r => .acons (sub σ e) (sub σ r)

/-- a def table entry with its body replaced -/
def T (σ : Nat → Ex) (d : List UInt8 × Nat × Ex) : List UInt8 × Nat × Ex := (d.1, d.2.1, mkB σ d.2.2)

/-- a parser result with the markers replaced -/
def S (σ : Nat → Ex) (r : Ex × List Tok) : Ex × List Tok := (sub σ r.1, r.2)

theorem findDef_map (σ : Nat → Ex) (g : List UInt8) : ∀ ds : Defs,
    findDef g (ds.map (T σ)) = (findDef g ds).map fun kb => (kb.1, mkB σ kb.2)
  | [] => rfl
  | (n, a, b) :: ds => by
    simp only [List.map_cons, T, findDef]
    split
    · rfl
    · exact findDef_map σ g ds

/-- **the parser commutes with replacing def bodies** -/
theorem par (σ : Nat → Ex) (ds : Defs) : ∀ f : Nat,
    (∀ sc ts, pExpr f sc (ds.map (T σ)) ts = (pExpr f sc ds ts).map (S σ)) ∧
    (∀ sc acc ts, pAdd f sc (ds.map (T σ)) (sub σ acc) ts = (pAdd f sc ds acc ts).map (S σ)) ∧
    (∀ sc ts, pMul f sc (ds.map (T σ)) ts = (pMul f sc ds ts).map (S σ)) ∧
    (∀ sc acc ts, pMulT f sc (ds.map (T σ)) (sub σ acc) ts = (pMulT f sc ds acc ts).map (S σ)) ∧
    (∀ sc ts, pApp f sc (ds.map (T σ)) ts = (pApp f sc ds ts).map (S σ)) ∧
    (∀ sc k ts, pArgs f sc (ds.map (T σ)) k ts = (pArgs f sc ds k ts).map (S σ)) ∧
    (∀ sc ts, pAtom f sc (ds.map (T σ)) ts = (pAtom f sc ds ts).map (S σ))
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp [pExpr, pAdd, pMul, pMulT, pApp, pArgs, pAtom]
  | f + 1 => by
    obtain ⟨hE, hA, hM, hT, hP, hG, hO⟩ := par σ ds f
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro sc ts
      unfold pExpr
      split
      · rename_i h; cases h
      · rename_i h; cases h
        rw [hE]
        cases h1 : pExpr f _ ds _ with
        | none => rfl
        | some vr =>
          obtain ⟨v, r⟩ := vr
          rcases r with _ | ⟨t, r⟩
          · rfl
          · cases t <;> try rfl
            simp only [Option.map, S]
            rw [hE]
            cases h2 : pExpr f _ ds r with
            | none => rfl
            | some br => rfl
      · rename_i h _; cases h
        rw [hM]
        cases h1 : pMul f _ ds _ with
        | none => rfl
        | some vr => obtain ⟨v, r⟩ := vr; exact hA _ v r
    · intro sc acc ts
      unfold pAdd
      split
      · rename_i h; cases h
      · rename_i h; cases h
        rw [hM]
        cases h1 : pMul f _ ds _ with
        | none => rfl
        | some vr => obtain ⟨v, r⟩ := vr; exact hA _ (Ex.add acc v) r
      · rename_i h; cases h
        rw [hM]
        cases h1 : pMul f _ ds _ with
        | none => rfl
        | some vr => obtain ⟨v, r⟩ := vr; exact hA _ (Ex.sub acc v) r
      · rfl
    · intro sc ts
      simp only [pMul]
      rw [hP]
      cases h1 : pApp f _ ds _ with
      | none => rfl
      | some vr => obtain ⟨v, r⟩ := vr; exact hT _ v r
    · intro sc acc ts
      unfold pMulT
      split
      · rename_i h; cases h
      · rename_i h; cases h
        rw [hP]
        cases h1 : pApp f _ ds _ with
        | none => rfl
        | some vr => obtain ⟨v, r⟩ := vr; exact hT _ (Ex.mul acc v) r
      · rfl
    · intro sc ts
      unfold pApp
      split
      · rename_i h; cases h
      · rename_i h; cases h
        cases h0 : idx _ _ 0 with
        | some i => rfl
        | none =>
          simp only [findDef_map]
          cases h1 : findDef _ ds with
          | none => rfl
          | some kb =>
            obtain ⟨k, b⟩ := kb
            simp only [Option.map]
            rw [hG]
            cases h2 : pArgs f _ ds k _ with
            | none => rfl
            | some vr => rfl
      · rfl
      · rename_i h _ _; cases h
        exact hO _ _
    · intro sc k ts
      unfold pArgs
      split
      · rename_i h; cases h
      · rfl
      · rename_i h; cases h
        rw [hO]
        cases h1 : pAtom f _ ds _ with
        | none => rfl
        | some vr =>
          obtain ⟨v, r⟩ := vr
          simp only [Option.map, S]
          rw [hG]
          cases h2 : pArgs f _ ds _ r with
          | none => rfl
          | some vr => rfl
    · intro sc ts
      unfold pAtom
      split
      · rename_i h; cases h
      · rfl
      · cases h0 : idx _ _ 0 with
        | some i => rfl
        | none =>
          simp only [findDef_map]
          cases h1 : findDef _ ds with
          | none => rfl
          | some kb =>
            obtain ⟨k, b⟩ := kb
            cases k <;> rfl
      · rename_i h; cases h
        rw [hE]
        cases h1 : pExpr f _ ds _ with
        | none => rfl
        | some vr =>
          obtain ⟨v, r⟩ := vr
          rcases r with _ | ⟨t, r⟩
          · rfl
          · cases t <;> rfl
      · rfl

/-! ## Programs: the defs with marker bodies, and inlining -/

/-- the marker environment of the bodies so far (oldest first) -/
def σof (B : List Ex) : Nat → Ex := fun j => B.getD j .anil

/-- the inlined bodies (oldest first) of non-inlined defs given newest first -/
def realBodies : List (Nat × Ex) → List Ex
  | [] => []
  | (_, e) :: older => realBodies older ++ [sub (σof (realBodies older)) e]

/-- **inlining**: the program (entry arity, entry body) of the non-inlined defs (newest first) -/
def inlineProg : List (Nat × Ex) → Prog
  | [] => (0, .anil)
  | (n, e) :: older => (n, sub (σof (realBodies older)) e)

/-- `pDefs` with index markers as def bodies: all defs (arity, body), newest first -/
def pDefsU : Nat → Defs → List (Nat × Ex) → List Tok → Option (List (Nat × Ex))
  | 0, _, _, _ => none
  | f + 1, ds, acc, Tok.kdef :: Tok.id g :: ts =>
    match pParams f [] 0 ts with
    | some (sc, n, Tok.colon :: Tok.kty _ :: Tok.assign :: r) =>
      match (match findDef g ds with | some _ => none | none => pExpr f sc ds r) with
      | some (e, []) => some ((n, e) :: acc)
      | some (e, r2) => pDefsU f ((g, n, Ex.var acc.length) :: ds) ((n, e) :: acc) r2
      | none => none
    | _ => none
  | _, _, _, _ => none

/-- **the non-inlined elaboration** (a call is `Ex.call (Ex.var j) args`, `j` = the callee's number) -/
def nanoElabU (xs : List UInt8) : Option (List (Nat × Ex)) :=
  match (if adjOk xs then lex xs.length xs else none) with
  | some ts =>
    match uniTy none ts with
    | some _ => pDefsU (ts.length + 1) [] [] ts
    | none => none
  | none => none

theorem length_realBodies : ∀ acc : List (Nat × Ex), (realBodies acc).length = acc.length
  | [] => rfl
  | (_, e) :: older => by simp [realBodies, length_realBodies older]

/-- every body of the marker table is a marker of an existing def -/
def Good (ds : Defs) (acc : List (Nat × Ex)) : Prop := ∀ d ∈ ds, ∃ j, d.2.2 = Ex.var j ∧ j < acc.length

theorem step_tab {ds : Defs} {acc : List (Nat × Ex)} (hg : Good ds acc) (g : List UInt8) (n : Nat) (e : Ex) :
    (g, n, sub (σof (realBodies acc)) e) :: ds.map (T (σof (realBodies acc))) =
      ((g, n, Ex.var acc.length) :: ds).map (T (σof (realBodies ((n, e) :: acc)))) ∧
    Good ((g, n, Ex.var acc.length) :: ds) ((n, e) :: acc) := by
  have hl := length_realBodies acc
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, realBodies]
    congr 1
    · simp only [T, mkB, σof]
      rw [← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]; simp
    · apply List.map_congr_left
      intro d hd
      obtain ⟨j, hj, hlt⟩ := hg d hd
      obtain ⟨a, b, c⟩ := d
      simp only at hj; subst hj
      simp only [T, mkB, σof]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  · intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨acc.length, rfl, by simp⟩
    · obtain ⟨j, hj, hlt⟩ := hg d hd
      exact ⟨j, hj, by simp; omega⟩

/-- `pDefs` on the real table = `pDefsU` on the marker table, then inlining -/
theorem pDefs_eq : ∀ (f : Nat) (ds : Defs) (acc : List (Nat × Ex)) (ts : List Tok), Good ds acc →
    pDefs f (ds.map (T (σof (realBodies acc)))) ts = (pDefsU f ds acc ts).map inlineProg
  | 0, ds, acc, ts, _ => by simp [pDefs, pDefsU]
  | f + 1, ds, acc, ts, hg => by
    unfold pDefs
    split
    · rename_i h; cases h
    · rename_i f' ds' g ts' h
      cases h
      simp only [pDefsU]
      split
      · rename_i sc n s r hp
        simp only [hp, findDef_map]
        cases hf : findDef g ds with
        | some kb => rfl
        | none =>
          simp only [Option.map]
          rw [(par (σof (realBodies acc)) ds f).1]
          cases he : pExpr f sc ds r with
          | none => rfl
          | some er =>
            obtain ⟨e, r2⟩ := er
            rcases r2 with _ | ⟨t, r2⟩
            · rfl
            · simp only [Option.map, S]
              rw [(step_tab hg g n e).1]
              exact pDefs_eq f _ _ _ (step_tab hg g n e).2
      · rename_i hno
        split
        · rename_i hp2; exact absurd hp2 (hno _ _ _ _)
        · rfl
    · rename_i h
      unfold pDefsU
      split
      · rename_i h2; cases h2
      · exact (h _ _ _ (by assumption) rfl).elim
      · rfl

/-- **the spec is the non-inlined elaboration followed by inlining** -/
theorem nanoElab_eq (xs : List UInt8) : nanoElab xs = (nanoElabU xs).map inlineProg := by
  unfold nanoElab nanoElabT nanoElabU
  cases hl : (if adjOk xs = true then lex xs.length xs else none) with
  | none => rfl
  | some ts =>
    cases hu : uniTy none ts with
    | none => simp only [hu]; rfl
    | some s =>
      have := pDefs_eq (ts.length + 1) [] [] ts (fun d hd => absurd hd List.not_mem_nil)
      simp only [List.map_nil] at this
      simp only [hu, this]
      cases pDefsU (ts.length + 1) [] [] ts <;> rfl

end Nano.U
