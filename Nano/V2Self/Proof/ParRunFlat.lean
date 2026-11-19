/- Nano/V2Self/Proof/ParRunFlat: Layer 2, the FLATTEN tasks (codes 81 / 82, v142 / v143).  `RN.words n` = the words v142/v143 emit for
the arena tree `n` (input locals skipped everywhere, the first child of rd/len/len' skipped, a CONTINUE state tuple with one
non-input component flattened away).  `flat_run`: the frame `flat n` always runs to its continuation with `out ++ n.words`. -/
import Nano.V2Self.Proof.ParRunStar
namespace ParRun
open ParSpec

/-- header words of a node (v142), given the number of input-local children `ni` -/
def hdr (t a b nk ni : Nat) : List UInt64 :=
  [t.toUInt64] ++ (if t = 6 then [(nk - ni).toUInt64] else if t < 10 then [a.toUInt64] else []) ++
    (if t = 2 ∨ t = 5 then [b.toUInt64] else if t = 8 then [(b - ni).toUInt64] else [])

mutual
def RN.words : RN → List UInt64
  | .mk t a b _ _ ks =>
    let ni := (ks.filter RN.isInp).length
    if t = 6 ∧ ks.length - ni = 1 then RN.wordsL ks else
    hdr t a b ks.length ni ++
      (if t = 9 ∧ a < 4 then (match ks with | [] => [] | _ :: r => RN.wordsL r) else RN.wordsL ks)
def RN.wordsL : List RN → List UInt64
  | [] => []
  | n :: r => (if n.isInp then [] else RN.words n) ++ RN.wordsL r
end

/-- deterministic cut: a run to `[]` passes through every configuration reachable on the way -/
theorem Star.cut {c d fin} (h1 : Star c d) (h2 : Star c ([], fin)) : Star d ([], fin) := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih =>
    cases h2 with
    | refl => simp [stepS] at hs
    | step hs' h2' => rw [hs] at hs'; cases hs'; exact ih h2'

theorem Star.one {f fs st k st'} (h : stepF f st = some (k, st')) : Star (f :: fs, st) (k ++ fs, st') :=
  .step (stepS_some.mpr ⟨k, st', h, rfl⟩) (.refl _)

theorem RN.words_mk (t a b : Nat) (sh : Option Sh) (p : Bool) (ks : List RN) : RN.words (.mk t a b sh p ks) =
    if t = 6 ∧ ks.length - (ks.filter RN.isInp).length = 1 then RN.wordsL ks else
    hdr t a b ks.length (ks.filter RN.isInp).length ++
      (if t = 9 ∧ a < 4 then (match ks with | [] => [] | _ :: r => RN.wordsL r) else RN.wordsL ks) := by
  rw [RN.words.eq_def]

theorem RN.wordsL_cons (n : RN) (r : List RN) : RN.wordsL (n :: r) = (if n.isInp then [] else RN.words n) ++ RN.wordsL r := by
  rw [RN.wordsL]

theorem RN.tail_words {ks : List RN} :
    (match ks with | [] => [] | _ :: r => RN.wordsL r) = RN.wordsL ks.tail := by
  cases ks <;> rfl

mutual
theorem flat_run (n : RN) (ks : List Frame) (st : St) :
    Star (.flat n :: ks, st) (ks, { st with out := st.out ++ n.words }) := by
  match n with
  | .mk t a b sh p kd =>
    by_cases h6 : t = 6 ∧ kd.length - (kd.filter RN.isInp).length = 1
    · have hs : stepF (.flat (.mk t a b sh p kd)) st = some ([.flatL kd], st) := by
        simp only [stepF, RN.kids, RN.tag]; rw [if_pos h6]
      refine (Star.one hs).trans ?_
      rw [RN.words_mk, if_pos h6]
      exact flatL_run kd ks st
    · have hs : stepF (.flat (.mk t a b sh p kd)) st =
          some ([.flatL (if t = 9 ∧ a < 4 then kd.tail else kd)], { st with out := st.out ++ hdr t a b kd.length (kd.filter RN.isInp).length }) := by
        simp only [stepF, RN.kids, RN.tag, RN.a, RN.b]; rw [if_neg h6]; simp [hdr]
      refine (Star.one hs).trans ?_
      rw [RN.words_mk, if_neg h6, RN.tail_words]
      by_cases hp : t = 9 ∧ a < 4
      · simp only [if_pos hp]
        match kd with
        | [] => simpa using flatL_run [] ks { st with out := st.out ++ hdr t a b 0 0 }
        | k0 :: r => simpa using flatL_run r ks { st with out := st.out ++ hdr t a b (k0 :: r).length ((k0 :: r).filter RN.isInp).length }
      · simp only [if_neg hp]
        simpa using flatL_run kd ks { st with out := st.out ++ hdr t a b kd.length (kd.filter RN.isInp).length }
theorem flatL_run (ns : List RN) (ks : List Frame) (st : St) :
    Star (.flatL ns :: ks, st) (ks, { st with out := st.out ++ RN.wordsL ns }) := by
  match ns with
  | [] =>
    have hs : stepF (.flatL []) st = some ([], st) := rfl
    simpa [RN.wordsL] using Star.one (fs := ks) hs
  | n :: r =>
    by_cases hi : n.isInp
    · have hs : stepF (.flatL (n :: r)) st = some ([.flatL r], st) := by simp [stepF, hi]
      refine (Star.one hs).trans ?_
      rw [RN.wordsL_cons, if_pos hi, List.nil_append]; exact flatL_run r ks st
    · have hs : stepF (.flatL (n :: r)) st = some ([.flat n, .flatL r], st) := by simp [stepF, hi]
      refine (Star.one hs).trans ?_
      refine (flat_run n (.flatL r :: ks) st).trans ?_
      rw [RN.wordsL_cons, if_neg hi, ← List.append_assoc]; exact flatL_run r ks { st with out := st.out ++ n.words }
end

end ParRun
