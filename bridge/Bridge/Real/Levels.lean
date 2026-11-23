/- Bridge.Real.Levels: level assignments (finding (a)) against real con-leche.

`Denotes.const` reads `cval n (substFn φ ps us)` with `ps` the constant's OWN stored level parameters.  Two
occurrences of the same constant (inside different heads' types, or in the program) are read at different
assignments; `CvalParams` (model_exists', Bridge.ModelExists2) makes `cval n` depend only on `ps`, so the two
agree as soon as their level arguments EVALUATE to the same numbers (`const_agree`). -/
import Bridge.ModelExists2
import Bridge.Transfer

namespace Bridge.Real
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.ModelExists2

universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-- `substFn` at two assignments agrees on the parameters when the level arguments evaluate alike. -/
theorem substFn_agree (φ φ' : LevelParam → Nat) :
    ∀ (ps : List LevelParam) (us us' : List Level), us.map (Level.eval φ) = us'.map (Level.eval φ') →
      us.length = ps.length → ∀ p ∈ ps, Level.substFn φ ps us p = Level.substFn φ' ps us' p
  | [], _, _, _, _, p, hp => absurd hp List.not_mem_nil
  | k :: ks, u :: us, u' :: us', h, hl, p, hp => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [Level.substFn]
      by_cases hk : k = p
      · simp [hk, h.1]
      · simp only [hk, ite_false]
        have hp' : p ∈ ks := by
          rcases List.mem_cons.mp hp with rfl | h'
          · exact absurd rfl hk
          · exact h'
        exact substFn_agree φ φ' ks us us' h.2 (by simpa using hl) p hp'
  | k :: ks, [], _, _, hl, _, _ => by simp at hl
  | k :: ks, u :: us, [], h, _, _, _ => by simp at h

/-- **Two occurrences of one stored constant whose level arguments evaluate alike denote the same set.** -/
theorem const_agree {M : Model V env} (hP : CvalParams M) {n : Name} {us us' : List Level}
    {φ φ' : LevelParam → Nat} {ρ ρ' : BVarIdx → V} {X Y : V}
    (hX : Denotes M.cval env φ ρ (.const n us) X) (hY : Denotes M.cval env φ' ρ' (.const n us') Y)
    (h : us.map (Level.eval φ) = us'.map (Level.eval φ')) : X = Y := by
  cases hX with
  | const hf hl =>
    cases hY with
    | const hf' hl' =>
      rw [hf] at hf'; cases hf'
      exact hP n _ hf _ _ (substFn_agree φ φ' _ us us' h hl)

/-- level-free constants: φ-independent -/
theorem const_agree0 {M : Model V env} (hP : CvalParams M) {n : Name}
    {φ φ' : LevelParam → Nat} {ρ ρ' : BVarIdx → V} {X Y : V}
    (hX : Denotes M.cval env φ ρ (.const n []) X) (hY : Denotes M.cval env φ' ρ' (.const n []) Y) : X = Y :=
  const_agree hP hX hY rfl

end Bridge.Real
