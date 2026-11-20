/- nano stage 2, layer A: an explicit gas.  Every step that continues lowers `Φ = 13·(tokens left) + 3·(frames) +
κ(control)`, so `13 · ts.length + 6` steps are enough (`run_enough`); `stage2` (gas fixed) is then exactly the
non-inlined elaboration on stage 1's bytes (`stage2_lexB`). -/
import Legacy.Nano.ParseBTop

namespace Nano.PB
open Nano Nano.U Nano.B

def κ : Ctl → Nat
  | .defs _ => 5 | .params _ _ => 7 | .names _ _ _ => 7 | .dbody => 6
  | .expr _ => 17 | .add _ => 11 | .mul _ => 13 | .mulT _ => 11 | .app _ => 9 | .args _ _ => 12
  | .atom _ => 8 | .ret => 10

def Φ (c : Ctl) (s : St) : Nat := 13 * s.ts.length + 3 * s.K.length + κ c

theorem step_dec (c c' : Ctl) (s s' : St) (h : step c s = .go c' s') : Φ c' s' < Φ c s := by
  rcases s with ⟨ts, out, d, sc, ds, K, cg, cf, na⟩
  cases c <;> simp only [step] at h
  all_goals (repeat' (split at h))
  all_goals (try (cases h; done))
  all_goals (try (simp only [endDef, retF] at h; repeat' (split at h)))
  all_goals (try (cases h; done))
  all_goals (repeat' (split at h))
  all_goals (try (cases h; done))
  all_goals (injection h with h1 h2; subst h1 h2; simp [Φ, κ]; try omega)

/-- more gas than `Φ` changes nothing -/
theorem run_stable : ∀ (g : Nat) (c : Ctl) (s : St), Φ c s < g → ∀ g', g ≤ g' → run g' c s = run g c s
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | g + 1, c, s, h, g', hg => by
    obtain ⟨g'', rfl⟩ : ∃ g'', g' = g'' + 1 := ⟨g' - 1, by omega⟩
    simp only [run]
    cases hs : step c s with
    | go c' s' =>
      have := step_dec c c' s s' hs
      exact run_stable g c' s' (by omega) g'' (by omega)
    | done o => rfl
    | fail => rfl

/-- the gas that is always enough -/
def gasOf (ts : List Tok) : Nat := 13 * ts.length + 6

theorem parseA_gas (ts : List Tok) (n : Nat) : parseA (gasOf ts + n) ts = parseA (gasOf ts) ts :=
  run_stable (gasOf ts) _ _ (by simp [Φ, κ, st0, gasOf]) _ (by omega)

/-- **stage 2 (layer A), gas fixed**: stage 1's bytes → `serU u`, or `[]` -/
def stage2 (bs : List UInt8) : List UInt8 :=
  match decL bs with
  | some (_, ts) => (parseA (gasOf ts) ts).getD []
  | none => []

/-- **stage 1 then stage 2 = the non-inlined elaboration, for every source** -/
theorem stage2_lexB (xs : List UInt8) :
    stage2 (lexB xs) = match nanoElabU xs with
      | some u => serU u
      | none => [] := by
  rw [nanoElabU_lexT]
  unfold stage2
  rw [lexB_eq]
  cases lexT xs with
  | none => rfl
  | some st =>
    obtain ⟨s, ts⟩ := st
    have h := parseA_eq ts
    simp only [Option.bind]
    cases hp : pDefsU (ts.length + 1) [] [] ts with
    | none => rw [hp] at h; simp [h]
    | some u =>
      rw [hp] at h
      obtain ⟨n, h⟩ := h
      have := h (gasOf ts)
      rw [parseA_gas] at this
      simp [this]

/-- the form of `selfHosted_four`'s premise `hfe` -/
theorem stage2_hfe (xs : List UInt8) (u : List (Nat × Ex)) (h : nanoElabU xs = some u) :
    stage2 (lexB xs) = serU u := by
  rw [stage2_lexB, h]

end Nano.PB
