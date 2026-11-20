/- Nano/V2Self/Proof/Parser/ParRunStar: generic facts about Layer-2 runs (`ParRun.Star`): step counting, determinism, and the frame
discipline "a run of `k ++ ks` to the empty stack first runs `k` to the empty stack, leaving `ks` untouched". -/
import Nano.V2Self.Proof.Parser.ParRun
namespace ParRun

/-- `Star` with its number of steps (for strong induction) -/
inductive StarN : Nat → List Frame × St → List Frame × St → Prop
  | refl (c) : StarN 0 c c
  | step {n c d e} : stepS c = some d → StarN n d e → StarN (n + 1) c e

theorem StarN.toStar {n c e} (h : StarN n c e) : Star c e := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs ih

theorem Star.toN {c e} (h : Star c e) : ∃ n, StarN n c e := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | step hs _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .step hs h⟩

theorem Star.trans {a b c} (h1 : Star a b) (h2 : Star b c) : Star a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

theorem stepS_cons (f : Frame) (fs : List Frame) (st : St) :
    stepS (f :: fs, st) = (stepF f st).map fun (k, st') => (k ++ fs, st') := rfl

theorem stepS_some {f fs st d} : stepS (f :: fs, st) = some d ↔ ∃ k st', stepF f st = some (k, st') ∧ d = (k ++ fs, st') := by
  rw [stepS_cons]; cases h : stepF f st with
  | none => simp
  | some x =>
    obtain ⟨k, st'⟩ := x
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨_, _, rfl, rfl⟩
    · rintro ⟨_, _, h1, rfl⟩; cases h1; rfl

/-- frame discipline (lifting): a run of `k` lifts to a run of `k ++ ks` that stops at `ks` -/
theorem Star.append {k st kf stf} (ks : List Frame) (h : Star (k, st) (kf, stf)) : Star (k ++ ks, st) (kf ++ ks, stf) := by
  generalize hc : (k, st) = c at h
  generalize he : (kf, stf) = e at h
  induction h generalizing k st with
  | refl => cases hc; cases he; exact .refl _
  | step hs _ ih =>
    subst hc
    match k, hs with
    | f :: k', hs =>
      obtain ⟨k2, st2, h2, rfl⟩ := stepS_some.mp hs
      have := ih (k := k2 ++ k') (st := st2) rfl he
      rw [List.append_assoc] at this
      exact .step (stepS_some.mpr ⟨k2, st2, h2, rfl⟩) this

theorem StarN.zero_nil {fs st fin} (h : StarN 0 (fs, st) ([], fin)) : fs = [] ∧ fin = st := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩

/-- frame discipline (splitting): a run of `k ++ ks` to the empty stack passes through `ks` -/
theorem StarN.split {n k ks st fin} (h : StarN n (k ++ ks, st) ([], fin)) :
    ∃ st' n1 n2, n1 + n2 = n ∧ StarN n1 (k, st) ([], st') ∧ StarN n2 (ks, st') ([], fin) := by
  induction n generalizing k st with
  | zero =>
    have h0 := h.zero_nil
    obtain ⟨hk, rfl⟩ := h0
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hk
    exact ⟨_, 0, 0, rfl, .refl _, .refl _⟩
  | succ n ih =>
    match k with
    | [] => exact ⟨st, 0, n + 1, by omega, .refl _, h⟩
    | f :: k' =>
      cases h with
      | step hs h' =>
        rw [List.cons_append] at hs
        obtain ⟨k2, st2, h2, rfl⟩ := stepS_some.mp hs
        rw [← List.append_assoc] at h'
        obtain ⟨st', n1, n2, hn, r1, r2⟩ := ih h'
        exact ⟨st', n1 + 1, n2, by omega, .step (stepS_some.mpr ⟨_, _, h2, rfl⟩) r1, r2⟩

/-- one step of a single frame inside a larger stack -/
theorem StarN.head {n f fs st fin} (h : StarN (n + 1) (f :: fs, st) ([], fin)) :
    ∃ k st', stepF f st = some (k, st') ∧ StarN n (k ++ fs, st') ([], fin) := by
  cases h with
  | step hs h' =>
    obtain ⟨k2, st2, h2, rfl⟩ := stepS_some.mp hs
    exact ⟨k2, st2, h2, h'⟩


end ParRun
