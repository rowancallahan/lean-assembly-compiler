/- Nano/V2Self/Proof/ParRunObl: pure Layer-2 reachability facts for `Obl` (box B): `assignTy`, `selfP`, `prev`, `names`. -/
import Nano.V2Self.Proof.ParRunNames
import Nano.V2Self.Proof.ParRunDef
import Nano.V2Self.Proof.ParTokWF
namespace ParRun
open ParSpec

theorem mkNode_eq {st st' : St} {t a b : Nat} {s : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') : ∃ v ar, st' = { st with vals := v, arena := ar } := by
  unfold mkNode at h; split at h <;> cases h; exact ⟨_, _, rfl⟩

theorem locOf_eq {st st' : St} {bd : Bd} (h : locOf st bd = some st') : ∃ v ar, st' = { st with vals := v, arena := ar } := by
  unfold locOf at h; split at h <;> cases h; exact ⟨_, _, rfl⟩

def isTyF : Frame → Bool
  | .tyAtom | .tyCross | .tyPair _ | .rparen => true
  | _ => false

/-- per-handler facts behind the four obligations -/
theorem stepF_obl {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) :
    (st.ty.isSome = true → st'.ty.isSome = true) ∧
    (Frame.afterColon ∈ k → f = .defs ∧ k = [.tyAtom, .afterColon]) ∧
    (Frame.selfArgs ∈ k → k = [.selfArgs] ∧ st'.cur = st.cur ∧ st'.arm = true) ∧
    (Frame.zeroDone ∈ k → st'.cur.params ≠ []) ∧
    (f ≠ .defs ∨ k = [] → st.cur.params <+: st'.cur.params) ∧
    (st'.arm = true → st.arm = true ∨ f = .zeroDone) ∧
    (f = .defs → k ≠ [] → st'.arm = false) := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp_all [leaf]; done)
    | (cases h; simp_all; intro e; simp [e] at *)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | (obtain ⟨v, ar, rfl⟩ := mkNode_eq h2; simp_all; done)
       | (obtain ⟨v, ar, rfl⟩ := locOf_eq h2; simp_all; done)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨v, ar, rfl⟩ := mkNode_eq h2'
          first | (obtain ⟨v, ar, rfl⟩ := mkNode_eq h1) | cases h1
          all_goals simp_all))

theorem Star.lift {P : List Frame × St → Prop} (hp : ∀ {c d}, stepS c = some d → StkInv c → DInv c → P c → P d)
    {c d : List Frame × St} (h : Star c d) (hk : StkInv c) (hd : DInv c) (hi : P c) : P d := by
  induction h with
  | refl => exact hi
  | step hs _ ih => exact ih (stepS_stkinv hs hk) (stepS_dinv hs hk hd) (hp hs hk hd hi)

/-! ## assignTy: below an `.assign` there is always a pending `.tyAtom` until the type is set -/
def TA : List Frame → Bool
  | [] => true
  | .tyAtom :: _ => true
  | .assign .. :: _ => false
  | _ :: r => TA r

theorem stepF_ta {f : Frame} {st st' : St} {k rest : List Frame} (h : stepF f st = some (k, st'))
    (hi : st.ty.isSome = true ∨ TA (f :: rest) = true) : st'.ty.isSome = true ∨ TA (k ++ rest) = true := by
  rcases hi with hi | hi
  · exact .inl ((stepF_obl h).1 hi)
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp_all [TA, leaf]; done)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | (obtain ⟨v, ar, rfl⟩ := mkNode_eq h2; simp_all [TA]; done)
       | (obtain ⟨v, ar, rfl⟩ := locOf_eq h2; simp_all [TA]; done)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨v, ar, rfl⟩ := mkNode_eq h2'
          first | (obtain ⟨v, ar, rfl⟩ := mkNode_eq h1) | cases h1
          all_goals simp_all [TA]))

theorem reach_assignTy {toks : List Tok} {i sz : Nat} {fs : List Frame} {st : St}
    (h : Star ([.defs], init toks) (.assign i sz :: fs, st)) : st.ty.isSome = true := by
  have := h.lift (P := fun c => c.2.ty.isSome = true ∨ TA c.1 = true) (fun {c d} hs _ _ hi => by
      obtain ⟨fs, st⟩ := c
      cases fs with
      | nil => simp [stepS] at hs
      | cons f rest =>
        obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
        exact stepF_ta h1 hi) (stkinv_init toks) (dinv_init toks) (.inr rfl)
  simpa [TA] using this

end ParRun
