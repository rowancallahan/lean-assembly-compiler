/- Nano/V2Self/Proof/Parser/ParRunObl: pure Layer-2 reachability facts for `Obl` (box B): `assignTy`, `selfP`, `prev`, `names`. -/
import Nano.V2Self.Proof.Parser.ParRunNames
import Nano.V2Self.Proof.Parser.ParRunDef
import Nano.V2Self.Proof.Lex.ParTokWF
namespace ParRun
open ParSpec

theorem mkNode_eqO {st st' : St} {t a b : Nat} {s : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') : ∃ v ar, st' = { st with vals := v, arena := ar } := by
  unfold mkNode at h; split at h <;> cases h; exact ⟨_, _, rfl⟩

theorem locOf_eqO {st st' : St} {bd : Bd} (h : locOf st bd = some st') : ∃ v ar, st' = { st with vals := v, arena := ar } := by
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
       | (obtain ⟨v, ar, rfl⟩ := mkNode_eqO h2; simp_all; done)
       | (obtain ⟨v, ar, rfl⟩ := locOf_eqO h2; simp_all; done)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨v, ar, rfl⟩ := mkNode_eqO h2'
          first | (obtain ⟨v, ar, rfl⟩ := mkNode_eqO h1) | cases h1
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
       | (obtain ⟨v, ar, rfl⟩ := mkNode_eqO h2; simp_all [TA]; done)
       | (obtain ⟨v, ar, rfl⟩ := locOf_eqO h2; simp_all [TA]; done)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨v, ar, rfl⟩ := mkNode_eqO h2'
          first | (obtain ⟨v, ar, rfl⟩ := mkNode_eqO h1) | cases h1
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

/-! ## names -/
theorem idsOK_of_tokL {ts : List UInt64} {toks : List Tok} (h : ParSpec.TokL ts toks) : IdsOK toks := by
  induction h with
  | nil => intro x hx; simp at hx
  | kw _ _ _ _ _ ih => intro x hx; simp at hx; exact ih x hx
  | num _ _ _ _ ih => intro x hx; simp at hx; exact ih x hx
  | id nm hn _ ih =>
    intro x hx; simp at hx
    rcases hx with rfl | hx
    · simpa using hn
    · exact ih x hx

theorem reach_names {ts : List UInt64} {toks : List Tok} (hT : ParSpec.TokL ts toks) {fs : List Frame} {st : St}
    (h : Star ([.defs], init toks) (fs, st)) : ∀ d ∈ st.defs, d.name ≠ [] :=
  (h.ninv (ninv_init (idsOK_of_tokL hT))).2.1

/-! ## selfP: `.selfArgs` is pushed only in an arm, alone, and is executed at once; arms need a non-empty parameter list -/
def SelfInv (c : List Frame × St) : Prop :=
  (c.2.arm = true → c.2.cur.params ≠ []) ∧ (Frame.zeroDone ∈ c.1 → c.2.cur.params ≠ []) ∧
  (∀ g ∈ c.1.tail, g ≠ .selfArgs) ∧ (c.1.head? = some .selfArgs → c.2.arm = true)

theorem prefix_ne {l l' : List Sh} (h : l <+: l') (hl : l ≠ []) : l' ≠ [] := by
  rintro rfl; exact hl (List.prefix_nil.mp h)

theorem stepS_sinv {c d : List Frame × St} (hs : stepS c = some d) (hd : DInv c) (hi : SelfInv c) : SelfInv d := by
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f rest =>
  obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
  obtain ⟨_, _, hS, hZ, hP, hA, hD⟩ := stepF_obl h1
  obtain ⟨i1, i2, i3, i4⟩ := hi
  simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at i1 i2 i3 i4
  have hrest : f = .defs → rest = [] := fun e => by
    have := hd (by simp [e]); simp at this; exact this.2
  have keep : st.cur.params ≠ [] → (f ≠ .defs ∨ k = []) → st'.cur.params ≠ [] := fun h e => prefix_ne (hP e) h
  refine ⟨fun ha => ?_, fun hz => ?_, fun g hg => ?_, fun hh => ?_⟩
  · rcases hA ha with ha0 | rfl
    · by_cases e : f = .defs ∧ k ≠ []
      · rw [hD e.1 e.2] at ha; cases ha
      · exact keep (i1 ha0) (by by_cases hf : f = .defs; exact .inr (Classical.byContradiction fun hk => e ⟨hf, hk⟩); exact .inl hf)
    · exact keep (i2 (by simp)) (.inl (by simp))
  · rcases List.mem_append.mp hz with hz | hz
    · exact hZ hz
    · by_cases e : f = .defs
      · rw [hrest e] at hz; cases hz
      · exact keep (i2 (List.mem_cons_of_mem _ hz)) (.inl e)
  · simp only at hg ⊢
    rintro rfl
    cases k with
    | nil => exact i3 _ (List.mem_of_mem_tail (by simpa using hg)) rfl
    | cons g0 k' =>
      rcases List.mem_append.mp (by simpa using hg) with hg | hg
      · obtain ⟨e, _⟩ := hS (List.mem_cons_of_mem _ hg); cases e; exact absurd ‹Frame.selfArgs ∈ []› (by simp)
      · exact i3 _ hg rfl
  · simp only at hh ⊢
    cases k with
    | nil => exact absurd rfl (i3 _ (List.mem_of_head? hh))
    | cons g0 k' =>
      simp at hh; subst hh; exact (hS (by simp)).2.2

theorem reach_selfP {toks : List Tok} {fs : List Frame} {st : St}
    (h : Star ([.defs], init toks) (.selfArgs :: fs, st)) : st.cur.params ≠ [] := by
  have := h.lift (P := SelfInv) (fun hs _ hd hi => stepS_sinv hs hd hi) (stkinv_init toks) (dinv_init toks)
    ⟨fun e => by simp [init] at e, fun e => by simp at e, fun g hg => by simp at hg, fun e => by simp at e⟩
  exact this.1 (this.2.2.2 rfl)

/-! ## prev: above `.afterColon` only type frames run, and each leaves a keyword token just before the cursor -/
def PInv (c : List Frame × St) : Prop :=
  (∃ pre, c.2.all = pre ++ c.2.toks) ∧
  (Frame.afterColon ∈ c.1 → (∀ g ∈ c.1, g = .afterColon ∨ isTyF g = true) ∧
    (c.1.head? ≠ some .tyAtom → ∃ t, prevTok c.2 = some t ∧ ∀ v, t ≠ .num v))

theorem prevTok_eq {st : St} {pre : List Tok} (h : st.all = pre ++ st.toks) : prevTok st = pre.getLast? := by
  simp only [prevTok, h, List.length_append, Nat.add_sub_cancel, List.take_left']

theorem prevTok_cons1 {st st' : St} {pre r : List Tok} {t : Tok} (h : st.all = pre ++ st.toks) (ht : st.toks = t :: r)
    (ha : st'.all = st.all) (hr : st'.toks = r) : prevTok st' = some t := by
  rw [prevTok_eq (pre := pre ++ [t]) (by rw [ha, h, ht, hr]; simp)]; simp

theorem prevTok_cons2 {st st' : St} {pre r : List Tok} {t u : Tok} (h : st.all = pre ++ st.toks) (ht : st.toks = t :: u :: r)
    (ha : st'.all = st.all) (hr : st'.toks = r) : prevTok st' = some u := by
  rw [prevTok_eq (pre := pre ++ [t, u]) (by rw [ha, h, ht, hr]; simp)]; simp

theorem stepS_pinv {c d : List Frame × St} (hs : stepS c = some d) (hk : StkInv c) (hd : DInv c) (hi : PInv c) : PInv d := by
  obtain ⟨⟨pre, hpre⟩, hac⟩ := hi
  obtain ⟨ha', ⟨q, hq⟩⟩ := (Star.step hs (.refl _)).toks
  refine ⟨⟨pre ++ q, by rw [ha', hpre, ← hq, List.append_assoc]⟩, ?_⟩
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f rest =>
  obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
  simp only at hpre hac ⊢
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨rfl, rfl⟩ := (stepF_obl h1).2.1 hm
    have : rest = [] := by have := hd (by simp); simpa using this
    subst this
    refine ⟨fun g hg => ?_, fun hh => absurd rfl hh⟩
    simp at hg; rcases hg with rfl | rfl <;> simp [isTyF]
  · obtain ⟨hall, hpv⟩ := hac (List.mem_cons_of_mem _ hm)
    have hrest : ∀ g ∈ rest, g = .afterColon ∨ isTyF g = true := fun g hg => hall g (List.mem_cons_of_mem _ hg)
    rcases hall f (by simp) with rfl | hf
    · rcases stackOK_cons hk.1 with ⟨rfl, _⟩ | ⟨_, hD, _⟩
      · cases hm
      · simp [isD] at hD
    cases f <;> simp [isTyF] at hf <;> simp only [stepF] at h1 <;> (repeat' split at h1) <;> (try cases h1) <;>
      (refine ⟨fun g hg => ?_, fun hh => ?_⟩
       · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
         rcases hg with hg | hg
         · first | (subst hg; simp [isTyF]) | (rcases hg with rfl | rfl | rfl <;> simp [isTyF]) | (rcases hg with rfl | rfl <;> simp [isTyF])
         · exact hrest g hg
       · first
         | exact absurd rfl hh
         | exact ⟨_, prevTok_cons1 hpre (by assumption) rfl rfl, by simp⟩
         | exact ⟨_, prevTok_cons2 hpre (by assumption) rfl rfl, by simp⟩
         | exact hpv (by simp))

theorem reach_prev {toks : List Tok} {fs : List Frame} {st : St}
    (h : Star ([.defs], init toks) (.afterColon :: fs, st)) : ∃ t, prevTok st = some t ∧ ∀ v, t ≠ .num v := by
  have := h.lift (P := PInv) (fun hs hk hd hi => stepS_pinv hs hk hd hi) (stkinv_init toks) (dinv_init toks)
    ⟨⟨[], by simp [init]⟩, fun e => by simp at e⟩
  exact (this.2 (by simp)).2 (by simp)

end ParRun
