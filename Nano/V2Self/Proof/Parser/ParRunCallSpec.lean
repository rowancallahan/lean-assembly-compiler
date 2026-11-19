/- Nano/V2Self/Proof/Parser/ParRunCallSpec: Layer 2 → ParSpec for CALL arguments (box G).
`tyMatch_of`: Par1's argument check (`argOK`: shape code = parameter code, or a numeral / len' for a Nat parameter) together with the
input rule (argument is the input local ⇔ parameter is the input: the deferred validation v210) is ParSpec's `tyMatch`.
`toNdL_dropInp`: the flattener's "skip input locals" is ParSpec's `dropInp`. -/
import Nano.V2Self.Proof.Parser.ParRunArgs
namespace ParRun
open ParSpec

theorem tyMatch_of {p : Ps} {v : RN} {ty : Ty} (hv : ValOK v ty) (hn : p ≠ .sh .nt) (hi : p = .inp ↔ v.isInp = true)
    (hok : v.sh = some (psCode p) ∨ (psCode p = .nt ∧ (v.tag = 1 ∨ (v.tag = 9 ∧ v.a = 1)))) : tyMatch p ty = true := by
  obtain ⟨hty, hpe, h9⟩ := hv
  have hsh : v.sh = some (psCode p) ∨ (psCode p = .nt ∧ v.tag = 1) := by
    rcases hok with h | ⟨h1, h2 | ⟨h2, h3⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl (by rw [h1]; exact h9 h2 h3)
  cases ty with
  | bot => simp [TyRel] at hty; rw [hpe] at hty; cases hty
  | inp =>
    obtain ⟨hin, hls⟩ := hty
    have := hi.mpr hin; subst this; rfl
  | lit =>
    obtain ⟨huw, hni⟩ := hty
    cases p with
    | inp => have := hi.mp rfl; rw [hni] at this; cases this
    | fuel => rfl
    | sh s =>
      rcases hsh with h | ⟨h1, _⟩
      · rw [huw] at h; simp [psCode] at h; subst h; rfl
      · exact absurd (by simpa [psCode] using h1) hn
  | s t =>
    obtain ⟨hs, hni, ht1⟩ := hty
    cases p with
    | inp =>
      obtain ⟨l, r, rfl⟩ := hni (hi.mp rfl)
      rcases hsh with h | ⟨h1, _⟩ <;> simp_all [psCode]
    | fuel =>
      rcases hsh with h | ⟨_, h2⟩
      · rw [hs] at h; simp [psCode] at h; subst h; rfl
      · exact absurd h2 ht1
    | sh s =>
      rcases hsh with h | ⟨h1, _⟩
      · rw [hs] at h; simp [psCode] at h; subst h; simp [tyMatch]
      · exact absurd (by simpa [psCode] using h1) hn

/-- the input rule, position by position: the parameter is the input iff the argument is the input local -/
inductive InpPair : List Ps → List RN → Prop
  | nil : InpPair [] []
  | cons {p ps v vs} : (p = .inp ↔ v.isInp = true) → InpPair ps vs → InpPair (p :: ps) (v :: vs)

theorem toNdL_cons (n : RN) (r : List RN) : RN.toNdL (n :: r) = if n.isInp then RN.toNdL r else RN.toNd n :: RN.toNdL r := by
  rw [RN.toNdL]

theorem toNdL_dropInp : ∀ {ps : List Ps} {vs : List RN}, InpPair ps vs → RN.toNdL vs = dropInp ps (vs.map RN.toNd) := by
  intro ps vs h
  induction h with
  | nil => simp [RN.toNdL, dropInp]
  | @cons p ps v vs hp _ ih =>
    rw [toNdL_cons, ih]
    by_cases hv : v.isInp = true
    · have := hp.mpr hv; subst this
      simp [hv, dropInp]
    · have hne : p ≠ .inp := fun e => hv (hp.mp e)
      simp only [hv, Bool.false_eq_true, if_false]
      cases p with
      | inp => exact absurd rfl hne
      | fuel => simp [dropInp]
      | sh s => simp [dropInp]

theorem InpPair.get {ps : List Ps} {vs : List RN} (h : InpPair ps vs) :
    ∀ (i : Nat) (h1 : i < ps.length) (h2 : i < vs.length), (ps[i] = .inp ↔ vs[i].isInp = true) := by
  induction h with
  | nil => intro i h1; simp at h1
  | cons hp _ ih =>
    intro i h1 h2
    cases i with
    | zero => exact hp
    | succ i => exact ih i (by simpa using h1) (by simpa using h2)

theorem argsMatch_of : ∀ (ps : List Ps) (vs : List (RN × Ty)), ps.length = vs.length →
    (∀ (i : Nat) (h1 : i < ps.length) (h2 : i < vs.length), tyMatch ps[i] vs[i].2 = true) → ArgsMatch ps vs
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | p :: ps, v :: vs, hl, h =>
    .cons (h 0 (by simp) (by simp)) (argsMatch_of ps vs (by simpa using hl) fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))

/-- operand `i` (0 = top) of `as.reverse ++ base` is argument `k − 1 − i` -/
theorem operand_idx {α : Type} (l base : List α) (idx : Nat) (h : idx < l.length) :
    (l.reverse ++ base)[l.length - 1 - idx]? = some l[idx] := by
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse (by omega)]
  rw [show l.length - 1 - (l.length - 1 - idx) = idx by omega]
  exact List.getElem?_eq_getElem h

/-! ## prims -/
theorem primPar_ne_nt (p i : Nat) : primPar p i ≠ .nt := by
  unfold primPar; split <;> (try split) <;> simp

theorem toNd_prim1 (p b : Nat) (sh : Option Sh) (pe : Bool) (kids : List RN) (hp : p < 4) :
    (RN.mk 9 p b sh pe kids).toNd = .prim p (RN.toNdL kids.tail) := by
  rw [RN.toNd.eq_def]
  simp only [hp, and_self, if_true]
  cases kids <;> simp [RN.toNdL]

theorem toNd_prim2 (p b : Nat) (sh : Option Sh) (pe : Bool) (kids : List RN) (hp : ¬ p < 4) :
    (RN.mk 9 p b sh pe kids).toNd = .prim p (RN.toNdL kids) := by
  rw [RN.toNd.eq_def]
  simp only [hp, and_false, if_false]
  simp

theorem prim_toNd {p : Nat} {sh : Option Sh} {ps : List Ps} {kids : List RN} (hi : InpPair ps kids)
    (h4 : p < 4 → ps.head? = some .inp) :
    (RN.mk 9 p 0 sh false kids).toNd = .prim p (dropInp ps (kids.map RN.toNd)) := by
  rw [← toNdL_dropInp hi]
  by_cases hp : p < 4
  · rw [toNd_prim1 _ _ _ _ _ hp]
    cases hi with
    | nil => rfl
    | @cons q qs v vs hq _ =>
      have hq' : q = .inp := by simpa using h4 hp
      have hv : v.isInp = true := hq.mp hq'
      simp [toNdL_cons, hv]
  · rw [toNd_prim2 _ _ _ _ _ hp]

/-! ## the input rule from the deferred validation (`nodeOK`, v209) — prims -/
theorem inpPair_of : ∀ (ps : List Ps) (vs : List RN), ps.length = vs.length →
    (∀ (i : Nat) (h1 : i < ps.length) (h2 : i < vs.length), (ps[i] = .inp ↔ vs[i].isInp = true)) → InpPair ps vs
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | p :: ps, v :: vs, hl, h =>
    .cons (h 0 (by simp) (by simp)) (inpPair_of ps vs (by simpa using hl) fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))

theorem filter_inp0 {ks : List RN} (h : (ks.filter RN.isInp).length = 0) : ∀ k ∈ ks, k.isInp = false := by
  intro k hk
  cases hi : k.isInp with
  | false => rfl
  | true =>
    have : k ∈ ks.filter RN.isInp := List.mem_filter.mpr ⟨hk, hi⟩
    rw [List.length_eq_zero_iff.mp h] at this; cases this

/-- a validated PRIM node satisfies the input rule of its signature: rd / len / len' have the input local as first operand and
nowhere else, the other prims have no input operand -/
theorem prim_inpPair {t : Nat} (h1 : 38 < t) (h2 : t < 48) {ps : List Ps} {rs : Sh} (hsig : primSig t = some (t - 38, ps, rs))
    {ds : List DefR} {b : Nat} {sh : Option Sh} {pe : Bool} {kids : List RN} (hl : kids.length = ps.length)
    (hok : nodeOK ds (RN.mk 9 (t - 38) b sh pe kids) = true) : InpPair ps kids := by
  obtain ⟨ps', hsig', _, _, hinpi, _⟩ := prim_sig h1 h2
  rw [hsig] at hsig'; simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hsig'
  obtain ⟨rfl, _⟩ := hsig'
  refine inpPair_of _ _ hl.symm fun i i1 i2 => ?_
  have hget := hinpi i
  rw [List.getElem?_eq_getElem i1] at hget
  simp only [Option.some.injEq] at hget
  rw [hget]
  simp only [nodeOK, RN.kids, RN.tag, RN.a, RN.sh] at hok
  by_cases h4 : t - 38 < 4
  · by_cases hm : (kids.filter RN.isInp).length = 0
    · simp [hm, h4] at hok
    · simp only [hm, if_false, h4, if_true, show ¬ (9 : Nat) = 8 from by decide, show ¬ (9 : Nat) = 6 from by decide, show ¬ (9 : Nat) = 11 from by decide,
        Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hm1, hp0⟩ := hok
      cases kids with
      | nil => simp at hm
      | cons k0 r =>
        simp only at hp0
        have hr : (r.filter RN.isInp).length = 0 := by
          simp only [List.filter_cons, hp0, if_true, List.length_cons] at hm1; omega
        cases i with
        | zero => simp [h4, hp0]
        | succ i =>
          have hi : i < r.length := by simpa using i2
          have := filter_inp0 hr r[i] (List.getElem_mem hi)
          simp [this]
  · by_cases hm : (kids.filter RN.isInp).length = 0
    · have := filter_inp0 hm kids[i] (List.getElem_mem i2)
      simp [this, h4]
    · simp [hm, h4] at hok

/-! ## the input rule from the deferred validation (`inpMatch`, v210) — def CALLs -/
theorem inpMatch_get : ∀ (ws : List Sh) (g : Bool) (ks : List RN), inpMatch ws g ks = true →
    ∀ (i : Nat) (hi : i < ks.length), (ks[i].isInp = true ↔ (g = false ∧ FirstLs ws i))
  | _, _, [], _, i, hi => absurd hi (by simp)
  | [], _, _ :: _, h, _, _ => by simp [inpMatch] at h
  | w :: ws, g, k :: ks, h, i, hi => by
    simp only [inpMatch, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, ← h1, FirstLs, List.getElem?_cons_zero, Option.some.injEq]
      cases g <;> cases hw : (w == Sh.ls) <;> simp_all
    | succ i =>
      have ih := inpMatch_get ws (g || w == .ls) ks h2 i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      rw [ih]
      simp only [FirstLs, List.getElem?_cons_succ, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      constructor
      · rintro ⟨⟨hg, hw⟩, hl, hf⟩
        refine ⟨hg, hl, fun j hj => ?_⟩
        cases j with
        | zero => simpa using hw
        | succ j => simpa using hf j (by omega)
      · rintro ⟨hg, hl, hf⟩
        refine ⟨⟨hg, by simpa using hf 0 (by omega)⟩, hl, fun j hj => ?_⟩
        simpa using hf (j + 1) (by omega)

/-- a validated CALL node satisfies the input rule of its callee, when the callee's row marks its input as the first List code -/
theorem def_inpPair {ps : List Ps} {ws : List Sh} {kids : List RN} (hinv : ∀ (i : Nat) (h : i < ps.length), (ps[i] = .inp ↔ FirstLs ws i))
    (hl : kids.length = ps.length) (hok : inpMatch ws false kids = true) : InpPair ps kids :=
  inpPair_of _ _ hl.symm fun i i1 i2 => by
    rw [hinv i i1, inpMatch_get ws false kids hok i i2]; simp

end ParRun
