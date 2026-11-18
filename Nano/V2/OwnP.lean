import Nano.V2.Heap
/- nano v2: facts about the ownership checker `Ex.lv` (Nano/V2/Own.lean) used by the buffer proof
(Nano/V2/CompB.lean): one inversion lemma per construct, and `lv_step` (a checked block only kills live BUFFER
variables, `Step`; flag lists keep their length). -/
namespace Nano.V2B

theorem dead_iff (d : List Nat) (i : Nat) : dead d i = true ↔ fl d i = 2 := by simp [dead, fl]
theorem live_iff (d : List Nat) (i : Nat) : live d i = true ↔ fl d i = 0 := by simp [live, fl]

theorem fl_set (d : List Nat) (j v k : Nat) : fl (d.set j v) k = if k = j ∧ j < d.length then v else fl d k := by
  unfold fl
  by_cases hk : k = j
  · subst hk
    by_cases hl : k < d.length
    · simp [List.getD_eq_getElem?_getD, hl]
    · simp [List.getD_eq_getElem?_getD, hl, List.getElem?_eq_none (show d.length ≤ k by omega)]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set, hk, Ne.symm hk]

theorem fl_cons_zero (a : Nat) (d : List Nat) : fl (a :: d) 0 = a := rfl
theorem fl_cons_succ (a : Nat) (d : List Nat) (k : Nat) : fl (a :: d) (k + 1) = fl d k := rfl
theorem fl_tail (d : List Nat) (k : Nat) : fl d.tail k = fl d (k + 1) := by
  cases d <;> rfl
theorem fl_drop2 (d : List Nat) (k : Nat) : fl (d.drop 2) k = fl d (k + 2) := by
  unfold fl; simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]; congr 2; omega

theorem fl_orL : ∀ {a b : List Nat}, a.length = b.length → ∀ k, fl (orL a b) k = max (fl a k) (fl b k)
  | [], [], _, _ => rfl
  | x :: a, y :: b, h, k => by
    cases k with
    | zero => rfl
    | succ k => exact fl_orL (a := a) (b := b) (by simpa using h) k

theorem use_spec {tys : List Ty} {d d' : List Nat} {i : Nat} (h : use tys d i = some d') :
    Step tys d d' ∧ d'.length = d.length ∧ ((tys.getD i .w).hasBuf = true → fl d i = 0 ∧ fl d' i = 2 ∨ i ≥ d.length) ∧
      ((tys.getD i .w).hasBuf = false → d' = d) := by
  unfold use at h
  split at h
  · rename_i hb
    split at h
    · rename_i hl
      simp only [Option.some.injEq, kill, hb, if_true] at h; subst h
      rw [live_iff] at hl
      refine ⟨fun k => ?_, by simp, fun _ => ?_, fun h' => absurd (hb.symm.trans h') (by decide)⟩
      · rw [fl_set]; split
        · next hk => obtain ⟨rfl, _⟩ := hk; exact .inr ⟨hl, rfl, hb⟩
        · exact .inl rfl
      · by_cases hi : i < d.length
        · exact .inl ⟨hl, by rw [fl_set]; simp [hi]⟩
        · exact .inr (by omega)
    · simp at h
  · rename_i hb
    simp only [Option.some.injEq] at h; subst h
    exact ⟨Step.refl _ _, rfl, fun h' => absurd h' hb, fun _ => rfl⟩

/-! ## inversion, one lemma per construct -/

theorem lv_var {tys : List Ty} {d d' : List Nat} {i : Nat} : (Ex.var i).lv tys d = some d' ↔ use tys d i = some d' := by
  simp [Ex.lv]

theorem lv_two {tys : List Ty} {d d' : List Nat} {a b : Ex} (h : (match a.lv tys d with
    | some d1 => b.lv tys d1 | none => none) = some d') : ∃ d1, a.lv tys d = some d1 ∧ b.lv tys d1 = some d' := by
  revert h; cases a.lv tys d <;> simp

theorem lv_three {tys : List Ty} {d d' : List Nat} {a b x : Ex} (h : (match a.lv tys d with
    | some d1 => match b.lv tys d1 with
      | some d2 => x.lv tys d2
      | none => none
    | none => none) = some d') : ∃ d1 d2, a.lv tys d = some d1 ∧ b.lv tys d1 = some d2 ∧ x.lv tys d2 = some d' := by
  revert h; cases h1 : a.lv tys d <;> simp; cases h2 : b.lv tys _ <;> simp_all

theorem lv_letg {tys : List Ty} {d d' : List Nat} {v b : Ex} (h : (match tyOf tys v, v.lv tys d with
    | some τ, some d1 => (b.lv (τ :: tys) (0 :: d1)).map List.tail
    | _, _ => none) = some d') :
    ∃ τ d1 d'', tyOf tys v = some τ ∧ v.lv tys d = some d1 ∧ b.lv (τ :: tys) (0 :: d1) = some d'' ∧ d' = d''.tail := by
  revert h; cases h1 : tyOf tys v <;> cases h2 : v.lv tys d <;> simp
  intro d'' h3 h4; exact ⟨d'', h3, h4.symm⟩

theorem lvT_letg {tys : List Ty} {d d' : List Nat} {v : Ex} {b : Tl} (h : (match tyOf tys v, v.lv tys d with
    | some τ, some d1 => (b.lvT (τ :: tys) (0 :: d1)).map List.tail
    | _, _ => none) = some d') :
    ∃ τ d1 d'', tyOf tys v = some τ ∧ v.lv tys d = some d1 ∧ b.lvT (τ :: tys) (0 :: d1) = some d'' ∧ d' = d''.tail := by
  revert h; cases h1 : tyOf tys v <;> cases h2 : v.lv tys d <;> simp
  intro d'' h3 h4; exact ⟨d'', h3, h4.symm⟩

theorem lv_bin {tys : List Ty} {d d' : List Nat} {o : Op} {a b : Ex} (h : (Ex.bin o a b).lv tys d = some d') :
    ∃ d1, a.lv tys d = some d1 ∧ b.lv tys d1 = some d' := lv_two (by simpa [Ex.lv] using h)

theorem lv_pair {tys : List Ty} {d d' : List Nat} {a b : Ex} (h : (Ex.pair a b).lv tys d = some d') :
    ∃ d1, a.lv tys d = some d1 ∧ b.lv tys d1 = some d' := lv_two (by simpa [Ex.lv] using h)

theorem lv_fst {tys : List Ty} {d d' : List Nat} {a : Ex} (h : (Ex.fst a).lv tys d = some d') : a.lv tys d = some d' := by
  simpa [Ex.lv] using h
theorem lv_snd {tys : List Ty} {d d' : List Nat} {a : Ex} (h : (Ex.snd a).lv tys d = some d') : a.lv tys d = some d' := by
  simpa [Ex.lv] using h
theorem lv_iget {tys : List Ty} {d d' : List Nat} {a : Ex} (h : (Ex.iget a).lv tys d = some d') : a.lv tys d = some d' := by
  simpa [Ex.lv] using h

theorem lv_size {tys : List Ty} {d d' : List Nat} {a : Ex} (h : (Ex.size a).lv tys d = some d') :
    (∃ i, a = .var i ∧ fl d i ≠ 2 ∧ d' = d) ∨ a.lv tys d = some d' := by
  cases a <;> simp only [Ex.lv] at h <;> try exact .inr h
  rename_i i
  split at h
  · simp at h
  · rename_i hd; simp only [Option.some.injEq] at h; exact .inl ⟨i, rfl, fun h2 => hd ((dead_iff _ _).2 h2), h.symm⟩

theorem lv_get {tys : List Ty} {d d' : List Nat} {a j : Ex} (h : (Ex.get a j).lv tys d = some d') :
    (∃ i, a = .var i ∧ fl d i ≠ 2 ∧ j.lv tys d = some d' ∧ fl d' i ≠ 2) ∨
      ∃ d1, a.lv tys d = some d1 ∧ j.lv tys d1 = some d' := by
  cases a
  case var i =>
    simp only [Ex.lv] at h
    split at h
    · simp at h
    · rename_i hd
      revert h; cases hj : j.lv tys d with
      | none => simp
      | some d1 =>
        simp only
        split
        · simp
        · rename_i hd1; intro h; simp only [Option.some.injEq] at h; subst h
          exact .inl ⟨i, rfl, fun h2 => hd ((dead_iff _ _).2 h2), rfl, fun h2 => hd1 ((dead_iff _ _).2 h2)⟩
  all_goals exact .inr (lv_two h)

theorem lv_set {tys : List Ty} {d d' : List Nat} {a j x : Ex} (h : (Ex.set a j x).lv tys d = some d') :
    (∃ i d1 d2, a = .var i ∧ fl d i = 0 ∧ j.lv tys d = some d1 ∧ x.lv tys d1 = some d2 ∧ use tys d2 i = some d') ∨
      ∃ d1 d2, a.lv tys d = some d1 ∧ j.lv tys d1 = some d2 ∧ x.lv tys d2 = some d' := by
  cases a
  case var i =>
    simp only [Ex.lv] at h
    split at h
    · rename_i hl
      revert h; cases hj : j.lv tys d with
      | none => simp
      | some d1 =>
        cases hx : x.lv tys d1 with
        | none => simp [hx]
        | some d2 => intro h; simp only [hx] at h; exact .inl ⟨i, d1, d2, rfl, (live_iff d i).1 hl, rfl, hx, h⟩
    · simp at h
  all_goals exact .inr (lv_three h)

theorem lv_push {tys : List Ty} {d d' : List Nat} {a x : Ex} (h : (Ex.push a x).lv tys d = some d') :
    (∃ i d1, a = .var i ∧ fl d i = 0 ∧ x.lv tys d = some d1 ∧ use tys d1 i = some d') ∨
      ∃ d1, a.lv tys d = some d1 ∧ x.lv tys d1 = some d' := by
  cases a
  case var i =>
    simp only [Ex.lv] at h
    split at h
    · rename_i hl
      revert h; cases hx : x.lv tys d with
      | none => simp
      | some d1 => intro h; exact .inl ⟨i, d1, rfl, (live_iff d i).1 hl, rfl, h⟩
    · simp at h
  all_goals exact .inr (lv_two h)

theorem lv_ite {tys : List Ty} {d d' : List Nat} {k : Cmp} {a b t e : Ex} (h : (Ex.ite k a b t e).lv tys d = some d') :
    ∃ d1 d2 x y, a.lv tys d = some d1 ∧ b.lv tys d1 = some d2 ∧ t.lv tys d2 = some x ∧ e.lv tys d2 = some y ∧
      d' = orL x y := by
  simp only [Ex.lv] at h
  cases h1 : a.lv tys d with
  | none => simp [h1] at h
  | some d1 =>
    cases h2 : b.lv tys d1 with
    | none => simp [h1, h2] at h
    | some d2 =>
      cases h3 : t.lv tys d2 with
      | none => simp [h1, h2, h3] at h
      | some x =>
        cases h4 : e.lv tys d2 with
        | none => simp [h1, h2, h3, h4] at h
        | some y => simp [h1, h2, h3, h4] at h; exact ⟨d1, d2, x, y, rfl, h2, h3, h4, h.symm⟩

/-- `let`: a read-only alias of a buffer variable, or an ordinary `let` -/
theorem lv_let {tys : List Ty} {d d' : List Nat} {v b : Ex} (h : (Ex.let_ v b).lv tys d = some d') :
    (∃ j τ d'', v = .var j ∧ tys[j]? = some τ ∧ τ.hasBuf = true ∧ fl d j ≠ 2 ∧
      b.lv (τ :: tys) (1 :: d.set j (max (fl d j) 1)) = some d'' ∧ d' = d''.tail.set j (fl d j)) ∨
    ∃ τ d1 d'', tyOf tys v = some τ ∧ v.lv tys d = some d1 ∧ b.lv (τ :: tys) (0 :: d1) = some d'' ∧ d' = d''.tail := by
  cases v
  case var j =>
    simp only [Ex.lv] at h
    revert h
    cases hj : tys[j]? with
    | none => simp
    | some τ =>
      simp only
      split
      · rename_i hro
        split
        · simp
        · rename_i hd
          cases hb : b.lv (τ :: tys) (1 :: d.set j (max (d.getD j 0) 1)) with
          | none => simp
          | some d'' =>
            simp only [Option.map_some, Option.some.injEq]; intro h
            simp only [Bool.and_eq_true] at hro
            exact .inl ⟨j, τ, d'', rfl, hj, hro.1, fun h2 => hd ((dead_iff _ _).2 h2), hb, h.symm⟩
      · cases hu : use tys d j with
        | none => simp
        | some d1 =>
          simp only
          cases hb : b.lv (τ :: tys) (0 :: d1) with
          | none => simp
          | some d'' =>
            simp only [Option.map_some, Option.some.injEq]; intro h
            exact .inr ⟨τ, d1, d'', by simpa [tyOf] using hj, by simpa [Ex.lv] using hu, hb, h.symm⟩
  all_goals exact .inr (lv_letg h)

theorem lv_split {tys : List Ty} {d d' : List Nat} {e b : Ex} (h : (Ex.split e b).lv tys d = some d') :
    ∃ τ σ d1 d'', tyOf tys e = some (.prod τ σ) ∧ e.lv tys d = some d1 ∧
      b.lv (σ :: τ :: tys) (0 :: 0 :: d1) = some d'' ∧ d' = d''.drop 2 := by
  simp only [Ex.lv] at h
  revert h
  split
  · rename_i τ σ d1 h1 h2
    cases hb : Ex.lv (σ :: τ :: tys) (0 :: 0 :: d1) b with
    | none => simp
    | some d'' => simp only [Option.map_some, Option.some.injEq]; intro h; exact ⟨τ, σ, d1, d'', h1, h2, hb, h.symm⟩
  · simp

theorem lv_loop {tys : List Ty} {d d' : List Nat} {f i z : Ex} {t : Tl} (h : (Ex.loop f i z t).lv tys d = some d') :
    ∃ σ d1 dz dt, tyOf tys i = some σ ∧ f.lv tys d = some d1 ∧ i.lv tys d1 = some d' ∧
      z.lv (σ :: tys) (0 :: killAll tys d') = some dz ∧ t.lvT (σ :: tys) (0 :: killAll tys d') = some dt := by
  simp only [Ex.lv] at h
  cases hi : tyOf tys i with
  | none => simp [hi] at h
  | some σ =>
    cases h1 : f.lv tys d with
    | none => simp [hi, h1] at h
    | some d1 =>
      cases h2 : i.lv tys d1 with
      | none => simp [hi, h1, h2] at h
      | some d2 =>
        simp only [hi, h1, h2] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
          obtain ⟨⟨dz, hz⟩, ⟨dt, ht⟩⟩ := hc
          simp only [Option.some.injEq] at h; subst h
          exact ⟨σ, d1, dz, dt, rfl, rfl, h2, hz, ht⟩
        · simp at h

theorem lvT_ret {tys : List Ty} {d d' : List Nat} {e : Ex} (h : (Tl.ret e).lvT tys d = some d') : e.lv tys d = some d' := by
  simpa [Tl.lvT] using h
theorem lvT_next {tys : List Ty} {d d' : List Nat} {e : Ex} (h : (Tl.next e).lvT tys d = some d') : e.lv tys d = some d' := by
  simpa [Tl.lvT] using h

theorem lvT_ite {tys : List Ty} {d d' : List Nat} {k : Cmp} {a b : Ex} {t e : Tl}
    (h : (Tl.ite k a b t e).lvT tys d = some d') :
    ∃ d1 d2 x y, a.lv tys d = some d1 ∧ b.lv tys d1 = some d2 ∧ t.lvT tys d2 = some x ∧ e.lvT tys d2 = some y ∧
      d' = orL x y := by
  simp only [Tl.lvT] at h
  cases h1 : a.lv tys d with
  | none => simp [h1] at h
  | some d1 =>
    cases h2 : b.lv tys d1 with
    | none => simp [h1, h2] at h
    | some d2 =>
      cases h3 : t.lvT tys d2 with
      | none => simp [h1, h2, h3] at h
      | some x =>
        cases h4 : e.lvT tys d2 with
        | none => simp [h1, h2, h3, h4] at h
        | some y => simp [h1, h2, h3, h4] at h; exact ⟨d1, d2, x, y, rfl, h2, h3, h4, h.symm⟩

theorem lvT_let {tys : List Ty} {d d' : List Nat} {v : Ex} {b : Tl} (h : (Tl.let_ v b).lvT tys d = some d') :
    (∃ j τ d'', v = .var j ∧ tys[j]? = some τ ∧ τ.hasBuf = true ∧ fl d j ≠ 2 ∧
      b.lvT (τ :: tys) (1 :: d.set j (max (fl d j) 1)) = some d'' ∧ d' = d''.tail.set j (fl d j)) ∨
    ∃ τ d1 d'', tyOf tys v = some τ ∧ v.lv tys d = some d1 ∧ b.lvT (τ :: tys) (0 :: d1) = some d'' ∧ d' = d''.tail := by
  cases v
  case var j =>
    simp only [Tl.lvT] at h
    revert h
    cases hj : tys[j]? with
    | none => simp
    | some τ =>
      simp only
      split
      · rename_i hro
        split
        · simp
        · rename_i hd
          cases hb : b.lvT (τ :: tys) (1 :: d.set j (max (d.getD j 0) 1)) with
          | none => simp
          | some d'' =>
            simp only [Option.map_some, Option.some.injEq]; intro h
            simp only [Bool.and_eq_true] at hro
            exact .inl ⟨j, τ, d'', rfl, hj, hro.1, fun h2 => hd ((dead_iff _ _).2 h2), hb, h.symm⟩
      · cases hu : use tys d j with
        | none => simp
        | some d1 =>
          simp only
          cases hb : b.lvT (τ :: tys) (0 :: d1) with
          | none => simp
          | some d'' =>
            simp only [Option.map_some, Option.some.injEq]; intro h
            exact .inr ⟨τ, d1, d'', by simpa [tyOf] using hj, by simpa [Ex.lv] using hu, hb, h.symm⟩
  all_goals exact .inr (lvT_letg h)

theorem lvT_split {tys : List Ty} {d d' : List Nat} {e : Ex} {b : Tl} (h : (Tl.split e b).lvT tys d = some d') :
    ∃ τ σ d1 d'', tyOf tys e = some (.prod τ σ) ∧ e.lv tys d = some d1 ∧
      b.lvT (σ :: τ :: tys) (0 :: 0 :: d1) = some d'' ∧ d' = d''.drop 2 := by
  simp only [Tl.lvT] at h
  revert h
  split
  · rename_i τ σ d1 h1 h2
    cases hb : Tl.lvT (σ :: τ :: tys) (0 :: 0 :: d1) b with
    | none => simp
    | some d'' => simp only [Option.map_some, Option.some.injEq]; intro h; exact ⟨τ, σ, d1, d'', h1, h2, hb, h.symm⟩
  · simp

/-! ## `lv_step`: flags only go live → dead, for buffers; lengths are kept -/

theorem step_tail {tys : List Ty} {τ : Ty} {a : Nat} {d d'' : List Nat} (h : Step (τ :: tys) (a :: d) d'')
    (hl : d''.length = d.length + 1) : Step tys d d''.tail ∧ d''.tail.length = d.length := by
  refine ⟨fun k => ?_, by simp [hl]⟩
  rw [fl_tail]; have := h (k + 1); simpa [fl_cons_succ] using this

theorem step_drop2 {tys : List Ty} {τ σ : Ty} {a b : Nat} {d d'' : List Nat} (h : Step (σ :: τ :: tys) (a :: b :: d) d'')
    (hl : d''.length = d.length + 2) : Step tys d (d''.drop 2) ∧ (d''.drop 2).length = d.length := by
  refine ⟨fun k => ?_, by simp [hl]⟩
  rw [fl_drop2]; have := h (k + 2); simpa [fl_cons_succ] using this

theorem step_orL {tys : List Ty} {d x y : List Nat} (hx : Step tys d x) (hy : Step tys d y) (lx : x.length = d.length)
    (ly : y.length = d.length) : Step tys d (orL x y) ∧ (orL x y).length = d.length := by
  refine ⟨fun k => ?_, by simp [orL, lx, ly]⟩
  rw [fl_orL (lx.trans ly.symm)]
  rcases hx k with a | ⟨a1, a2, a3⟩ <;> rcases hy k with b | ⟨b1, b2, b3⟩
  · left; rw [a, b]; simp
  · right; refine ⟨b1, ?_, b3⟩; rw [a, b2]; omega
  · right; refine ⟨a1, ?_, a3⟩; rw [a2, b]; omega
  · right; refine ⟨a1, ?_, a3⟩; rw [a2, b2]; rfl

theorem step_alias {tys : List Ty} {τ : Ty} {d d'' : List Nat} {j m : Nat}
    (h : Step (τ :: tys) (1 :: d.set j m) d'') (hl : d''.length = d.length + 1) :
    Step tys d (d''.tail.set j (fl d j)) ∧ (d''.tail.set j (fl d j)).length = d.length := by
  obtain ⟨ht, htl⟩ := step_tail h (by simpa using hl)
  simp only [List.length_set] at htl
  refine ⟨fun k => ?_, by simp only [List.length_set]; exact htl⟩
  rw [fl_set]
  by_cases hk : k = j ∧ j < d''.tail.length
  · rw [if_pos hk, hk.1]; exact .inl rfl
  · rw [if_neg hk]
    rcases ht k with a | ⟨a1, a2, a3⟩
    · rw [a, fl_set]; split
      · next hk' => exact absurd ⟨hk'.1, by omega⟩ hk
      · exact .inl rfl
    · rw [fl_set] at a1; split at a1
      · next hk' => exact absurd ⟨hk'.1, by omega⟩ hk
      · exact .inr ⟨a1, a2, a3⟩

mutual
theorem lv_step : ∀ (e : Ex) (tys : List Ty) (d d' : List Nat), e.lv tys d = some d' →
    Step tys d d' ∧ d'.length = d.length
  | .var i, tys, d, d', h => by obtain ⟨a, b, _⟩ := use_spec (lv_var.1 h); exact ⟨a, b⟩
  | .lit _, _, d, d', h | .mk _, _, d, d', h | .isize, _, d, d', h => by
    simp only [Ex.lv, Option.some.injEq] at h; subst h; exact ⟨Step.refl _ _, rfl⟩
  | .bin _ a b, tys, d, d', h => by
    obtain ⟨d1, h1, h2⟩ := lv_bin h
    obtain ⟨s1, l1⟩ := lv_step a tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step b tys d1 d' h2
    exact ⟨s1.trans s2, l2.trans l1⟩
  | .pair a b, tys, d, d', h => by
    obtain ⟨d1, h1, h2⟩ := lv_pair h
    obtain ⟨s1, l1⟩ := lv_step a tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step b tys d1 d' h2
    exact ⟨s1.trans s2, l2.trans l1⟩
  | .fst a, tys, d, d', h => lv_step a tys d d' (lv_fst h)
  | .snd a, tys, d, d', h => lv_step a tys d d' (lv_snd h)
  | .iget a, tys, d, d', h => lv_step a tys d d' (lv_iget h)
  | .size a, tys, d, d', h => by
    rcases lv_size h with ⟨_, _, _, rfl⟩ | h1
    · exact ⟨Step.refl _ _, rfl⟩
    · exact lv_step a tys d d' h1
  | .get a j, tys, d, d', h => by
    rcases lv_get h with ⟨_, _, _, h1, _⟩ | ⟨d1, h1, h2⟩
    · exact lv_step j tys d d' h1
    · obtain ⟨s1, l1⟩ := lv_step a tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step j tys d1 d' h2
      exact ⟨s1.trans s2, l2.trans l1⟩
  | .set a j x, tys, d, d', h => by
    rcases lv_set h with ⟨i, d1, d2, _, _, h1, h2, h3⟩ | ⟨d1, d2, h1, h2, h3⟩
    · obtain ⟨s1, l1⟩ := lv_step j tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step x tys d1 d2 h2
      obtain ⟨s3, l3, _⟩ := use_spec h3
      exact ⟨(s1.trans s2).trans s3, by omega⟩
    · obtain ⟨s1, l1⟩ := lv_step a tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step j tys d1 d2 h2
      obtain ⟨s3, l3⟩ := lv_step x tys d2 d' h3
      exact ⟨(s1.trans s2).trans s3, by omega⟩
  | .push a x, tys, d, d', h => by
    rcases lv_push h with ⟨i, d1, _, _, h1, h2⟩ | ⟨d1, h1, h2⟩
    · obtain ⟨s1, l1⟩ := lv_step x tys d d1 h1; obtain ⟨s2, l2, _⟩ := use_spec h2
      exact ⟨s1.trans s2, by omega⟩
    · obtain ⟨s1, l1⟩ := lv_step a tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step x tys d1 d' h2
      exact ⟨s1.trans s2, l2.trans l1⟩
  | .ite _ a b t e, tys, d, d', h => by
    obtain ⟨d1, d2, x, y, h1, h2, h3, h4, rfl⟩ := lv_ite h
    obtain ⟨s1, l1⟩ := lv_step a tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step b tys d1 d2 h2
    obtain ⟨s3, l3⟩ := lv_step t tys d2 x h3; obtain ⟨s4, l4⟩ := lv_step e tys d2 y h4
    obtain ⟨s5, l5⟩ := step_orL s3 s4 l3 l4
    exact ⟨(s1.trans s2).trans s5, by omega⟩
  | .let_ v b, tys, d, d', h => by
    rcases lv_let h with ⟨j, τ, d'', rfl, _, _, _, h1, rfl⟩ | ⟨τ, d1, d'', _, h1, h2, rfl⟩
    · obtain ⟨s1, l1⟩ := lv_step b _ _ d'' h1
      exact step_alias s1 (by simpa using l1)
    · obtain ⟨s1, l1⟩ := lv_step v tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step b _ _ d'' h2
      obtain ⟨s3, l3⟩ := step_tail s2 (by simpa using l2)
      exact ⟨s1.trans s3, l3.trans l1⟩
  | .split e b, tys, d, d', h => by
    obtain ⟨τ, σ, d1, d'', _, h1, h2, rfl⟩ := lv_split h
    obtain ⟨s1, l1⟩ := lv_step e tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step b _ _ d'' h2
    obtain ⟨s3, l3⟩ := step_drop2 s2 (by simpa using l2)
    exact ⟨s1.trans s3, l3.trans l1⟩
  | .loop f i z t, tys, d, d', h => by
    obtain ⟨_, d1, _, _, _, h1, h2, _, _⟩ := lv_loop h
    obtain ⟨s1, l1⟩ := lv_step f tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step i tys d1 d' h2
    exact ⟨s1.trans s2, l2.trans l1⟩
theorem lvT_step : ∀ (t : Tl) (tys : List Ty) (d d' : List Nat), t.lvT tys d = some d' →
    Step tys d d' ∧ d'.length = d.length
  | .ret e, tys, d, d', h => lv_step e tys d d' (lvT_ret h)
  | .next e, tys, d, d', h => lv_step e tys d d' (lvT_next h)
  | .ite _ a b t e, tys, d, d', h => by
    obtain ⟨d1, d2, x, y, h1, h2, h3, h4, rfl⟩ := lvT_ite h
    obtain ⟨s1, l1⟩ := lv_step a tys d d1 h1; obtain ⟨s2, l2⟩ := lv_step b tys d1 d2 h2
    obtain ⟨s3, l3⟩ := lvT_step t tys d2 x h3; obtain ⟨s4, l4⟩ := lvT_step e tys d2 y h4
    obtain ⟨s5, l5⟩ := step_orL s3 s4 l3 l4
    exact ⟨(s1.trans s2).trans s5, by omega⟩
  | .let_ v b, tys, d, d', h => by
    rcases lvT_let h with ⟨j, τ, d'', rfl, _, _, _, h1, rfl⟩ | ⟨τ, d1, d'', _, h1, h2, rfl⟩
    · obtain ⟨s1, l1⟩ := lvT_step b _ _ d'' h1
      exact step_alias s1 (by simpa using l1)
    · obtain ⟨s1, l1⟩ := lv_step v tys d d1 h1; obtain ⟨s2, l2⟩ := lvT_step b _ _ d'' h2
      obtain ⟨s3, l3⟩ := step_tail s2 (by simpa using l2)
      exact ⟨s1.trans s3, l3.trans l1⟩
  | .split e b, tys, d, d', h => by
    obtain ⟨τ, σ, d1, d'', _, h1, h2, rfl⟩ := lvT_split h
    obtain ⟨s1, l1⟩ := lv_step e tys d d1 h1; obtain ⟨s2, l2⟩ := lvT_step b _ _ d'' h2
    obtain ⟨s3, l3⟩ := step_drop2 s2 (by simpa using l2)
    exact ⟨s1.trans s3, l3.trans l1⟩
end

/-! ## `cE`'s result type is `tyOf`'s (the checker types `let`/`split`/loops with `tyOf`) -/

theorem tyOf_var (env : List (Ty × Nat)) (i : Nat) : tyOf (env.map (·.1)) (.var i) = (env[i]?).map (·.1) := by
  simp [tyOf]

mutual
theorem cE_tyOf : ∀ (e : Ex) (env : List (Ty × Nat)) (n : Nat) (code : SC) (τ : Ty), cE env n e = some (code, τ) →
    tyOf (env.map (·.1)) e = some τ
  | .lit _, _, _, _, _, h => by simp only [cE, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl
  | .isize, _, _, _, _, h => by simp only [cE, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl
  | .mk _, _, _, _, _, h => by
    simp only [cE] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; rfl
    · simp at h
  | .var i, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i τ' p hi; split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [tyOf_var, hi, ← h.2]; rfl
      · simp at h
    · simp at h
  | .bin _ a b, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ha hb; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
      simp [tyOf, cE_tyOf a _ _ _ _ ha, cE_tyOf b _ _ _ _ hb]
    · simp at h
  | .ite _ a b t e, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ha hb ht he; split at h
      · rename_i heq; subst heq; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
        simp [tyOf, cE_tyOf a _ _ _ _ ha, cE_tyOf b _ _ _ _ hb, cE_tyOf t _ _ _ _ ht, cE_tyOf e _ _ _ _ he]
      · simp at h
    · simp at h
  | .let_ v b, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i cv τv hv; split at h
      · rename_i cb ρ hb; split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
          have := cE_tyOf b _ _ _ _ hb; simp only [List.map_cons] at this
          simp [tyOf, cE_tyOf v _ _ _ _ hv, this]
        · simp at h
      · simp at h
    · simp at h
  | .pair a b, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ca τa ha; split at h
      · rename_i cb τb hb; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
        simp [tyOf, cE_tyOf a _ _ _ _ ha, cE_tyOf b _ _ _ _ hb]
      · simp at h
    · simp at h
  | .fst a, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ce τ1 σ1 ha; split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; simp [tyOf, cE_tyOf a _ _ _ _ ha]
      · simp at h
    · simp at h
  | .snd a, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ce τ1 σ1 ha; split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; simp [tyOf, cE_tyOf a _ _ _ _ ha]
      · simp at h
    · simp at h
  | .split e b, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ce τ1 σ1 he; split at h
      · rename_i cb ρ hb; split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
          have := cE_tyOf b _ _ _ _ hb; simp only [List.map_cons] at this
          simp [tyOf, cE_tyOf e _ _ _ _ he, this]
        · simp at h
      · simp at h
    · simp at h
  | .size a, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ha; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; simp [tyOf, cE_tyOf a _ _ _ _ ha]
    · simp at h
  | .iget a, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ha; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; simp [tyOf, cE_tyOf a _ _ _ _ ha]
    · simp at h
  | .get a b, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ha hb; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
      simp [tyOf, cE_tyOf a _ _ _ _ ha, cE_tyOf b _ _ _ _ hb]
    · simp at h
  | .push a b, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ha hb; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
      simp [tyOf, cE_tyOf a _ _ _ _ ha, cE_tyOf b _ _ _ _ hb]
    · simp at h
  | .set a b x, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i ha hb hx; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
      simp [tyOf, cE_tyOf a _ _ _ _ ha, cE_tyOf b _ _ _ _ hb, cE_tyOf x _ _ _ _ hx]
    · simp at h
  | .loop f i z t, env, n, code, τ, h => by
    unfold cE at h; split at h
    · rename_i cf ci σ hf hi; simp only at h; split at h
      · rename_i cz ρ hz; split at h
        · rename_i cb hb; split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
            have h1 := cE_tyOf z _ _ _ _ hz; simp only [List.map_cons] at h1
            have h2 := cT_tyT t _ _ _ _ _ _ hb; simp only [List.map_cons] at h2
            simp [tyOf, cE_tyOf f _ _ _ _ hf, cE_tyOf i _ _ _ _ hi, h1, h2]
          · simp at h
        · simp at h
      · simp at h
    · simp at h
theorem cT_tyT : ∀ (t : Tl) (env : List (Ty × Nat)) (D : Nat) (σ ρ : Ty) (x : Nat) (code : SC),
    cT env D σ ρ x t = some code → tyT (env.map (·.1)) σ ρ t = true
  | .ret e, env, D, σ, ρ, x, code, h => by
    unfold cT at h; split at h
    · rename_i ce τ he; split at h
      · rename_i hc; simp [tyT, cE_tyOf e _ _ _ _ he, hc.1]
      · simp at h
    · simp at h
  | .next e, env, D, σ, ρ, x, code, h => by
    unfold cT at h; split at h
    · rename_i ce τ he; split at h
      · rename_i hc; simp [tyT, cE_tyOf e _ _ _ _ he, hc.1]
      · simp at h
    · simp at h
  | .ite _ a b t e, env, D, σ, ρ, x, code, h => by
    unfold cT at h; split at h
    · rename_i ca cb ct ce ha hb ht he
      simp [tyT, cE_tyOf a _ _ _ _ ha, cE_tyOf b _ _ _ _ hb, cT_tyT t _ _ _ _ _ _ ht, cT_tyT e _ _ _ _ _ _ he]
    · simp at h
  | .let_ v b, env, D, σ, ρ, x, code, h => by
    unfold cT at h; split at h
    · rename_i cv τ hv; split at h
      · rename_i cb hb
        have := cT_tyT b _ _ _ _ _ _ hb; simp only [List.map_cons] at this
        simp [tyT, cE_tyOf v _ _ _ _ hv, this]
      · simp at h
    · simp at h
  | .split e b, env, D, σ, ρ, x, code, h => by
    unfold cT at h; split at h
    · rename_i ce τ τ' he; split at h
      · rename_i cb hb
        have := cT_tyT b _ _ _ _ _ _ hb; simp only [List.map_cons] at this
        simp [tyT, cE_tyOf e _ _ _ _ he, this]
      · simp at h
    · simp at h
end

end Nano.V2B
