/- Nano/SelfHost/SrcLink/SrcLink: generic lemmas for the kernel-checked link between C's source text and its parse
(`refParse (lex text) = some AST`), checked per def: (1) the reference lexer `lexAll` is sound for `LexSpec.Lexes`;
(2) `Lexes` composes across chunks ending in a newline; (3) `tokens` composes; (4) `pDefs` composes def by def. -/
import Nano.Parser.ParSpec

namespace SrcLink
open ParSpec LexSpec

/-! ## (1) the reference lexer is sound -/
theorem lexAcc_sound : ∀ (f : Nat) (l : List UInt8) (acc out : List UInt64), lexAcc f l acc = some out →
    ∃ t, out = acc.reverse ++ t ∧ Lexes l t
  | _, [], acc, out, h => by simp only [lexAcc, Option.some.injEq] at h; exact ⟨[], by simp [h], .nil⟩
  | 0, _ :: _, _, _, h => by simp [lexAcc] at h
  | f + 1, c :: r, acc, out, h => by
    simp only [lexAcc] at h
    obtain ⟨⟨e, r'⟩, hs, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t, rfl, hl⟩ := lexAcc_sound f r' _ out h
    exact ⟨e ++ t, by simp, .cons hs hl⟩

theorem lexAll_sound {f : Nat} {l : List UInt8} {t : List UInt64} (h : lexAll f l = some t) : Lexes l t := by
  obtain ⟨t', e, hl⟩ := lexAcc_sound f l [] t h; simp at e; subst e; exact hl

/-! ## (2) chunks ending in a newline compose -/
theorem isPrefixOf_app : ∀ (p l m : List UInt8), 10 ∉ p → l.getLast? = some 10 →
    p.isPrefixOf (l ++ m) = p.isPrefixOf l
  | [], _, _, _, _ => by simp [List.isPrefixOf]
  | _ :: _, [], _, _, h => by simp at h
  | a :: p, [b], m, hp, h => by
    simp at h; subst h
    have : (a == 10) = false := by simpa using fun e => hp (by simp [e])
    simp [List.isPrefixOf, this]
  | a :: p, b :: c :: l, m, hp, h => by
    have ih := isPrefixOf_app p (c :: l) m (fun e => hp (by simp [e])) (by simpa using h)
    simp only [List.cons_append, List.isPrefixOf] at ih ⊢
    rw [ih]

theorem find?_congr {α : Type} {p q : α → Bool} : ∀ (L : List α), (∀ x ∈ L, p x = q x) → L.find? p = L.find? q
  | [], _ => rfl
  | x :: L, h => by
    simp only [List.find?_cons, h x (by simp)]
    rw [find?_congr L (fun y hy => h y (by simp [hy]))]

theorem takeWhile_app {p : UInt8 → Bool} : ∀ (l m : List UInt8), (∃ x ∈ l, p x = false) →
    (l ++ m).takeWhile p = l.takeWhile p ∧ (l ++ m).dropWhile p = l.dropWhile p ++ m
  | [], _, ⟨_, h, _⟩ => by simp at h
  | x :: l, m, ⟨y, hy, hpy⟩ => by
    by_cases hx : p x = true
    · have : ∃ z ∈ l, p z = false := by
        rcases List.mem_cons.1 hy with rfl | h
        · rw [hx] at hpy; cases hpy
        · exact ⟨y, h, hpy⟩
      obtain ⟨h1, h2⟩ := takeWhile_app l m this
      simp [List.takeWhile_cons, List.dropWhile_cons, hx, h1, h2]
    · simp [List.takeWhile_cons, List.dropWhile_cons, hx]

theorem op_no10 : ∀ e ∈ opTable, 10 ∉ e.1 := by decide

theorem last_of_suffix {l s : List UInt8} (h : s <:+ l) (hs : s ≠ []) : s.getLast? = l.getLast? := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getLast?_append]; cases e : s.getLast? with
  | none => simp at e; exact absurd e hs
  | some _ => rfl

theorem mem_dropWhile {p : UInt8 → Bool} {x : UInt8} : ∀ (l : List UInt8), x ∈ l → p x = false → x ∈ l.dropWhile p
  | [], h, _ => by simp at h
  | y :: l, h, hx => by
    by_cases hy : p y = true
    · rw [List.dropWhile_cons_of_pos hy]
      rcases List.mem_cons.1 h with rfl | h'
      · rw [hy] at hx; cases hx
      · exact mem_dropWhile l h' hx
    · rw [List.dropWhile_cons_of_neg hy]; exact h

theorem dw_head {p : UInt8 → Bool} : ∀ (l : List UInt8) (a : UInt8) (t : List UInt8), l.dropWhile p = a :: t → p a = false
  | [], _, _, h => by simp at h
  | y :: l, a, t, h => by
    by_cases hy : p y = true
    · rw [List.dropWhile_cons_of_pos hy] at h; exact dw_head l a t h
    · rw [List.dropWhile_cons_of_neg hy] at h; cases h; simpa using hy

theorem blockEnd_app : ∀ (d : Nat) (l m t : List UInt8), blockEnd d l = some t → blockEnd d (l ++ m) = some (t ++ m) ∧ t <:+ l
  | _, [], _, _, h => by simp [blockEnd] at h
  | _, [_], _, _, h => by simp [blockEnd] at h
  | d, c :: c' :: r, m, t, h => by
    simp only [List.cons_append, blockEnd] at h ⊢
    have s1 : r <:+ c :: c' :: r := (List.suffix_cons _ _).trans (List.suffix_cons _ _)
    have s2 : c' :: r <:+ c :: c' :: r := List.suffix_cons _ _
    split at h
    · rename_i h1; rw [if_pos h1]
      split at h
      · rename_i h2; rw [if_pos h2]; cases h; exact ⟨rfl, s1⟩
      · rename_i h2; rw [if_neg h2]; obtain ⟨a, b⟩ := blockEnd_app _ r m t h; exact ⟨a, b.trans s1⟩
    · rename_i h1; rw [if_neg h1]
      split at h
      · rename_i h2; rw [if_pos h2]; obtain ⟨a, b⟩ := blockEnd_app _ r m t h; exact ⟨a, b.trans s1⟩
      · rename_i h2; rw [if_neg h2]
        obtain ⟨a, b⟩ := blockEnd_app _ (c' :: r) m t h
        simp only [List.cons_append] at a; exact ⟨a, b.trans s2⟩

theorem attrEnd_app : ∀ (l w : List UInt8) (d : Bool) (m t : List UInt8), attrEnd l w d = some t →
    attrEnd (l ++ m) w d = some (t ++ m) ∧ t <:+ l
  | [], _, _, _, _, h => by simp [attrEnd] at h
  | b :: r, w, d, m, t, h => by
    simp only [List.cons_append, attrEnd] at h ⊢
    have IH := fun w d h => attrEnd_app r w d m t h
    have sr := List.suffix_cons b r
    split at h
    · rename_i h1; rw [if_pos h1]; split at h
      · cases h
      · rename_i h2; rw [if_neg h2]; obtain ⟨a, b'⟩ := IH _ _ h; exact ⟨a, b'.trans sr⟩
    · rename_i h1; rw [if_neg h1]; split at h
      · cases h
      · rename_i h2; rw [if_neg h2]
        split at h
        · rename_i h3; rw [if_pos h3]; obtain ⟨a, b'⟩ := IH _ _ h; exact ⟨a, b'.trans sr⟩
        · rename_i h3; rw [if_neg h3]; split at h
          · rename_i h4; rw [if_pos h4]; split at h
            · rename_i h5; rw [if_pos h5]; obtain ⟨a, b'⟩ := IH _ _ h; exact ⟨a, b'.trans sr⟩
            · cases h
          · rename_i h4; rw [if_neg h4]; split at h
            · rename_i h5; rw [if_pos h5]; split at h
              · rename_i h6; rw [if_pos h6]; cases h; exact ⟨rfl, sr⟩
              · cases h
            · cases h

theorem scopeLine_app (k : Nat) (r m n e : List UInt8) (hr : (10 : UInt8) ∈ r) (h : scopeLine k r = some (n, e)) :
    scopeLine k (r ++ m) = some (n, e ++ m) ∧ e <:+ r := by
  unfold scopeLine at h ⊢
  simp only at h ⊢
  obtain ⟨-, a2⟩ := takeWhile_app (p := (· == 32)) r m ⟨10, hr, by decide⟩
  rw [a2]
  have h1 : (10 : UInt8) ∈ r.dropWhile (· == 32) := mem_dropWhile _ hr (by decide)
  obtain ⟨b1, b2⟩ := takeWhile_app (p := isW) (r.dropWhile (· == 32)) m ⟨10, h1, by decide⟩
  rw [b1, b2]
  have h2 : (10 : UInt8) ∈ (r.dropWhile (· == 32)).dropWhile isW := mem_dropWhile _ h1 (by decide)
  obtain ⟨-, c2⟩ := takeWhile_app (p := (· == 32)) _ m ⟨10, h2, by decide⟩
  rw [c2]
  have h3 : (10 : UInt8) ∈ ((r.dropWhile (· == 32)).dropWhile isW).dropWhile (· == 32) := mem_dropWhile _ h2 (by decide)
  have hE : ∀ (E : List UInt8), (10 : UInt8) ∈ E → (E ++ m).head? = E.head? := fun E hE => by
    cases E with
    | nil => simp at hE
    | cons a E => rfl
  rw [hE _ h3, hE r hr]
  have sfx : ((r.dropWhile (· == 32)).dropWhile isW).dropWhile (· == 32) <:+ r :=
    (List.dropWhile_suffix _).trans ((List.dropWhile_suffix _).trans (List.dropWhile_suffix _))
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hc, rfl, rfl⟩ := h
  rw [if_pos hc]; exact ⟨rfl, sfx⟩

theorem last_cons {c : UInt8} {r : List UInt8} (hl : (c :: r).getLast? = some 10) (hr : r ≠ []) : r.getLast? = some 10 := by
  rw [← hl, last_of_suffix (List.suffix_cons c r) hr]

theorem docWs_nil (f : Nat) (t : List UInt8) (h : docWs f [] = some t) : t = [] := by
  cases f with
  | zero => simp [docWs] at h
  | succ f => simp [docWs] at h; exact h

theorem docWs_app : ∀ (F F' : Nat) (l m t : List UInt8), F ≤ F' → l.getLast? = some 10 → docWs F l = some t →
    t ≠ [] → docWs F' (l ++ m) = some (t ++ m) ∧ t <:+ l
  | 0, _, _, _, _, _, _, h, _ => by simp [docWs] at h
  | _ + 1, _, [], _, _, _, hl, _, _ => by simp at hl
  | f + 1, F', c :: r, m, t, hF, hl, h, ht => by
    obtain ⟨f', rfl⟩ : ∃ f', F' = f' + 1 := ⟨F' - 1, by omega⟩
    by_cases hr0 : r = []
    · subst hr0
      simp at hl; subst hl
      simp only [docWs] at h
      rw [if_pos (by simp)] at h; exact absurd (docWs_nil f t h) ht
    have hlr := last_cons hl hr0
    have hh : (r ++ m).head? = r.head? := by
      cases r with
      | nil => exact absurd rfl hr0
      | cons a r => rfl
    have htl : (r ++ m).tail = r.tail ++ m := List.tail_append_of_ne_nil hr0
    have sr : r <:+ c :: r := List.suffix_cons _ _
    have t45 : r.head? = some 45 → r.tail ≠ [] := fun e e2 => by
      obtain ⟨a, rfl⟩ : ∃ a, r = [a] := by
        cases r with
        | nil => exact absurd rfl hr0
        | cons a r' => simp at e2; exact ⟨a, by rw [e2]⟩
      simp at e hlr; rw [e] at hlr; cases hlr
    have hh2 : r.head? = some 45 → (r.tail ++ m).head? = r.tail.head? := fun e => by
      have := t45 e
      cases hq : r.tail with
      | nil => exact absurd hq this
      | cons a r => rfl
    simp only [List.cons_append, docWs] at h ⊢
    rw [hh, htl]
    split at h
    · rename_i h1; rw [if_pos h1]
      obtain ⟨a, b⟩ := docWs_app f f' r m t (by omega) hlr h ht
      exact ⟨a, b.trans sr⟩
    rename_i h1; rw [if_neg h1]
    split at h
    · cases h
    rename_i h1'; rw [if_neg h1']
    split at h
    · rename_i h2; rw [if_pos h2]
      have h10 : (10 : UInt8) ∈ r := List.mem_of_getLast? hlr
      obtain ⟨-, d2⟩ := takeWhile_app (p := (· != 10)) r m ⟨10, h10, by decide⟩
      rw [d2]
      have sd : r.dropWhile (· != 10) <:+ r := List.dropWhile_suffix _
      have hne : r.dropWhile (· != 10) ≠ [] := fun e => by
        rw [e] at h; exact ht (docWs_nil f t h)
      obtain ⟨a, b⟩ := docWs_app f f' _ m t (by omega) (by rw [← hlr]; exact last_of_suffix sd hne) h ht
      exact ⟨a, b.trans (sd.trans sr)⟩
    rename_i h2; rw [if_neg h2]
    split at h
    · rename_i h3
      rw [hh2 h3.2.1, if_pos h3]
      have htt : (r.tail ++ m).tail = r.tail.tail ++ m := List.tail_append_of_ne_nil (t45 h3.2.1)
      rw [htt]
      obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨b1, b2⟩ := blockEnd_app 0 r.tail.tail m u hu
      rw [b1, Option.bind_some]
      have hne : u ≠ [] := fun e => by rw [e] at hd; exact ht (docWs_nil f t hd)
      have su : u <:+ c :: r := b2.trans ((List.tail_suffix _).trans ((List.tail_suffix r).trans sr))
      obtain ⟨a, b⟩ := docWs_app f f' u m t (by omega) (by rw [← hl]; exact last_of_suffix su hne) hd ht
      exact ⟨a, b.trans su⟩
    · rename_i h3
      have h3' : ¬ (c = 47 ∧ r.head? = some 45 ∧ (r.tail ++ m).head? ≠ some 45 ∧ (r.tail ++ m).head? ≠ some 33) := by
        intro e; rw [hh2 e.2.1] at e; exact h3 e
      rw [if_neg h3']; cases h; exact ⟨rfl, List.suffix_refl _⟩

theorem startsWord_app (w u m : List UInt8) (hw : 10 ∉ w) (hu : u.getLast? = some 10) :
    startsWord w (u ++ m) = startsWord w u := by
  unfold startsWord
  rw [isPrefixOf_app w u m hw hu]
  cases hp : w.isPrefixOf u
  · simp
  · have hpre := List.isPrefixOf_iff_prefix.1 hp
    have hlen : w.length < u.length := by
      rcases Nat.lt_or_eq_of_le hpre.length_le with h | h
      · exact h
      · exfalso
        have := hpre.eq_of_length h
        subst this; exact hw (List.mem_of_getLast? hu)
    rw [List.drop_append_of_le_length (by omega)]
    obtain ⟨x0, xs, hx⟩ : ∃ x0 xs, u.drop w.length = x0 :: xs := by
      cases e : u.drop w.length with
      | nil => have := congrArg List.length e; simp at this; omega
      | cons x0 xs => exact ⟨x0, xs, rfl⟩
    rw [hx]; rfl

theorem declNext_app (k : Nat) (t m : List UInt8) (ht : t.getLast? = some 10) (h : declNext k t = true) :
    declNext k (t ++ m) = true := by
  unfold declNext at h ⊢
  cases hd : docWs (t.length + 1) t with
  | none => rw [hd] at h; cases h
  | some u =>
    rw [hd] at h
    have hu : u ≠ [] := by rintro rfl; simp [startsWord, PRIV, DEF, List.isPrefixOf] at h
    obtain ⟨a1, a2⟩ := docWs_app _ ((t ++ m).length + 1) t m u (by simp) ht hd hu
    rw [a1]
    have hul : u.getLast? = some 10 := by rw [← ht]; exact last_of_suffix a2 hu
    simp only
    rw [isPrefixOf_app _ u m (by decide) hul, startsWord_app _ u m (by decide) hul, startsWord_app _ u m (by decide) hul]
    exact h

theorem cmdNext_app (t m : List UInt8) (ht : t.getLast? = some 10) (h : cmdNext t = true) : cmdNext (t ++ m) = true := by
  unfold cmdNext at h ⊢
  cases hd : docWs (t.length + 1) t with
  | none => rw [hd] at h; cases h
  | some u =>
    rw [hd] at h
    have hu : u ≠ [] := by rintro rfl; simp [startsWord, PRIV, DEF, NS, SEC, END, List.isPrefixOf] at h
    obtain ⟨a1, a2⟩ := docWs_app _ ((t ++ m).length + 1) t m u (by simp) ht hd hu
    rw [a1]
    have hul : u.getLast? = some 10 := by rw [← ht]; exact last_of_suffix a2 hu
    simp only
    rw [isPrefixOf_app _ u m (by decide) hul, isPrefixOf_app _ u m (by decide) hul, startsWord_app _ u m (by decide) hul,
      startsWord_app _ u m (by decide) hul, startsWord_app _ u m (by decide) hul, startsWord_app _ u m (by decide) hul,
      startsWord_app _ u m (by decide) hul]
    exact h

theorem step_app {l m : List UInt8} {e : List UInt64} {r : List UInt8} (hl : l.getLast? = some 10)
    (h : step l = some (e, r)) : step (l ++ m) = some (e, r ++ m) ∧ (r = [] ∨ r.getLast? = some 10) := by
  match l, hl, h with
  | c :: r0, hl, h =>
    have suf : ∀ s, s <:+ (c :: r0) → s = [] ∨ s.getLast? = some 10 := fun s hs => by
      by_cases e : s = []
      · exact .inl e
      · exact .inr (by rw [last_of_suffix hs e, hl])
    have h10 : (10 : UInt8) ∈ c :: r0 := List.mem_of_getLast? hl
    simp only [step] at h ⊢
    simp only [List.cons_append]
    split at h
    · rename_i hw; rw [if_pos hw]; cases h
      exact ⟨rfl, suf _ (List.suffix_cons _ _)⟩
    rename_i hw; rw [if_neg hw]
    have hne : r0 ≠ [] := by
      rintro rfl; simp at hl; subst hl; exact hw (by decide)
    obtain ⟨a0, r1, rfl⟩ : ∃ a0 r1, r0 = a0 :: r1 := by
      cases r0 with
      | nil => exact absurd rfl hne
      | cons a0 r1 => exact ⟨a0, r1, rfl⟩
    simp only [List.cons_append, List.head?_cons, List.tail_cons] at h ⊢
    have hc10 : c ≠ 10 := fun e => hw (by simp [e])
    have h10r : (10 : UInt8) ∈ a0 :: r1 := by
      rcases List.mem_cons.1 h10 with e | e
      · exact absurd e.symm hc10
      · exact e
    have sr1 : r1 <:+ c :: a0 :: r1 := (List.suffix_cons _ _).trans (List.suffix_cons _ _)
    split at h
    · rename_i h45; rw [if_pos h45]; cases h
      have ha0 : a0 = 45 := by simp at h45; exact h45.2
      have hm : (10 : UInt8) ∈ r1 := by
        rcases List.mem_cons.1 h10r with e | e
        · rw [ha0] at e; cases e
        · exact e
      obtain ⟨-, t2⟩ := takeWhile_app (p := (· != 10)) r1 m ⟨10, hm, by decide⟩
      rw [t2]; exact ⟨rfl, suf _ ((List.dropWhile_suffix _).trans sr1)⟩
    rename_i h45; rw [if_neg h45]
    split at h
    · rename_i h47; rw [if_pos h47]
      obtain ⟨t, hb, he⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨hdn, hcn, rfl, rfl⟩ : (r1.head? = some 45 → declNext 2 t = true) ∧
          (r1.head? = some 33 → cmdNext t = true) ∧ e = [] ∧ t = r := by
        cases hb2 : (r1.head? == some 45 && !declNext 2 t)
        · cases hb3 : (r1.head? == some 33 && !cmdNext t)
          · simp only [hb2, hb3, Bool.false_eq_true, if_false, ite_false, Option.some.injEq, Prod.mk.injEq] at he
            exact ⟨fun e => by simpa [e] using hb2, fun e => by simpa [e] using hb3, he.1.symm, he.2⟩
          · simp [hb2, hb3] at he
        · simp [hb2] at he
      have ha0 : a0 = 45 := by simp at h47; exact h47.2
      have hr1 : r1 ≠ [] := by rintro rfl; simp at hl; rw [ha0] at hl; cases hl
      have hh : (r1 ++ m).head? = r1.head? := by
        cases r1 with
        | nil => exact absurd rfl hr1
        | cons a r => rfl
      simp only [hh]
      by_cases hc : (r1.head? == some 45 || r1.head? == some 33) = true
      · rw [if_pos hc]; simp only [hc, ite_true] at hb
        obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.1 hb
        have hune : u ≠ [] := fun e => by rw [e] at hd; simp [blockEnd] at hd
        have hr1t : r1.tail ≠ [] := fun e => by rw [e] at hu; exact hune (docWs_nil _ _ hu)
        have sl : r1.tail <:+ c :: a0 :: r1 := (List.tail_suffix _).trans sr1
        obtain ⟨a1, a2⟩ := docWs_app _ (a0 :: (r1 ++ m)).length r1.tail m u
          (by simp only [List.length_cons, List.length_append]; omega)
          (by rw [← hl]; exact last_of_suffix sl hr1t) hu hune
        have htl : (r1 ++ m).tail = r1.tail ++ m := List.tail_append_of_ne_nil hr1
        rw [htl, a1, Option.bind_some]
        obtain ⟨b1, b2⟩ := blockEnd_app 0 u m t hd
        have st : t <:+ c :: a0 :: r1 := b2.trans (a2.trans sl)
        rw [b1, Option.bind_some]
        have hdn' : (r1.head? == some 45 && !declNext 2 (t ++ m)) = false := by
          by_cases e : r1.head? = some 45
          · have d := hdn e
            have htn : t ≠ [] := by rintro rfl; simp [declNext, docWs, startsWord, PRIV, DEF, List.isPrefixOf] at d
            simp [declNext_app 2 t m (by rw [← hl]; exact last_of_suffix st htn) d]
          · simp [e]
        have hcn' : (r1.head? == some 33 && !cmdNext (t ++ m)) = false := by
          by_cases e : r1.head? = some 33
          · have d := hcn e
            have htn : t ≠ [] := by rintro rfl; simp [cmdNext, docWs, List.isPrefixOf, startsWord, PRIV, DEF, NS, SEC, END] at d
            simp [cmdNext_app t m (by rw [← hl]; exact last_of_suffix st htn) d]
          · simp [e]
        simp only [hdn', hcn', Bool.false_eq_true, if_false]; exact ⟨trivial, suf _ st⟩
      · rw [if_neg hc]
        have hc' : (r1.head? == some 45 || r1.head? == some 33) = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, ite_false] at hb
        have htl : (r1 ++ m).tail = r1.tail ++ m := List.tail_append_of_ne_nil hr1
        rw [htl]
        obtain ⟨b1, b2⟩ := blockEnd_app 0 r1.tail m t hb
        have n45 : (r1.head? == some 45) = false := by
          cases e : r1.head? == some 45
          · rfl
          · exact absurd (by simp [e]) hc
        have n33 : (r1.head? == some 33) = false := by
          cases e : r1.head? == some 33
          · rfl
          · exact absurd (by simp [e]) hc
        rw [b1, Option.bind_some]; simp only [n45, n33, Bool.false_and, Bool.false_eq_true, if_false]
        exact ⟨trivial, suf _ (b2.trans ((List.tail_suffix _).trans sr1))⟩
    rename_i h47; rw [if_neg h47]
    split at h
    · rename_i h64; rw [if_pos h64]
      obtain ⟨t, hb, he⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨hdn, rfl, rfl⟩ : declNext 1 t = true ∧ e = [] ∧ t = r := by
        cases hb2 : declNext 1 t
        · simp [hb2] at he
        · simp only [hb2, if_true, ite_true, Option.some.injEq, Prod.mk.injEq] at he
          exact ⟨rfl, he.1.symm, he.2⟩
      obtain ⟨b1, b2⟩ := attrEnd_app r1 [] false m t hb
      have st : t <:+ c :: a0 :: r1 := b2.trans sr1
      have htn : t ≠ [] := by rintro rfl; simp [declNext, docWs, startsWord, PRIV, DEF, List.isPrefixOf] at hdn
      rw [b1, Option.bind_some]
      simp only [declNext_app 1 t m (by rw [← hl]; exact last_of_suffix st htn) hdn, if_true, ite_true]
      exact ⟨trivial, suf _ st⟩
    rename_i h64; rw [if_neg h64]
    have hf : opTable.find? (fun e => e.1.isPrefixOf (c :: a0 :: (r1 ++ m))) =
        opTable.find? (fun e => e.1.isPrefixOf (c :: a0 :: r1)) :=
      find?_congr _ (fun x hx => by
        have := isPrefixOf_app x.1 (c :: a0 :: r1) m (op_no10 x hx) hl; simpa using this)
    rw [hf]
    split at h
    · rename_i s k hfd
      cases h
      have hpre : s.isPrefixOf (c :: a0 :: r1) = true := by
        have := List.find?_some hfd; simpa using this
      have hle : s.length ≤ (c :: a0 :: r1).length := (List.isPrefixOf_iff_prefix.1 hpre).length_le
      refine ⟨?_, suf _ (List.drop_suffix _ _)⟩
      have := List.drop_append_of_le_length (l₁ := c :: a0 :: r1) (l₂ := m) hle
      simp only [List.cons_append] at this; rw [this]
    · have h10' : ∃ x ∈ c :: a0 :: r1, isW x = false := ⟨10, h10, by decide⟩
      obtain ⟨t1, t2⟩ := takeWhile_app (p := isW) (c :: a0 :: r1) m h10'
      simp only [List.cons_append] at t1 t2
      rw [t1, t2]
      have sd : (c :: a0 :: r1).dropWhile isW <:+ c :: a0 :: r1 := List.dropWhile_suffix _
      split at h
      · split at h
        · cases h; rw [if_pos ‹_›, if_pos ‹_›]; exact ⟨rfl, suf _ sd⟩
        · cases h
      · split at h
        · rename_i hd hwc
          rw [if_neg hd, if_pos hwc]
          split at h
          · cases h
          rename_i hop; rw [if_neg hop]
          have hm := mem_dropWhile (p := isW) _ h10 (by decide)
          rcases hsk : scopeKw.lookup ((c :: a0 :: r1).takeWhile isW) with _ | k
          · simp only [hsk] at h ⊢
            split at h
            · rename_i hdk
              split at h
              · rename_i hdn
                cases h; rw [if_pos hdk]
                have hne : (c :: a0 :: r1).dropWhile isW ≠ [] := fun e => by rw [e] at hm; simp at hm
                rw [if_pos (declNext_app 0 _ m (by rw [← hl]; exact last_of_suffix sd hne) hdn)]
                exact ⟨rfl, suf _ sd⟩
              · cases h
            · cases h; rw [if_neg ‹_›]; exact ⟨rfl, suf _ sd⟩
          · simp only [hsk] at h ⊢
            obtain ⟨⟨n, e'⟩, hs, he⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
            obtain ⟨s1, s2⟩ := scopeLine_app k _ m n e' hm hs
            simp only [s1, Option.map_some]
            exact ⟨trivial, suf _ (s2.trans sd)⟩
        · cases h

theorem lexes_app {x1 : List UInt8} {x2 : List UInt8} {t1 t2 : List UInt64} (h1 : Lexes x1 t1) (h2 : Lexes x2 t2)
    (hl : x1 = [] ∨ x1.getLast? = some 10) : Lexes (x1 ++ x2) (t1 ++ t2) := by
  revert hl
  induction h1 with
  | nil => intro _; simpa using h2
  | cons hs hr ih =>
    intro hl
    rcases hl with hl | hl
    · subst hl; simp [step] at hs
    obtain ⟨hs', hr'⟩ := step_app (m := x2) hl hs
    rw [List.append_assoc]
    exact .cons hs' (ih hr')

/-! ## (3) `tokens` composes -/
theorem idn_app : ∀ (l m : List Nat) {n r : List Nat}, idn l = some (n, r) → idn (l ++ m) = some (n, r ++ m)
  | 0 :: l, m, n, r, h => by simp only [idn, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | 1 :: b :: l, m, n, r, h => by
    simp only [idn] at h ⊢
    obtain ⟨⟨n', r'⟩, h1, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [List.cons_append, idn, idn_app l m h1, Option.map_some]
  | [], _, _, _, h => by simp [idn] at h
  | [1], _, _, _, h => by simp [idn] at h
  | (k + 2) :: _, _, _, _, h => by simp [idn] at h

theorem idn_len : ∀ (l : List Nat) {n r : List Nat}, idn l = some (n, r) → r.length < l.length
  | 0 :: l, n, r, h => by simp only [idn, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
  | 1 :: b :: l, n, r, h => by
    simp only [idn] at h
    obtain ⟨⟨n', r'⟩, h1, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
    have := idn_len l h1; simp; omega
  | [], _, _, h => by simp [idn] at h
  | [1], _, _, h => by simp [idn] at h
  | (k + 2) :: _, _, _, h => by simp [idn] at h

theorem detokA_mono : ∀ (f k : Nat) (l : List Nat) (acc out : List Tok), detokA f l acc = some out →
    detokA (f + k) l acc = some out
  | _, _, [], acc, out, h => by simp only [detokA] at h ⊢; exact h
  | 0, _, _ :: _, _, _, h => by simp [detokA] at h
  | f + 1, k, t :: r, acc, out, h => by
    rw [show f + 1 + k = (f + k) + 1 by omega]
    simp only [detokA] at h ⊢
    split at h
    · rw [if_pos ‹_›]; split at h
      · rw [if_pos ‹_›]; exact detokA_mono f k _ _ _ h
      · cases h
    · rw [if_neg ‹_›]; split at h
      · rw [if_pos ‹_›]
        obtain ⟨⟨n, r'⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
        rw [h1]; exact detokA_mono f k _ _ _ h
      · rw [if_neg ‹_›]; split at h
        · rw [if_pos ‹_›]; exact detokA_mono f k _ _ _ h
        · cases h

theorem detokA_len : ∀ (f : Nat) (l : List Nat) (acc out : List Tok), detokA f l acc = some out →
    detokA (l.length + 1) l acc = some out
  | _, [], acc, out, h => by simp only [detokA] at h ⊢; exact h
  | 0, _ :: _, _, _, h => by simp [detokA] at h
  | f + 1, t :: r, acc, out, h => by
    simp only [detokA, List.length_cons] at h ⊢
    split at h
    · rw [if_pos ‹_›]; split at h
      · rename_i h8; rw [if_pos h8]
        have := detokA_mono _ (r.length - (r.drop 8).length) _ _ _ (detokA_len f _ _ _ h)
        rw [show (r.drop 8).length + 1 + (r.length - (r.drop 8).length) = r.length + 1 by simp; omega] at this
        exact this
      · cases h
    · rw [if_neg ‹_›]; split at h
      · rw [if_pos ‹_›]
        obtain ⟨⟨n, r'⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
        rw [h1]; simp only [Option.bind_some]
        have hl := idn_len r h1
        have := detokA_mono _ (r.length - r'.length) _ _ _ (detokA_len f _ _ _ h)
        rw [show r'.length + 1 + (r.length - r'.length) = r.length + 1 by omega] at this
        exact this
      · rw [if_neg ‹_›]; split at h
        · rw [if_pos ‹_›]; exact detokA_len f _ _ _ h
        · cases h

theorem detokA_acc2 : ∀ (f : Nat) (l : List Nat) (acc acc2 : List Tok),
    detokA f l (acc ++ acc2) = (detokA f l acc).map (acc2.reverse ++ ·)
  | _, [], acc, acc2 => by simp [detokA]
  | 0, _ :: _, _, _ => by simp [detokA]
  | f + 1, t :: r, acc, acc2 => by
    simp only [detokA]
    split
    · split
      · exact detokA_acc2 f _ (_ :: acc) acc2
      · rfl
    · split
      · cases idn r with
        | none => rfl
        | some p => exact detokA_acc2 f _ (_ :: acc) acc2
      · split
        · exact detokA_acc2 f _ (_ :: acc) acc2
        · rfl

theorem detokA_acc (f : Nat) (l : List Nat) (acc out : List Tok) (h : detokA f l [] = some out) :
    detokA f l acc = some (acc.reverse ++ out) := by
  have := detokA_acc2 f l [] acc; simp only [List.nil_append] at this; rw [this, h]; rfl

/-- one fully tokenized prefix, then the rest -/
theorem detokA_app : ∀ (f g : Nat) (a b : List Nat) (acc out res : List Tok), detokA f a acc = some out →
    detokA g b out.reverse = some res → detokA (f + g) (a ++ b) acc = some res
  | f, g, [], b, acc, out, res, h, h2 => by
    simp only [detokA, Option.some.injEq] at h; subst h
    simp only [List.reverse_reverse, List.nil_append] at h2 ⊢
    rw [Nat.add_comm]; exact detokA_mono g f b acc res h2
  | 0, _, _ :: _, _, _, _, _, h, _ => by simp [detokA] at h
  | f + 1, g, t :: r, b, acc, out, res, h, h2 => by
    rw [show f + 1 + g = (f + g) + 1 by omega]
    simp only [detokA, List.cons_append] at h ⊢
    split at h
    · rw [if_pos ‹_›]; split at h
      · rename_i h8
        rw [if_pos (by simp; omega)]
        rw [List.drop_append_of_le_length h8, List.take_append_of_le_length h8]
        exact detokA_app f g _ b _ out res h h2
      · cases h
    · rw [if_neg ‹_›]; split at h
      · rw [if_pos ‹_›]
        obtain ⟨⟨n, r'⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
        rw [idn_app r b h1]; simp only [Option.bind_some]
        exact detokA_app f g _ b _ out res h h2
      · rw [if_neg ‹_›]; split at h
        · rw [if_pos ‹_›]; exact detokA_app f g _ b _ out res h h2
        · cases h

/-- `tokens` of a concatenation -/
theorem tokens_app {w1 w2 : List UInt64} {A B : List Tok} (h1 : tokens w1 = some A) (h2 : tokens w2 = some B) :
    tokens (w1 ++ w2) = some (A ++ B) := by
  unfold tokens detok at *
  have h2' := detokA_acc _ _ A.reverse B h2
  rw [List.reverse_reverse] at h2'
  have := detokA_app _ _ _ _ [] A (A ++ B) h1 h2'
  have := detokA_len _ _ _ _ this
  simpa using this

/-! ## (4) `pDefs` composes def by def -/
theorem pDefs_base (fuel : Nat) (D : List DefI) : ∀ G, pDefs fuel (G + 1) D [] = some (D, []) := by
  intro G; simp [pDefs]

theorem pDefs_step {fuel k : Nat} {D : List DefI} {ts : List Tok} {di : DefI} {da : DefA} {r : List Tok}
    {Dn : List DefI} {ds : List DefA} (h : pDef fuel D ts = some (di, da, r)) (hne : ts ≠ [])
    (h2 : ∀ G, pDefs fuel (G + k) (D ++ [di]) r = some (Dn, ds)) :
    ∀ G, pDefs fuel (G + (k + 1)) D ts = some (Dn, da :: ds) := by
  intro G
  rw [show G + (k + 1) = (G + k) + 1 by omega]
  match ts, hne with
  | t :: ts', _ =>
    simp only [pDefs, h, Option.bind_some, h2 G, Option.map_some]

/-- `refParse` from the lexed words, the tokens, the def chain and main's signature -/
theorem refParse_of {ws : List UInt64} {toks : List Tok} {Dn : List DefI} {ds : List DefA} {k : Nat}
    (ht : tokens ws = some toks) (hk : k ≤ toks.length + 1)
    (hc : ∀ G, pDefs (8 * toks.length + 8) (G + k) [] toks = some (Dn, ds))
    (hm : (Dn.getLast?.map isMain) = some true) : refParse ws = some ds := by
  unfold refParse
  rw [ht]; simp only [Option.bind_some]
  have := hc (toks.length + 1 - k)
  rw [show toks.length + 1 - k + k = toks.length + 1 by omega] at this
  rw [this]; simp only [Option.bind_some]
  cases e : Dn.getLast? with
  | none => rw [e] at hm; cases hm
  | some d => rw [e] at hm; simp only [Option.map_some, Option.some.injEq] at hm; simp [hm]

/-! ## (5) a checkable equality for the parse results -/
mutual
def ndBeq : Nd → Nd → Bool
  | .const a, .const b => a == b
  | .loc a b, .loc c d => a == c && b == d
  | .bin o a b, .bin o' a' b' => o == o' && ndBeq a a' && ndBeq b b'
  | .ite c a b t e, .ite c' a' b' t' e' => c == c' && ndBeq a a' && ndBeq b b' && ndBeq t t' && ndBeq e e'
  | .letE s w v b, .letE s' w' v' b' => s == s' && w == w' && ndBeq v v' && ndBeq b b'
  | .pair cs, .pair cs' => ndBeqL cs cs'
  | .call i as, .call i' as' => i == i' && ndBeqL as as'
  | .prim p as, .prim p' as' => p == p' && ndBeqL as as'
  | .loop z s, .loop z' s' => ndBeq z z' && ndBeq s s'
  | .cont e, .cont e' => ndBeq e e'
  | _, _ => false
def ndBeqL : List Nd → List Nd → Bool
  | [], [] => true
  | a :: as, b :: bs => ndBeq a b && ndBeqL as bs
  | _, _ => false
end

mutual
theorem ndBeq_eq : ∀ a b : Nd, ndBeq a b = true → a = b
  | .const a, .const b, h => by simp [ndBeq] at h; rw [h]
  | .loc a b, .loc c d, h => by simp [ndBeq] at h; rw [h.1, h.2]
  | .bin o a b, .bin o' a' b', h => by
    simp only [ndBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, ndBeq_eq a a' h.1.2, ndBeq_eq b b' h.2]
  | .ite c a b t e, .ite c' a' b' t' e', h => by
    simp only [ndBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1.1.1, ndBeq_eq a a' h.1.1.1.2, ndBeq_eq b b' h.1.1.2, ndBeq_eq t t' h.1.2, ndBeq_eq e e' h.2]
  | .letE s w v b, .letE s' w' v' b', h => by
    simp only [ndBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1.1, h.1.1.2, ndBeq_eq v v' h.1.2, ndBeq_eq b b' h.2]
  | .pair cs, .pair cs', h => by simp only [ndBeq] at h; rw [ndBeqL_eq cs cs' h]
  | .call i as, .call i' as', h => by
    simp only [ndBeq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, ndBeqL_eq as as' h.2]
  | .prim p as, .prim p' as', h => by
    simp only [ndBeq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, ndBeqL_eq as as' h.2]
  | .loop z s, .loop z' s', h => by
    simp only [ndBeq, Bool.and_eq_true] at h; rw [ndBeq_eq z z' h.1, ndBeq_eq s s' h.2]
  | .cont e, .cont e', h => by simp only [ndBeq] at h; rw [ndBeq_eq e e' h]
  | .const _, .loc _ _, h | .const _, .bin _ _ _, h | .const _, .ite _ _ _ _ _, h | .const _, .letE _ _ _ _, h
  | .const _, .pair _, h | .const _, .call _ _, h | .const _, .prim _ _, h | .const _, .loop _ _, h
  | .const _, .cont _, h => by simp [ndBeq] at h
  | .loc _ _, .const _, h | .loc _ _, .bin _ _ _, h | .loc _ _, .ite _ _ _ _ _, h | .loc _ _, .letE _ _ _ _, h
  | .loc _ _, .pair _, h | .loc _ _, .call _ _, h | .loc _ _, .prim _ _, h | .loc _ _, .loop _ _, h
  | .loc _ _, .cont _, h => by simp [ndBeq] at h
  | .bin _ _ _, .const _, h | .bin _ _ _, .loc _ _, h | .bin _ _ _, .ite _ _ _ _ _, h | .bin _ _ _, .letE _ _ _ _, h
  | .bin _ _ _, .pair _, h | .bin _ _ _, .call _ _, h | .bin _ _ _, .prim _ _, h | .bin _ _ _, .loop _ _, h
  | .bin _ _ _, .cont _, h => by simp [ndBeq] at h
  | .ite _ _ _ _ _, .const _, h | .ite _ _ _ _ _, .loc _ _, h | .ite _ _ _ _ _, .bin _ _ _, h
  | .ite _ _ _ _ _, .letE _ _ _ _, h | .ite _ _ _ _ _, .pair _, h | .ite _ _ _ _ _, .call _ _, h
  | .ite _ _ _ _ _, .prim _ _, h | .ite _ _ _ _ _, .loop _ _, h | .ite _ _ _ _ _, .cont _, h => by simp [ndBeq] at h
  | .letE _ _ _ _, .const _, h | .letE _ _ _ _, .loc _ _, h | .letE _ _ _ _, .bin _ _ _, h
  | .letE _ _ _ _, .ite _ _ _ _ _, h | .letE _ _ _ _, .pair _, h | .letE _ _ _ _, .call _ _, h
  | .letE _ _ _ _, .prim _ _, h | .letE _ _ _ _, .loop _ _, h | .letE _ _ _ _, .cont _, h => by simp [ndBeq] at h
  | .pair _, .const _, h | .pair _, .loc _ _, h | .pair _, .bin _ _ _, h | .pair _, .ite _ _ _ _ _, h
  | .pair _, .letE _ _ _ _, h | .pair _, .call _ _, h | .pair _, .prim _ _, h | .pair _, .loop _ _, h
  | .pair _, .cont _, h => by simp [ndBeq] at h
  | .call _ _, .const _, h | .call _ _, .loc _ _, h | .call _ _, .bin _ _ _, h | .call _ _, .ite _ _ _ _ _, h
  | .call _ _, .letE _ _ _ _, h | .call _ _, .pair _, h | .call _ _, .prim _ _, h | .call _ _, .loop _ _, h
  | .call _ _, .cont _, h => by simp [ndBeq] at h
  | .prim _ _, .const _, h | .prim _ _, .loc _ _, h | .prim _ _, .bin _ _ _, h | .prim _ _, .ite _ _ _ _ _, h
  | .prim _ _, .letE _ _ _ _, h | .prim _ _, .pair _, h | .prim _ _, .call _ _, h | .prim _ _, .loop _ _, h
  | .prim _ _, .cont _, h => by simp [ndBeq] at h
  | .loop _ _, .const _, h | .loop _ _, .loc _ _, h | .loop _ _, .bin _ _ _, h | .loop _ _, .ite _ _ _ _ _, h
  | .loop _ _, .letE _ _ _ _, h | .loop _ _, .pair _, h | .loop _ _, .call _ _, h | .loop _ _, .prim _ _, h
  | .loop _ _, .cont _, h => by simp [ndBeq] at h
  | .cont _, .const _, h | .cont _, .loc _ _, h | .cont _, .bin _ _ _, h | .cont _, .ite _ _ _ _ _, h
  | .cont _, .letE _ _ _ _, h | .cont _, .pair _, h | .cont _, .call _ _, h | .cont _, .prim _ _, h
  | .cont _, .loop _ _, h => by simp [ndBeq] at h
theorem ndBeqL_eq : ∀ a b : List Nd, ndBeqL a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [ndBeqL, Bool.and_eq_true] at h; rw [ndBeq_eq a b h.1, ndBeqL_eq as bs h.2]
  | [], _ :: _, h => by simp [ndBeqL] at h
  | _ :: _, [], h => by simp [ndBeqL] at h
end

deriving instance DecidableEq for ParSpec.DefI

def defBeq (a b : DefA) : Bool :=
  a.id == b.id && a.npw == b.npw && a.nslots == b.nslots && a.kind == b.kind && a.nres == b.nres && ndBeq a.body b.body

theorem defBeq_eq {a b : DefA} (h : defBeq a b = true) : a = b := by
  cases a; cases b
  simp only [defBeq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [h1, h2, h3, h4, h5, ndBeq_eq _ _ h6]

/-- the per-def parse check -/
def chkDef (o : Option (DefI × DefA × List Tok)) (di : DefI) (da : DefA) (r : List Tok) : Bool :=
  match o with
  | some (a, b, c) => decide (a = di) && defBeq b da && (c == r)
  | none => false

theorem chkDef_sound {o : Option (DefI × DefA × List Tok)} {di : DefI} {da : DefA} {r : List Tok}
    (h : chkDef o di da r = true) : o = some (di, da, r) := by
  match o, h with
  | some (a, b, c), h =>
    simp only [chkDef, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rw [h.1.1, defBeq_eq h.1.2, h.2]

def lsBeq : List DefA → List DefA → Bool
  | [], [] => true
  | a :: as, b :: bs => defBeq a b && lsBeq as bs
  | _, _ => false

theorem lsBeq_eq : ∀ {a b : List DefA}, lsBeq a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [lsBeq, Bool.and_eq_true] at h; rw [defBeq_eq h.1, lsBeq_eq h.2]
  | [], _ :: _, h => by simp [lsBeq] at h
  | _ :: _, [], h => by simp [lsBeq] at h

end SrcLink
