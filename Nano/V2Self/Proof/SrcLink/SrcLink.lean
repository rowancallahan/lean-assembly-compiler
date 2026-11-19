/- Nano/V2Self/Proof/SrcLink/SrcLink: generic lemmas for the kernel-checked link between C's source text and its parse
(`refParse (lex text) = some AST`), checked per def: (1) the reference lexer `lexAll` is sound for `LexSpec.Lexes`;
(2) `Lexes` composes across chunks ending in a newline; (3) `tokens` composes; (4) `pDefs` composes def by def. -/
import Nano.V2Self.Proof.Parser.ParSpec

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

theorem step_app {l m : List UInt8} {e : List UInt64} {r : List UInt8} (hl : l.getLast? = some 10)
    (h : step l = some (e, r)) : step (l ++ m) = some (e, r ++ m) ∧ (r = [] ∨ r.getLast? = some 10) := by
  match l, hl, h with
  | c :: r0, hl, h =>
    have suf : ∀ s, s <:+ (c :: r0) → s = [] ∨ s.getLast? = some 10 := fun s hs => by
      by_cases e : s = []
      · exact .inl e
      · exact .inr (by rw [last_of_suffix hs e, hl])
    simp only [step] at h ⊢
    simp only [List.cons_append]
    split at h
    · rename_i hw; rw [if_pos hw]; cases h
      exact ⟨rfl, suf _ (List.suffix_cons _ _)⟩
    · rename_i hw; rw [if_neg hw]
      have hf : opTable.find? (fun e => e.1.isPrefixOf (c :: (r0 ++ m))) =
          opTable.find? (fun e => e.1.isPrefixOf (c :: r0)) :=
        find?_congr _ (fun x hx => by
          have := isPrefixOf_app x.1 (c :: r0) m (op_no10 x hx) hl; simpa using this)
      rw [hf]
      split at h
      · rename_i s k hfd
        cases h
        have hpre : s.isPrefixOf (c :: r0) = true := by
          have := List.find?_some hfd; simpa using this
        have hle : s.length ≤ (c :: r0).length := (List.isPrefixOf_iff_prefix.1 hpre).length_le
        refine ⟨?_, suf _ (List.drop_suffix _ _)⟩
        have := List.drop_append_of_le_length (l₁ := c :: r0) (l₂ := m) hle
        simp only [List.cons_append] at this; rw [this]
      · have h10 : ∃ x ∈ c :: r0, isW x = false :=
          ⟨10, List.mem_of_getLast? hl, by decide⟩
        obtain ⟨t1, t2⟩ := takeWhile_app (p := isW) (c :: r0) m h10
        simp only [List.cons_append] at t1 t2
        rw [t1, t2]
        have sd : (c :: r0).dropWhile isW <:+ c :: r0 := List.dropWhile_suffix _
        split at h
        · split at h
          · cases h; rw [if_pos ‹_›, if_pos ‹_›]; exact ⟨rfl, suf _ sd⟩
          · cases h
        · split at h
          · cases h; rw [if_neg ‹_›, if_pos ‹_›]; exact ⟨rfl, suf _ sd⟩
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
