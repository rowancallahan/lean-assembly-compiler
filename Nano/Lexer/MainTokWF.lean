/- Nano/Lexer/MainTokWF: the lexer spec's output is a well-formed token buffer (`ParSpec.TokWF`, the hypothesis of
the parser lead's `ParserSound`), up to the scope markers: `Lexes x ts → TokLM ts`. -/
import Nano.Lexer.ParTokWF
import Nano.Lexer.Lex2Spec

namespace NanoMain
open ParSpec

theorem op_tags : ∀ e ∈ LexSpec.opTable, e.2 ≠ 5 ∧ e.2 ≠ 14 ∧ okTag e.2.toNat = true := by decide
theorem kw_tags : ∀ e ∈ LexSpec.kwTable, e.2 ≠ 5 ∧ e.2 ≠ 14 ∧ okTag e.2.toNat = true := by decide

theorem le8_spec (n : Nat) : (LexSpec.le8 n).length = 8 ∧ ∀ b ∈ LexSpec.le8 n, b.toNat < 256 := by
  refine ⟨by simp [LexSpec.le8], fun b hb => ?_⟩
  simp only [LexSpec.le8, List.mem_map, List.mem_range] at hb
  obtain ⟨i, -, rfl⟩ := hb
  have : n / 256 ^ i % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : n / 256 ^ i % 256 < 2 ^ 64)]; omega

theorem lookup_mem {α β : Type} [BEq α] : ∀ (l : List (α × β)) (a : α) (b : β), l.lookup a = some b → ∃ a', (a', b) ∈ l
  | [], _, _, h => by simp at h
  | (x, y) :: r, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · cases h; exact ⟨x, by simp⟩
    · obtain ⟨a', h'⟩ := lookup_mem r a b h; exact ⟨a', List.mem_cons_of_mem _ h'⟩

/-- token words with the lexer's scope markers (`LexSpec.scopeTok`) between whole tokens: what `Lexes` produces;
`DsSpec.frame` removes the markers (`DsSpec.frame_tokWF`) -/
inductive TokLM : List UInt64 → Prop
  | nil : TokLM []
  | kw {r : List UInt64} (t : UInt64) : t ≠ 5 → t ≠ 14 → okTag t.toNat = true → TokLM r → TokLM (t :: r)
  | num {r : List UInt64} (bs : List UInt64) : bs.length = 8 → (∀ b ∈ bs, b.toNat < 256) → TokLM r → TokLM (5 :: bs ++ r)
  | id {r : List UInt64} (nm : List UInt64) : nm ≠ [] → TokLM r → TokLM (14 :: nm.flatMap (fun c => [1, c]) ++ 0 :: r)
  | sc {r : List UInt64} (o : Bool) (n : List UInt8) : TokLM r → TokLM (LexSpec.scopeTok o n ++ r)

theorem step_tok {l : List UInt8} {e : List UInt64} {r : List UInt8} (h : LexSpec.step l = some (e, r))
    {t : List UInt64} (ht : TokLM t) : TokLM (e ++ t) := by
  match l, h with
  | c :: rr, h =>
    simp only [LexSpec.step] at h
    split at h
    · cases h; exact ht
    split at h
    · cases h; exact ht
    split at h
    · obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 h
      have : e = [] := by split at he <;> simp_all
      subst this; exact ht
    split at h
    · obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 h
      have : e = [] := by split at he <;> simp_all
      subst this; exact ht
    split at h
    · rename_i s k hf
      cases h
      obtain ⟨a, b, c'⟩ := op_tags _ (List.mem_of_find?_eq_some hf)
      exact .kw k a b c' ht
    · split at h
      · split at h
        · cases h
          obtain ⟨l8, lb⟩ := le8_spec (LexSpec.numVal ((c :: rr).takeWhile LexSpec.isW))
          exact .num _ l8 lb ht
        · cases h
      · split at h
        · rename_i hw
          split at h
          · cases h
          split at h
          · obtain ⟨⟨n, e'⟩, -, he⟩ := Option.map_eq_some_iff.1 h
            cases he; exact .sc _ n ht
          split at h
          · split at h
            · cases h; exact ht
            · cases h
          cases h
          split
          · rename_i k hk
            obtain ⟨a', hm⟩ := lookup_mem _ _ _ hk
            obtain ⟨a, b, c'⟩ := kw_tags _ hm
            exact .kw k a b c' ht
          · have hne : ((c :: rr).takeWhile LexSpec.isW).map UInt8.toUInt64 ≠ [] := by simp [hw]
            have := TokLM.id (((c :: rr).takeWhile LexSpec.isW).map UInt8.toUInt64) hne ht
            simpa [List.flatMap_map, List.append_assoc] using this
        · cases h

theorem lexes_tokWF {x : List UInt8} {ts : List UInt64} (h : LexSpec.Lexes x ts) : TokLM ts := by
  induction h with
  | nil => exact .nil
  | cons hs _ ih => exact step_tok hs ih

theorem sc_head (o : Bool) (n : List UInt8) (r : List UInt64) :
    ∃ k r', LexSpec.scopeTok o n ++ r = k :: r' ∧ k ≠ 5 ∧ k ≠ 14 ∧ okTag k.toNat = false := by
  unfold LexSpec.scopeTok
  split <;> cases o <;> exact ⟨_, _, rfl, by decide, by decide, by decide⟩

/-- marker-free token words: a `TokLM` buffer that ParSpec's `tokens` decodes is a `TokL` buffer -/
theorem tokLM_tokL {ts : List UInt64} (ht : TokLM ts) :
    ∀ f acc res, ts.length ≤ f → detokA f (ts.map UInt64.toNat) acc = some res → ∃ toks, TokL ts toks := by
  induction ht with
  | nil => intro _ _ _ _ _; exact ⟨[], .nil⟩
  | @kw r t h5 h14 hok _ ih =>
    intro f acc res hf h
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have a5 : t.toNat ≠ 5 := toNat_ne (by decide) h5
    have a14 : t.toNat ≠ 14 := toNat_ne (by decide) h14
    simp only [List.map_cons, detokA, a5, a14, hok, if_false, if_true] at h
    obtain ⟨toks, h'⟩ := ih f _ _ (by simp at hf; omega) h
    exact ⟨_, .kw t h5 h14 hok h'⟩
  | @num r bs h8 hb _ ih =>
    intro f acc res hf h
    simp only [List.length_cons, List.length_append, h8] at hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have e1 : (bs.map UInt64.toNat ++ r.map UInt64.toNat).drop 8 = r.map UInt64.toNat := List.drop_left' (by simp [h8])
    simp only [List.map_cons, List.map_append, List.cons_append, detokA, show ((5 : UInt64).toNat = 5) from rfl, if_true,
      List.length_append, List.length_map, h8, show 8 ≤ 8 + r.length by omega, e1] at h
    obtain ⟨toks, h'⟩ := ih f _ _ (by omega) h
    exact ⟨_, .num bs h8 hb h'⟩
  | @id r nm hne _ ih =>
    intro f acc res hf h
    simp only [List.length_cons, List.length_append, flat2_len'] at hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [List.map_cons, List.map_append, List.cons_append, detokA, show ((14 : UInt64).toNat = 14) from rfl,
      show ((0 : UInt64).toNat = 0) from rfl, if_true, show ¬ (14 = 5) by decide, if_false, idn_flat, Option.bind_some] at h
    obtain ⟨toks, h'⟩ := ih f _ _ (by omega) h
    exact ⟨_, .id nm hne h'⟩
  | @sc r o n _ _ =>
    intro f acc res hf h
    obtain ⟨k, r', he, h5, h14, hok⟩ := sc_head o n r
    rw [he] at h hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have a5 : k.toNat ≠ 5 := toNat_ne (by decide) h5
    have a14 : k.toNat ≠ 14 := toNat_ne (by decide) h14
    simp [detokA, a5, a14, hok] at h

theorem tokL_of_tokens {ts : List UInt64} {toks : List Tok} (ht : TokLM ts) (h : tokens ts = some toks) : TokL ts toks := by
  obtain ⟨toks', h'⟩ := tokLM_tokL ht (ts.length + 1) [] toks (by omega) (by simpa [tokens, detok] using h)
  have := tokens_of h'; rw [h] at this; cases this; exact h'

end NanoMain
