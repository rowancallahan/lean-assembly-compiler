/- Nano/Lexer/MainTokWF: the lexer spec's output is a well-formed token buffer (`ParSpec.TokWF`, the hypothesis of
the parser lead's `ParserSound`): `Lexes x ts → TokWF ts`. -/
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

theorem step_tok {l : List UInt8} {e : List UInt64} {r : List UInt8} (h : LexSpec.step l = some (e, r))
    {t : List UInt64} {toks : List Tok} (ht : TokL t toks) : ∃ toks', TokL (e ++ t) toks' := by
  match l, h with
  | c :: rr, h =>
    simp only [LexSpec.step] at h
    split at h
    · cases h; exact ⟨_, ht⟩
    split at h
    · cases h; exact ⟨_, ht⟩
    split at h
    · obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 h
      have : e = [] := by split at he <;> simp_all
      subst this; exact ⟨_, ht⟩
    split at h
    · obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 h
      have : e = [] := by split at he <;> simp_all
      subst this; exact ⟨_, ht⟩
    split at h
    · rename_i s k hf
      cases h
      obtain ⟨a, b, c'⟩ := op_tags _ (List.mem_of_find?_eq_some hf)
      exact ⟨_, .kw k a b c' ht⟩
    · split at h
      · split at h
        · cases h
          obtain ⟨l8, lb⟩ := le8_spec (LexSpec.numVal ((c :: rr).takeWhile LexSpec.isW))
          exact ⟨_, .num _ l8 lb ht⟩
        · cases h
      · split at h
        · rename_i hw
          split at h
          · split at h
            · cases h; exact ⟨_, ht⟩
            · cases h
          split at h
          · split at h
            · cases h; exact ⟨_, ht⟩
            · cases h
          cases h
          split
          · rename_i k hk
            obtain ⟨a', hm⟩ := lookup_mem _ _ _ hk
            obtain ⟨a, b, c'⟩ := kw_tags _ hm
            exact ⟨_, .kw k a b c' ht⟩
          · have hne : ((c :: rr).takeWhile LexSpec.isW).map UInt8.toUInt64 ≠ [] := by simp [hw]
            have := TokL.id (((c :: rr).takeWhile LexSpec.isW).map UInt8.toUInt64) hne ht
            exact ⟨Tok.id ((((c :: rr).takeWhile LexSpec.isW).map UInt8.toUInt64).map UInt64.toNat) :: toks,
              by simpa [List.flatMap_map, List.append_assoc] using this⟩
        · cases h

theorem lexes_tokWF {x : List UInt8} {ts : List UInt64} (h : LexSpec.Lexes x ts) : TokWF ts := by
  induction h with
  | nil => exact ⟨[], .nil⟩
  | cons hs _ ih => obtain ⟨toks, ht⟩ := ih; exact step_tok hs ht

end NanoMain
