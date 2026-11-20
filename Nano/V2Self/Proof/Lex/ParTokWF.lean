/- Nano/V2Self/Proof/Lex/ParTokWF: `TokWF ts`, the token-buffer well-formedness hypothesis of `ParserSound` (parser lead; D derives it
from the lexer spec).  List-level mirror of box C's heap relation `ParInv.TokAt`: keyword words (okTag, ≠ 5, ≠ 14), numerals
`5, b₀..b₇` with byte words < 256, identifiers `14, (1, c)*, 0` with at least one character. -/
import Nano.V2Self.Proof.Parser.ParSpec
namespace ParSpec

theorem flat2_len' : ∀ nm : List UInt64, (nm.flatMap (fun c => [1, c])).length = 2 * nm.length
  | [] => rfl
  | c :: t => by rw [List.flatMap_cons, List.length_append, flat2_len' t]; simp; omega

inductive TokL : List UInt64 → List Tok → Prop
  | nil : TokL [] []
  | kw {r : List UInt64} {toks : List Tok} (t : UInt64) : t ≠ 5 → t ≠ 14 → okTag t.toNat = true → TokL r toks →
      TokL (t :: r) (.k t.toNat :: toks)
  | num {r : List UInt64} {toks : List Tok} (bs : List UInt64) : bs.length = 8 → (∀ b ∈ bs, b.toNat < 256) → TokL r toks →
      TokL (5 :: bs ++ r) (.num (bytesVal (bs.map UInt64.toNat)) :: toks)
  | id {r : List UInt64} {toks : List Tok} (nm : List UInt64) : nm ≠ [] → TokL r toks →
      TokL (14 :: nm.flatMap (fun c => [1, c]) ++ 0 :: r) (.id (nm.map UInt64.toNat) :: toks)

/-- the token buffer decodes (as `TokL`) to some token list -/
def TokWF (ts : List UInt64) : Prop := ∃ toks, TokL ts toks


theorem idn_flat (r : List Nat) : ∀ nm : List UInt64,
    idn ((nm.flatMap (fun c => [1, c])).map UInt64.toNat ++ 0 :: r) = some (nm.map UInt64.toNat, r)
  | [] => rfl
  | c :: t => by simp [idn, idn_flat r t]

theorem toNat_ne {t : UInt64} {n : Nat} (hn : n < 2 ^ 64) (h : t ≠ n.toUInt64) : t.toNat ≠ n := by
  intro e; apply h; apply UInt64.toNat_inj.mp; simp; omega

theorem detokA_of {r : List UInt64} {toks : List Tok} (ht : TokL r toks) :
    ∀ f acc, r.length ≤ f → detokA f (r.map UInt64.toNat) acc = some (acc.reverse ++ toks) := by
  induction ht with
  | nil => intro f acc _; cases f <;> simp [detokA]
  | @kw r toks t h5 h14 hok _ ih =>
    intro f acc hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have a5 : t.toNat ≠ 5 := toNat_ne (by decide) h5
    have a14 : t.toNat ≠ 14 := toNat_ne (by decide) h14
    simp only [List.map_cons, detokA, a5, a14, hok, if_false, if_true]
    rw [ih f _ (by simp at hf; omega)]; simp
  | @num r toks bs h8 _ _ ih =>
    intro f acc hf
    simp only [List.length_cons, List.length_append, h8] at hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have e1 : (bs.map UInt64.toNat ++ r.map UInt64.toNat).drop 8 = r.map UInt64.toNat := List.drop_left' (by simp [h8])
    have e2 : (bs.map UInt64.toNat ++ r.map UInt64.toNat).take 8 = bs.map UInt64.toNat := List.take_left' (by simp [h8])
    simp only [List.map_cons, List.map_append, List.cons_append, detokA, show ((5 : UInt64).toNat = 5) from rfl, if_true, List.length_append,
      List.length_map, h8, show 8 ≤ 8 + r.length by omega, e1, e2]
    rw [ih f _ (by omega)]; simp
  | @id r toks nm _ _ ih =>
    intro f acc hf
    simp only [List.length_cons, List.length_append, flat2_len'] at hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [List.map_cons, List.map_append, List.cons_append, detokA, show ((14 : UInt64).toNat = 14) from rfl, show ((0 : UInt64).toNat = 0) from rfl,
      if_true, show ¬ (14 = 5) by decide, if_false, idn_flat, Option.bind_some]
    rw [ih f _ (by omega)]; simp

/-- the token buffer's `TokL` decoding is ParSpec's `tokens` -/
theorem tokens_of {ts : List UInt64} {toks : List Tok} (ht : TokL ts toks) : tokens ts = some toks := by
  have := detokA_of ht (ts.length + 1) [] (by omega)
  simpa [tokens, detok] using this

end ParSpec
