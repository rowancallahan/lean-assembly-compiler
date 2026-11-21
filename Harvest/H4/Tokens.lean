/- Harvest/H4/Tokens: longest-match token tables for FUTURE syntax (`=>` already used, `fun`, `←`, `<-`, `|>.`, `<|`, `|>`,
`<|>`, `∘`, `::`, `++`, `⟨`, `⟩`, `#[`, `]`), as a nano-style longest-first table, and the identifier-versus-token rule.
Lean's side: the tokenizer picks the LONGEST token in the token table that is a prefix of the input
(`Lean.Data.Trie.matchPrefix`, Lean/Data/Trie.lean:168-193: doc "Find the longest key"; `partial`, so not kernel-reducible);
an identifier that is also a token is the token iff the token is at least as long (`isToken`, Parser/Basic.lean:934-941,
`private`, restated below).  What is proved here is the nano side: a longest-FIRST table with `find?` returns the longest
matching entry (generic lemma, then the concrete table by kernel evaluation).  Standalone (Init only). -/
namespace H4.Tok

def bytes (s : String) : List UInt8 := s.toUTF8.toList

/-- spellings of the future tokens (the Lean token, trimmed); `fun` and `←`/`<-` are two spellings of one token each -/
def futureToks : List String :=
  ["|>.", "<|>", "<-", "←", "=>", "|>", "<|", "::", "++", "∘", "⟨", "⟩", "#[", "]", "fun", "λ"]

/-- the table nano would search: longest (in bytes) first -/
def tab : List (List UInt8) :=
  ["|>.", "<|>", "←", "∘", "⟨", "⟩", "fun", "<-", "=>", "|>", "<|", "::", "++", "#[", "λ", "]"].map bytes

/-- the first prefix match of a longest-first table is the longest match -/
theorem find_longest (t : List (List UInt8)) (l : List UInt8) (h : t.Pairwise (fun a b => b.length ≤ a.length))
    (s : List UInt8) (hs : t.find? (fun e => e.isPrefixOf l) = some s) :
    ∀ e ∈ t, e.isPrefixOf l = true → e.length ≤ s.length := by
  induction t with
  | nil => simp at hs
  | cons a r ih =>
    rw [List.pairwise_cons] at h
    intro e he hp
    by_cases ha : a.isPrefixOf l = true
    · simp only [List.find?_cons, ha] at hs
      cases hs
      rcases List.mem_cons.1 he with rfl | he
      · exact Nat.le_refl _
      · exact h.1 e he
    · have ha' : a.isPrefixOf l = false := Bool.eq_false_iff.2 ha
      simp only [List.find?_cons, ha'] at hs
      rcases List.mem_cons.1 he with rfl | he
      · exact absurd hp ha
      · exact ih h.2 hs e he hp

theorem tab_sorted : tab.Pairwise (fun a b => b.length ≤ a.length) := by decide +kernel

/-- **concrete**: on every input, nano's choice among the future tokens is a longest match -/
theorem tab_munch (l : List UInt8) (s : List UInt8) (hs : tab.find? (fun e => e.isPrefixOf l) = some s) :
    ∀ e ∈ tab, e.isPrefixOf l = true → e.length ≤ s.length :=
  find_longest tab l tab_sorted s hs

/-- the dangerous pairs, where one token is a proper prefix of another: `|>` of `|>.`, `<|` of `<|>`, `<` of `<-`...
Longest-first resolves them; examples by evaluation -/
theorem munch_examples :
    tab.find? (fun e => e.isPrefixOf (bytes "|>.foo")) = some (bytes "|>.") ∧
    tab.find? (fun e => e.isPrefixOf (bytes "|> f")) = some (bytes "|>") ∧
    tab.find? (fun e => e.isPrefixOf (bytes "<|> g")) = some (bytes "<|>") ∧
    tab.find? (fun e => e.isPrefixOf (bytes "<| g")) = some (bytes "<|") ∧
    tab.find? (fun e => e.isPrefixOf (bytes "<-x")) = some (bytes "<-") ∧
    tab.find? (fun e => e.isPrefixOf (bytes "#[1]")) = some (bytes "#[") ∧
    tab.find? (fun e => e.isPrefixOf (bytes "=>x")) = some (bytes "=>") := by decide +kernel

/-- the pairs (token, longer token it prefixes): where one entry shadows another and order matters -/
def prefixPairs : List (String × String) :=
  futureToks.flatMap fun a => futureToks.filterMap fun b =>
    if a ≠ b && (bytes a).isPrefixOf (bytes b) then some (a, b) else none

theorem prefixPairs_eq : prefixPairs = [("|>", "|>."), ("<|", "<|>")] := by decide +kernel

/-- Lean's `isToken` (Parser/Basic.lean:934-941, `private`, restated): an identifier occupying `idLen` bytes is the token
`tk` when the token is at least that long -/
def isTokenL (idLen : Nat) (tk : Option Nat) : Bool :=
  match tk with
  | none => false
  | some n => n ≥ idLen

/-- `fun`, the word itself, is a token; `fun1`, `fun'` read as longer identifiers (the token matched is still `fun`, length 3) -/
theorem fun_is_token : isTokenL 3 (some 3) = true ∧ isTokenL 4 (some 3) = false := by decide

end H4.Tok
