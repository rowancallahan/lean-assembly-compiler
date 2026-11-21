/- Nano/Lexer/DsTok: the desugared words are a well-formed token buffer (`TokWF`, the parser's hypothesis),
and a token buffer without the identifier `match` desugars to itself. -/
import Nano.Lexer.DsSound
import Nano.Lexer.MainTokWF
namespace DsSpec
open ParSpec

/-- a piece of words that is a sequence of whole tokens -/
def Frag (a : List UInt64) : Prop := ∀ r toks, TokL r toks → ∃ toks', TokL (a ++ r) toks'

theorem frag_nil : Frag [] := fun _ toks h => ⟨toks, h⟩
theorem frag_app {a b : List UInt64} (ha : Frag a) (hb : Frag b) : Frag (a ++ b) := fun r toks h => by
  obtain ⟨t1, h1⟩ := hb r toks h
  obtain ⟨t2, h2⟩ := ha _ t1 h1
  exact ⟨t2, by simpa [List.append_assoc] using h2⟩
theorem frag_kw (k : UInt64) (h5 : k ≠ 5) (h14 : k ≠ 14) (hok : okTag k.toNat = true) : Frag [k] :=
  fun _ toks h => ⟨_, TokL.kw k h5 h14 hok h⟩
theorem frag_MU : Frag MU := fun r toks h => by
  have := TokL.id [36] (by simp) h
  exact ⟨_, by simpa [MU] using this⟩

theorem frag_kws : ∀ (l : List UInt64), (∀ k ∈ l, k ≠ 5 ∧ k ≠ 14 ∧ okTag k.toNat = true) → Frag l
  | [], _ => frag_nil
  | k :: l, h => by
    have := frag_app (frag_kw k (h k (by simp)).1 (h k (by simp)).2.1 (h k (by simp)).2.2)
      (frag_kws l (fun k' hk => h k' (by simp [hk])))
    simpa using this

/-- the first token of a well-formed buffer is a whole token, and the rest is well formed -/
theorem split_frag {ts : List UInt64} {toks : List Tok} (ht : TokL ts toks) {a r : List UInt64}
    (h : splitTok ts = some (a, r)) : Frag a ∧ ∃ toks', TokL r toks' := by
  have e := splitTok_app h
  cases ht with
  | nil => simp [splitTok] at h
  | @kw r0 toks0 k h5 h14 hok h0 =>
    simp only [splitTok, h5, h14, if_false, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨frag_kw k h5 h14 hok, _, h0⟩
  | @num r0 toks0 bs h8 hb h0 =>
    simp only [List.cons_append, splitTok, if_true, List.length_append, h8] at h
    rw [if_pos (by omega)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have e1 : (bs ++ r0).take 8 = bs := List.take_left' h8
    have e2 : (bs ++ r0).drop 8 = r0 := List.drop_left' h8
    rw [e1, e2]
    exact ⟨fun r toks hr => ⟨_, by simpa using TokL.num bs h8 hb hr⟩, _, h0⟩
  | @id r0 toks0 nm hne h0 =>
    have hi : ∀ (m : List UInt64) (r' : List UInt64), identTok (m.flatMap (fun c => [1, c]) ++ 0 :: r') =
        some (m.flatMap (fun c => [1, c]) ++ [0], r') := by
      intro m r'; induction m with
      | nil => simp [identTok]
      | cons c m ih => simp [identTok, ih]
    simp only [List.cons_append, splitTok, show ¬ ((14 : UInt64) = 5) by decide, if_false, if_true, List.append_eq, hi,
      Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun r toks hr => ⟨_, by simpa using TokL.id nm hne hr⟩, _, h0⟩

end DsSpec

namespace DsSpec
open ParSpec

theorem tokL_tail {k : UInt64} {r : List UInt64} {toks : List Tok} (h : TokL (k :: r) toks) (h5 : k ≠ 5) (h14 : k ≠ 14) :
    ∃ toks', TokL r toks' := by
  cases h with
  | kw _ _ _ _ h0 => exact ⟨_, h0⟩
  | num => exact absurd rfl h5
  | id => exact absurd rfl h14

theorem kws_ok : ∀ k ∈ ([1, 2, 6, 7, 9, 13, 15, 18, 19, 23, 32, 33, 34] : List UInt64), k ≠ 5 ∧ k ≠ 14 ∧ okTag k.toNat = true := by
  decide

theorem fk (l : List UInt64) (h : ∀ k ∈ l, k ∈ ([1, 2, 6, 7, 9, 13, 15, 18, 19, 23, 32, 33, 34] : List UInt64)) : Frag l :=
  frag_kws l (fun k hk => kws_ok k (h k hk))

theorem fpre (b : Bool) : Frag (if b then [] else [34]) := by
  split
  · exact frag_nil
  · exact fk _ (by decide)

theorem pat_frag {r1 r2 w : List UInt64} {p : Pat} {b c : Bool} {toks : List Tok} (ht : TokL r1 toks)
    (hp : pat r1 = some (p, r2)) (ha : armCode b p = some (w, c)) : Frag w ∧ ∃ toks', TokL r2 toks' := by
  unfold pat at hp
  obtain ⟨⟨a, r⟩, hs, hp⟩ := Option.bind_eq_some_iff.1 hp
  simp only at hp
  obtain ⟨fa, tr, hr⟩ := split_frag ht hs
  have one : ∀ (r' : List UInt64), r = 19 :: r' → ∃ toks', TokL r' toks' := by
    intro r' e; subst e; exact tokL_tail hr (by decide) (by decide)
  by_cases c5 : a.head? = some 5
  · rw [if_pos c5] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      simp only [armCode, Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
      refine ⟨?_, one _ rfl⟩
      exact frag_app (frag_app (frag_app (frag_app (frag_app (fpre b) (fk [32] (by decide))) frag_MU) (fk [23] (by decide))) fa)
        (fk [33] (by decide))
    · cases hp
  rw [if_neg c5] at hp
  by_cases cw : a = WILD
  · rw [if_pos cw] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      simp only [armCode, Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
      exact ⟨fpre b, one _ rfl⟩
    · cases hp
  rw [if_neg cw] at hp
  by_cases c14 : a.head? = some 14
  · rw [if_pos c14] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      simp only [armCode, Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
      refine ⟨?_, one _ rfl⟩
      exact frag_app (frag_app (frag_app (frag_app (frag_app (fpre b) (fk [2] (by decide))) fa) (fk [9] (by decide))) frag_MU)
        (fk [13] (by decide))
    · cases hp
  rw [if_neg c14] at hp
  by_cases c6 : a = [6]
  · rw [if_pos c6] at hp
    obtain ⟨⟨x, r1'⟩, hx, hp⟩ := Option.bind_eq_some_iff.1 hp
    simp only at hp
    obtain ⟨fx, tx, hrx⟩ := split_frag hr hx
    split at hp
    · split at hp
      · obtain ⟨t2, hr2⟩ := tokL_tail hrx (by decide) (by decide)
        obtain ⟨⟨y, r3⟩, hy, hp⟩ := Option.bind_eq_some_iff.1 hp
        simp only at hp
        obtain ⟨fy, ty, hry⟩ := split_frag hr2 hy
        split at hp
        · split at hp
          · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
            obtain ⟨t3, hr3⟩ := tokL_tail hry (by decide) (by decide)
            obtain ⟨t4, hr4⟩ := tokL_tail hr3 (by decide) (by decide)
            cases b
            · simp [armCode] at ha
            · simp only [armCode, if_true, Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha
              refine ⟨?_, _, hr4⟩
              exact frag_app (frag_app (frag_app (frag_app (frag_app (frag_app (fk [2, 6] (by decide)) fx)
                (fk [15] (by decide))) fy) (fk [7, 9] (by decide))) frag_MU) (fk [13] (by decide))
          · cases hp
        · cases hp
      · cases hp
    · cases hp
  · rw [if_neg c6] at hp; cases hp

/-- the code `go` emits is a well-formed token buffer -/
theorem go_tok : ∀ (f : Nat) (ts : List UInt64) (cs : List Nat) (sc : Bool) (out : List UInt64) (toks : List Tok),
    TokL ts toks → go f ts cs sc = some out → ∃ toks', TokL out toks'
  | 0, _, _, _, _, _, _, h => by simp [go] at h
  | f + 1, [], cs, sc, out, _, _, h => by
    simp only [go] at h; split at h
    · cases h; exact ⟨[], .nil⟩
    · cases h
  | f + 1, x :: xs, cs, sc, out, toks, ht, h => by
    simp only [go] at h
    obtain ⟨⟨a, r⟩, hs, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    obtain ⟨fa, tr, hr⟩ := split_frag ht hs
    have step : ∀ (pre : List UInt64) (cs' : List Nat) (sc' : Bool) (o' : List UInt64), go f r cs' sc' = some o' →
        Frag pre → ∃ toks', TokL (pre ++ o') toks' := by
      intro pre cs' sc' o' h1 h2
      obtain ⟨t1, h3⟩ := go_tok f r cs' sc' o' tr hr h1
      exact h2 _ _ h3
    have arm : ∀ (pre r1 : List UInt64) (p : Pat) (r2 w : List UInt64) (bb c' : Bool) (cs' : List Nat) (o' : List UInt64)
        (toks1 : List Tok), TokL r1 toks1 → pat r1 = some (p, r2) → armCode bb p = some (w, c') → go f r2 cs' false = some o' →
        Frag pre → ∃ toks', TokL (pre ++ w ++ o') toks' := by
      intro pre r1 p r2 w bb c' cs' o' toks1 h0 h1 h2 h3 h4
      obtain ⟨fw, t2, hr2⟩ := pat_frag h0 h1 h2
      obtain ⟨t3, h5⟩ := go_tok f r2 cs' false o' t2 hr2 h3
      exact frag_app h4 fw _ _ h5
    split at h
    · split at h
      · split at h
        · rename_i r1 _
          obtain ⟨⟨p, r2⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨⟨w, c'⟩, h2, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨o', h3, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨t1, hr1⟩ := tokL_tail hr (by decide) (by decide)
          have := arm [13] _ p r2 w true c' _ o' _ hr1 h1 h2 h3 (fk [13] (by decide))
          simpa using this
        · cases h
      · split at h
        · cases h
        · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          exact step a cs true o' h1 fa
    · split at h
      · split at h
        · cases h
        · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          have := step ([2] ++ MU ++ [9]) cs true o' h1 (frag_app (frag_app (fk [2] (by decide)) frag_MU) (fk [9] (by decide)))
          simpa using this
      · split at h
        · cases h
        · split at h
          · split at h
            · obtain ⟨⟨p, r2⟩, h1, h⟩ := Option.bind_eq_some_iff.1 h
              obtain ⟨⟨w, c'⟩, h2, h⟩ := Option.bind_eq_some_iff.1 h
              obtain ⟨o', h3, rfl⟩ := Option.map_eq_some_iff.1 h
              have := arm [] r p r2 w false c' _ o' _ hr h1 h2 h3 frag_nil
              simpa using this
            · split at h
              · cases h
              · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
                have := step [18] cs false o' h1 (fk [18] (by decide))
                simpa using this
          · split at h
            · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
              have := step [6] _ false o' h1 (fk [6] (by decide))
              simpa using this
            · split at h
              · split at h
                · cases h
                · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
                  have := step [7] _ false o' h1 (fk [7] (by decide))
                  simpa using this
              · split at h
                · split at h
                  · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
                    have := step [1] _ false o' h1 (fk [1] (by decide))
                    simpa using this
                  · cases h
                · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
                  exact step a cs false o' h1 fa

theorem ds0_tokWF {ts ts' : List UInt64} (ht : TokWF ts) (h : ds0 ts = some ts') : TokWF ts' ∧ ts'.length < 2 ^ 24 := by
  obtain ⟨toks, ht⟩ := ht
  unfold ds0 at h
  split at h
  · split at h
    · cases h; exact ⟨⟨toks, ht⟩, by omega⟩
    · split at h
      · cases h
      obtain ⟨o, h1, h2⟩ := Option.bind_eq_some_iff.1 h
      split at h2
      · cases h2; exact ⟨go_tok _ _ _ _ _ _ ht h1, by omega⟩
      · cases h2
  · cases h

theorem identTok_flat (m r : List UInt64) :
    identTok (m.flatMap (fun c => [1, c]) ++ 0 :: r) = some (m.flatMap (fun c => [1, c]) ++ [0], r) := by
  induction m with
  | nil => simp [identTok]
  | cons c m ih => simp [identTok, ih]

theorem okTag_le (k : UInt64) (h : okTag k.toNat = true) : k.toNat ≤ 47 := by
  unfold okTag at h; simp at h; omega

theorem split_sc (n : List UInt8) (r : List UInt64) :
    splitTok (14 :: ((n.flatMap fun b => [1, b.toUInt64]) ++ [0] ++ r)) =
      some (14 :: (n.flatMap fun b => [1, b.toUInt64]) ++ [0], r) := by
  have e : (n.flatMap fun b => [1, b.toUInt64]) = (n.map UInt8.toUInt64).flatMap (fun c => [1, c]) := by
    simp [List.flatMap_map]
  rw [e]
  simp only [List.append_assoc, List.singleton_append, splitTok, show ¬ ((14 : UInt64) = 5) by decide,
    if_false, if_true, identTok_flat, Option.map_some, List.cons_append, List.nil_append]

/-- the scope frame removes the scope markers: its output is a token buffer -/
theorem frame_tokWF {ts : List UInt64} (ht : NanoMain.TokLM ts) : ∀ f ph st b, frame f ts ph st = some b → TokWF b := by
  induction ht with
  | nil =>
    intro f ph st b h
    cases f with
    | zero => simp [frame] at h
    | succ f => simp [frame] at h; subst h; exact ⟨[], .nil⟩
  | @kw r k h5 h14 hok _ ih =>
    intro f ph st b h
    cases f with
    | zero => simp [frame] at h
    | succ f =>
      have hk := okTag_le k hok
      have n : k ≠ 48 ∧ k ≠ 49 ∧ k ≠ 50 ∧ k ≠ 51 := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro e; subst e; simp at hk)
      simp only [frame, n.1, n.2.1, n.2.2.1, n.2.2.2, if_false] at h
      split at h
      · cases h
      simp only [splitTok, h5, h14, if_false] at h
      obtain ⟨b', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨toks, ht'⟩ := ih f 1 st b' h1
      exact ⟨_, .kw k h5 h14 hok ht'⟩
  | @num r bs h8 hb _ ih =>
    intro f ph st b h
    cases f with
    | zero => simp [frame] at h
    | succ f =>
      simp only [List.cons_append, frame, show ¬ ((5 : UInt64) = 48) by decide, show ¬ ((5 : UInt64) = 49) by decide,
        show ¬ ((5 : UInt64) = 50) by decide, show ¬ ((5 : UInt64) = 51) by decide, if_false] at h
      split at h
      · cases h
      simp only [splitTok, if_true, List.length_append, h8] at h
      rw [if_pos (by omega)] at h
      have e1 : (bs ++ r).take 8 = bs := List.take_left' h8
      have e2 : (bs ++ r).drop 8 = r := List.drop_left' h8
      simp only [e1, e2] at h
      obtain ⟨b', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨toks, ht'⟩ := ih f 1 st b' h1
      exact ⟨_, by simpa using TokL.num bs h8 hb ht'⟩
  | @id r nm hne _ ih =>
    intro f ph st b h
    cases f with
    | zero => simp [frame] at h
    | succ f =>
      simp only [List.cons_append, frame, show ¬ ((14 : UInt64) = 48) by decide, show ¬ ((14 : UInt64) = 49) by decide,
        show ¬ ((14 : UInt64) = 50) by decide, show ¬ ((14 : UInt64) = 51) by decide, if_false] at h
      split at h
      · cases h
      simp only [splitTok, show ¬ ((14 : UInt64) = 5) by decide, if_false, if_true, List.append_eq, identTok_flat,
        Option.map_some] at h
      obtain ⟨b', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨toks, ht'⟩ := ih f 1 st b' h1
      exact ⟨_, by simpa using TokL.id nm hne ht'⟩
  | @sc r o n _ ih =>
    intro f ph st b h
    cases f with
    | zero => simp [frame] at h
    | succ f =>
      unfold LexSpec.scopeTok at h
      split at h
      · cases o
        · simp (config := {decide := true}) only [Bool.false_eq_true, if_false, if_true, List.singleton_append, frame] at h
          split at h
          · exact ih _ _ _ _ h
          · cases h
        · simp (config := {decide := true}) only [if_false, if_true, List.singleton_append, frame] at h
          split at h
          · exact ih _ _ _ _ h
          · cases h
      · cases o
        · simp (config := {decide := true}) only [Bool.false_eq_true, if_false, if_true, List.cons_append, frame,
            split_sc] at h
          split at h
          · exact ih _ _ _ _ h
          · cases h
        · simp (config := {decide := true}) only [if_false, if_true, List.cons_append, frame] at h
          split at h
          · simp only [split_sc] at h; exact ih _ _ _ _ h
          · cases h

/-- **the desugared words are well formed** -/
theorem ds_tokWF {ts ts' : List UInt64} (ht : NanoMain.TokLM ts) (h : ds ts = some ts') :
    TokWF ts' ∧ ts'.length < 2 ^ 24 := by
  unfold ds at h
  obtain ⟨b, hb, h2⟩ := Option.bind_eq_some_iff.1 h
  exact ds0_tokWF (frame_tokWF ht _ _ _ _ hb) h2

end DsSpec

namespace DsSpec
open ParSpec

theorem flat0_inj : ∀ (a b : List UInt64), a.flatMap (fun c => [1, c]) ++ [0] = b.flatMap (fun c => [1, c]) ++ [0] → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, true_and] at h
    obtain ⟨rfl, h⟩ := h
    rw [flat0_inj a b (by simpa using h)]

/-- the name `match` as a token -/
def matchTok : Tok := .id [109, 97, 116, 99, 104]

theorem noMatch_tok {ts : List UInt64} {toks : List Tok} (ht : TokL ts toks) (hm : matchTok ∉ toks) :
    ∀ f, ts.length < f → noMatch f ts = true := by
  induction ht with
  | nil => intro f hf; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩; simp [noMatch]
  | @kw r toks k h5 h14 _ _ ih =>
    intro f hf; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [noMatch, splitTok, h5, h14, if_false]
    rw [ih (fun e => hm (List.mem_cons_of_mem _ e)) f (by simp at hf; omega)]
    simp [MATCH]
  | @num r toks bs h8 _ _ ih =>
    intro f hf; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [List.cons_append, noMatch, splitTok, if_true, List.length_append, h8]
    rw [if_pos (by omega)]
    simp only
    have e1 : (bs ++ r).take 8 = bs := List.take_left' h8
    have e2 : (bs ++ r).drop 8 = r := List.drop_left' h8
    rw [e1, e2, ih (fun e => hm (List.mem_cons_of_mem _ e)) f (by simp [h8] at hf; omega)]
    simp [MATCH]
  | @id r toks nm hne _ ih =>
    intro f hf; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hi : ∀ (m : List UInt64) (r' : List UInt64), identTok (m.flatMap (fun c => [1, c]) ++ 0 :: r') =
        some (m.flatMap (fun c => [1, c]) ++ [0], r') := by
      intro m r'; induction m with
      | nil => simp [identTok]
      | cons c m ih => simp [identTok, ih]
    simp only [List.cons_append, noMatch, splitTok, show ¬ ((14 : UInt64) = 5) by decide, if_false, if_true, List.append_eq,
      hi, Option.map_some]
    rw [ih (fun e => hm (List.mem_cons_of_mem _ e)) f (by simp at hf; omega)]
    simp only [Bool.and_true, bne_iff_ne, ne_eq]
    intro e
    apply hm
    have : nm = [109, 97, 116, 99, 104] := by
      apply flat0_inj
      simp only [MATCH, List.cons.injEq, true_and] at e
      simpa using e
    subst this
    simp [matchTok]

/-- a token buffer has no scope markers: the frame passes it unchanged -/
theorem frame_id {ts : List UInt64} {toks : List Tok} (ht : TokL ts toks) :
    ∀ f, ts.length < f → ∀ ph, (ph = 0 ∨ ph = 1) → ∀ st, frame f ts ph st = some ts := by
  induction ht with
  | nil => intro f hf; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩; simp [frame]
  | @kw r toks k h5 h14 hok _ ih =>
    intro f hf ph hph st; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hk := okTag_le k hok
    have n : k ≠ 48 ∧ k ≠ 49 ∧ k ≠ 50 ∧ k ≠ 51 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro e; subst e; simp at hk)
    have h2 : ph ≠ 2 := by omega
    simp only [frame, n.1, n.2.1, n.2.2.1, n.2.2.2, h2, if_false, splitTok, h5, h14]
    rw [ih f (by simp at hf; omega) 1 (.inr rfl) st]; rfl
  | @num r toks bs h8 _ _ ih =>
    intro f hf ph hph st; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have h2 : ph ≠ 2 := by omega
    simp only [List.cons_append, frame, show ¬ ((5 : UInt64) = 48) by decide, show ¬ ((5 : UInt64) = 49) by decide,
      show ¬ ((5 : UInt64) = 50) by decide, show ¬ ((5 : UInt64) = 51) by decide, h2, if_false, splitTok, if_true,
      List.length_append, h8]
    rw [if_pos (by omega)]
    have e1 : (bs ++ r).take 8 = bs := List.take_left' h8
    have e2 : (bs ++ r).drop 8 = r := List.drop_left' h8
    simp only [e1, e2]
    rw [ih f (by simp [h8] at hf; omega) 1 (.inr rfl) st]; simp
  | @id r toks nm hne _ ih =>
    intro f hf ph hph st; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have h2 : ph ≠ 2 := by omega
    simp only [List.cons_append, frame, show ¬ ((14 : UInt64) = 48) by decide, show ¬ ((14 : UInt64) = 49) by decide,
      show ¬ ((14 : UInt64) = 50) by decide, show ¬ ((14 : UInt64) = 51) by decide, h2, if_false, splitTok,
      show ¬ ((14 : UInt64) = 5) by decide, if_true, List.append_eq, identTok_flat, Option.map_some]
    rw [ih f (by simp at hf; omega) 1 (.inr rfl) st]; simp

/-- a token buffer without the name `match` desugars to itself -/
theorem ds_id {ts : List UInt64} {toks : List Tok} (ht : TokL ts toks) (hm : matchTok ∉ toks) (hl : ts.length < 2 ^ 24) :
    ds ts = some ts := by
  unfold ds; rw [frame_id ht _ (by omega) 0 (.inl rfl) [], Option.bind_some]
  unfold ds0; rw [if_pos hl, if_pos (noMatch_tok ht hm _ (by omega))]

end DsSpec
