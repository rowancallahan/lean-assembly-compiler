/- Nano/Parser/ParInvName: Layer 3, NAME LOOKUP on `Rep` (box G; for tasks 43 / 55).
* `v85_drop` / `v8_drop`: the comparison / def-lookup loops write only cells 0, 22, 31 (the output suffix is untouched);
* `v8_val`: h[22] after the def lookup = `findD st.defs x` (+1, 0 for none);
* `rep_same`: `Rep` survives a `Same 21` / `Same 22` change (scratch cells) that keeps the output suffix. -/
import Nano.Parser.ParInvDefs
import Nano.Parser.ParInvBind
namespace ParInv
open C BufL ParSpec ParRun

theorem v85_drop : ∀ (n : Nat) (h : Buf) (a b : UInt64), (v85 n h a b).drop 184384 = h.drop 184384
  | 0, h, a, b => by rw [v85]; exact drop_bset0 _ _ _ (by decide)
  | n + 1, h, a, b => by
    rw [v85]
    simp only []
    repeat' split
    all_goals first
      | exact drop_bset0 _ _ _ (by decide)
      | exact v85_drop n h _ _

theorem v8_drop (h : Buf) (j x : UInt64) : (v8 h j x).drop 184384 = h.drop 184384 := drop_v8 h j x

/-- **def lookup, value**: h[22] = index + 1 of the innermost finished def with this name, 0 if none -/
theorem v8_val {h : Buf} {st : St} {bb : Bool} {p : UInt64} {nm : List UInt64} (hD : DefsRep h st bb)
    (h7 : (bget h 7).toNat < 2 ^ 24) (hl : 31 < h.length) (hn : NameOK h p nm) :
    bget (v8 h (bget h 12) p) 22 = (((findD st.defs (nm.map UInt64.toNat)).map (· + 1)).getD 0).toUInt64 :=
  (v8_findV hD h7 hl hn).2

/-- `Rep` ignores the scratch cells 21, 22 and 31 -/
theorem rep_same {r : Nat} {h h' ts : Buf} {st : St} {fs : List Frame} (R : Rep h ts st fs) (s : Same r h h')
    (hr : r = 21 ∨ r = 22) (ed : h'.drop 184384 = h.drop 184384) : Rep h' ts st fs := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := R
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have e : ∀ i : UInt64, i.toNat ≠ 21 → i.toNat ≠ 22 → i.toNat ≠ 31 → bget h' i = bget h i :=
    fun i a b c => s.2 i (by omega) c
  have et : TokAgree h h' := ⟨e 7 (by decide) (by decide) (by decide), fun i hi => e i (by omega) (by omega) (by omega)⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (by omega) (by omega)
  have c : ∀ n : UInt64, n.toNat ≠ 21 → n.toNat ≠ 22 → n.toNat ≠ 31 → bget h' n = bget h n := e
  refine ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide) (by decide)]; exact r0,
    by rw [c 3 (by decide) (by decide) (by decide)]; exact tokAt_frame et hn r3,
    by rw [c 11 (by decide) (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega) (by omega)) et hn es,
    defs_frame rD (c 12 (by decide) (by decide) (by decide)) (c 27 (by decide) (by decide) (by decide)) (c 26 (by decide) (by decide) (by decide))
      (fun i a _ => e i (by omega) (by omega) (by omega)) et hn es,
    arena_frame rA (c 8 (by decide) (by decide) (by decide)) (c 9 (by decide) (by decide) (by decide))
      (fun i a _ => e i (by omega) (by omega) (by omega)) es,
    fun s hs => by rw [c 25 (by decide) (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx => by rw [c 29 (by decide) (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx),
    by rw [c 30 (by decide) (by decide) (by decide)]; exact r30, by rw [c 32 (by decide) (by decide) (by decide)]; exact r32,
    out_frame rO ed,
    tasks_frame rK (c 5 (by decide) (by decide) (by decide)) (fun i _ _ => e i (by omega) (by omega) (by omega)) et hn es
      (fun i a _ => e i (by omega) (by omega) (by omega)) rA.2.1⟩

/-! ## binding lookup: v7 ↔ `findB` -/
theorem v7_drop : ∀ (n : Nat) (h : Buf) (j x : UInt64), (v7 n h j x).drop 184384 = h.drop 184384
  | 0, h, j, x => by rw [v7]; exact drop_bset0 _ _ _ (by decide)
  | n + 1, h, j, x => by
    rw [v7]
    simp only []
    repeat' split
    all_goals first
      | exact drop_bset0 _ _ _ (by decide)
      | (rw [drop_bset0 _ _ _ (by decide)]; exact v85_drop _ _ _ _)
      | (rw [v7_drop n]; exact v85_drop _ _ _ _)

theorem findB_snoc (l : List Bd) (d : Bd) (x : List Nat) : findB (l ++ [d]) x = if d.name = x then some d else findB l x := by
  unfold findB
  rw [List.reverse_append]
  by_cases hd : d.name = x <;> simp [hd]

/-- `idxOf` (the machine's innermost 1-based match) is B's `findB` on the first `j` bindings -/
theorem idxOf_findB (tab : List (UInt64 × List UInt64)) (bs : List Bd) (nx : List UInt64) (x : List Nat)
    (hx : nx.map UInt64.toNat = x) (hl : tab.length = bs.length)
    (hn : ∀ i (hi : i < tab.length) (hi' : i < bs.length), (tab[i].2).map UInt64.toNat = (bs[i]'hi').name) :
    ∀ j, j ≤ bs.length → (idxOf tab nx j = 0 ∧ findB (bs.take j) x = none) ∨
      (∃ i, idxOf tab nx j = i + 1 ∧ ∃ hi : i < bs.length, findB (bs.take j) x = some (bs[i]'hi))
  | 0, _ => Or.inl (by simp [idxOf, findB])
  | j + 1, hj => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, findB_snoc]
    simp only [idxOf]
    have hget : tab.getD j (0, []) = tab[j]'(by omega) := by simp [List.getD, show j < tab.length by omega]
    rw [hget]
    have e := hn j (by omega) (by omega)
    by_cases hq : (tab[j]'(by omega)).2 = nx
    · have : (bs[j]'(by omega)).name = x := by rw [← e, hq, hx]
      exact Or.inr ⟨j, by simp [hq], by omega, by simp [this]⟩
    · have : ¬ (bs[j]'(by omega)).name = x := by
        intro c; apply hq; apply map_toNat_inj; rw [e, c, hx]
      simp only [hq, this, if_false]
      exact idxOf_findB tab bs nx x hx hl hn j (by omega)

/-- a table of name positions and spellings for the bindings -/
theorem bindTab_of {h : Buf} {bs : List Bd} (hB : BindsRep h bs) (h7 : (bget h 7).toNat < 2 ^ 24) :
    ∃ tab : List (UInt64 × List UInt64), tab.length = bs.length ∧ TabRep h tab ∧
      ∀ i (hi : i < tab.length) (hi' : i < bs.length), (tab[i].2).map UInt64.toNat = (bs[i]'hi').name := by
  obtain ⟨_, _, hrows⟩ := hB
  have key : ∀ n, n ≤ bs.length → ∃ tab : List (UInt64 × List UInt64), tab.length = n ∧
      (∀ i (hi : i < tab.length) (hi' : i < bs.length), bget h (d9 + 4 * i.toUInt64) = (tab[i]).1 ∧
        NameOK h (tab[i]).1 (tab[i]).2 ∧ (tab[i]).2.length < 2 ^ 24 ∧ (tab[i].2).map UInt64.toNat = (bs[i]'hi').name) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨[], rfl, fun i hi => absurd hi (by simp)⟩
    | succ n ih =>
      intro hn
      obtain ⟨tab, hl, ht⟩ := ih (by omega)
      obtain ⟨⟨nm, hok, hmap⟩, _⟩ := hrows n (by omega)
      refine ⟨tab ++ [(bget h (d9 + 4 * n.toUInt64), nm)], by simp [hl], fun i hi hi' => ?_⟩
      by_cases hin : i < tab.length
      · rw [List.getElem_append_left hin]; exact ht i hin hi'
      · have hin' : i = n := by simp at hi; omega
        subst hin'
        rw [List.getElem_append_right (by omega)]
        simp only [hl, Nat.sub_self, List.getElem_cons_zero]
        refine ⟨by simp, hok, ?_, hmap⟩
        obtain ⟨_, _, hb⟩ := hok
        omega
  obtain ⟨tab, hl, ht⟩ := key bs.length (Nat.le_refl _)
  exact ⟨tab, hl, fun i hi => ⟨(ht i hi (by omega)).1, (ht i hi (by omega)).2.1, (ht i hi (by omega)).2.2.1⟩,
    fun i hi hi' => (ht i hi hi').2.2.2⟩

/-- **binding lookup**: h[21] after `v7` over all bindings is 0 with `findB = none`, or `i + 1` with `findB = some binds[i]`;
only the scratch cells 21 / 31 change -/
theorem v7_findB {h : Buf} {bs : List Bd} {p : UInt64} {nm : List UInt64} (hB : BindsRep h bs)
    (h7 : (bget h 7).toNat < 2 ^ 24) (hl : 31 < h.length) (hn : NameOK h p nm) :
    Same 21 h (v7 16777216 h (bget h 4) p) ∧
      ((bget (v7 16777216 h (bget h 4) p) 21 = 0 ∧ findB bs (nm.map UInt64.toNat) = none) ∨
       (∃ i, bget (v7 16777216 h (bget h 4) p) 21 = (i + 1).toUInt64 ∧ ∃ hi : i < bs.length,
          findB bs (nm.map UInt64.toNat) = some (bs[i]'hi))) := by
  obtain ⟨tab, htl, hTab, hnames⟩ := bindTab_of hB h7
  obtain ⟨e4, hlt, _⟩ := hB
  have hnm : nm.length < 2 ^ 24 := by obtain ⟨_, _, hb⟩ := hn; omega
  obtain ⟨hS, h21⟩ := v7_lookup tab p nm bs.length 16777216 h (bget h 4) e4 (by omega) (by omega) (by omega) hl
    (by omega) hTab hn hnm
  refine ⟨hS, ?_⟩
  rw [h21]
  have := idxOf_findB tab bs nm _ rfl htl (fun i hi hi' => hnames i hi hi') bs.length (Nat.le_refl _)
  rw [List.take_length] at this
  rcases this with ⟨h0, hf⟩ | ⟨i, hi, hlt', hf⟩
  · exact Or.inl ⟨by rw [h0]; rfl, hf⟩
  · exact Or.inr ⟨i, by rw [hi], hlt', hf⟩

end ParInv
