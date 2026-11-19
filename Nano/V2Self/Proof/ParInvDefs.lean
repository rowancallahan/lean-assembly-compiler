/- Nano/V2Self/Proof/ParInvDefs: def-level machine lemmas (parser lead): the identifier skip `v86`, the def-table lookup `v8`
against box B's `findD`, and the def-start task 60 (`v127`). -/
import Nano.V2Self.Proof.ParInvValRep
namespace ParInv
open C BufL ParSpec ParRun

/-- **v86** skips an identifier's spelling: from the first marker cell `a` it stops after the terminator and stores that position
in the cursor h[3] -/
theorem v86_skip : ∀ (nm : List UInt64) (n : Nat) (h : Buf) (a : UInt64), NameSeq h a nm →
    a.toNat + 2 * nm.length < (bget h 7).toNat → nm.length + 1 ≤ n →
    v86 n h a = bset h 3 (a + 2 * nm.length.toUInt64 + 1)
  | [], n + 1, h, a, hs, hl, _ => by
    simp only [NameSeq] at hs
    have ha : a < bget h 7 := by rw [UInt64.lt_iff_toNat_lt]; simpa using hl
    simp [v86, ha, hs]
  | c :: t, n + 1, h, a, hs, hl, hn => by
    simp only [NameSeq] at hs
    obtain ⟨h1, _, h3⟩ := hs
    have ha : a < bget h 7 := by rw [UInt64.lt_iff_toNat_lt]; simp at hl; omega
    have h0 : (bget h (d11 + a) == 0) = false := by rw [h1]; decide
    have a2 : (a + 2).toNat = a.toNat + 2 := by
      have := (bget h 7).toNat_lt; rw [UInt64.toNat_add]; simp at hl ⊢; omega
    have ih := v86_skip t n h (a + 2) h3 (by rw [a2]; simp at hl; omega) (by simp at hn; omega)
    simp only [v86, ha, if_true, h0, Bool.false_eq_true, if_false, ih]
    congr 1
    simp [Nat.toUInt64]; grind
  | _, 0, _, _, _, _, hn => by simp at hn

/-- B's def lookup on a list extended by one row -/
theorem findD_snoc (l : List DefR) (d : DefR) (x : List Nat) :
    findD (l ++ [d]) x = if d.name = x then some l.length else findD l x := by
  unfold findD
  rw [List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  rw [List.findIdx?_cons]
  by_cases hd : d.name = x
  · simp [hd]
  · simp only [hd, beq_iff_eq, if_false, Option.map_map]
    simp only [List.length_append, List.length_singleton]
    cases hf : List.findIdx? (fun d => d.name == x) l.reverse with
    | none => simp
    | some i =>
      have := (List.findIdx?_eq_some_iff_getElem.mp hf).1
      simp at this ⊢; omega

theorem map_toNat_inj : ∀ {a b : List UInt64}, a.map UInt64.toNat = b.map UInt64.toNat → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [UInt64.toNat_inj.mp h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- `idxOf` (the machine's innermost 1-based match) is B's `findD` on the first `j` rows -/
theorem idxOf_findD (tab : List (UInt64 × List UInt64)) (ds : List DefR) (nx : List UInt64) (x : List Nat)
    (hx : nx.map UInt64.toNat = x) (hl : tab.length = ds.length)
    (hn : ∀ i (hi : i < tab.length) (hi' : i < ds.length), (tab[i].2).map UInt64.toNat = (ds[i]'hi').name) :
    ∀ j, j ≤ ds.length → idxOf tab nx j = ((findD (ds.take j) x).map (· + 1)).getD 0
  | 0, _ => by simp [idxOf, findD]
  | j + 1, hj => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, findD_snoc]
    simp only [idxOf]
    have hget : tab.getD j (0, []) = tab[j]'(by omega) := by simp [List.getD, show j < tab.length by omega]
    rw [hget, idxOf_findD tab ds nx x hx hl hn j (by omega)]
    have e := hn j (by omega) (by omega)
    have hlen : (ds.take j).length = j := by simp; omega
    by_cases hq : (tab[j]'(by omega)).2 = nx
    · have : (ds[j]'(by omega)).name = x := by rw [← e, hq, hx]
      simp [hq, this, hlen]
    · have : ¬ (ds[j]'(by omega)).name = x := by
        intro c; apply hq; apply map_toNat_inj; rw [e, c, hx]
      simp [hq, this]

/-- a table of name positions and spellings for the finished rows -/
theorem defTab_of {h : Buf} {st : St} {bb : Bool} (hD : DefsRep h st bb) (h7 : (bget h 7).toNat < 2 ^ 24) :
    ∃ tab : List (UInt64 × List UInt64), tab.length = st.defs.length ∧ DefTabRep h tab ∧
      ∀ i (hi : i < tab.length) (hi' : i < st.defs.length), (tab[i].2).map UInt64.toNat = (st.defs[i]'hi').name := by
  obtain ⟨_, hlt, _, hrows, _⟩ := hD
  have key : ∀ n, n ≤ st.defs.length → ∃ tab : List (UInt64 × List UInt64), tab.length = n ∧
      (∀ i (hi : i < tab.length) (hi' : i < st.defs.length), bget h (d7 + 8 * i.toUInt64) = (tab[i]).1 ∧
        NameOK h (tab[i]).1 (tab[i]).2 ∧ (tab[i]).2.length < 2 ^ 24 ∧ (tab[i].2).map UInt64.toNat = (st.defs[i]'hi').name) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨[], rfl, fun i hi => absurd hi (by simp)⟩
    | succ n ih =>
      intro hn
      obtain ⟨tab, hl, ht⟩ := ih (by omega)
      obtain ⟨⟨⟨nm, hok, hmap⟩, _⟩, _⟩ := hrows n (by omega)
      refine ⟨tab ++ [(bget h (d7 + 8 * n.toUInt64), nm)], by simp [hl], fun i hi hi' => ?_⟩
      by_cases hin : i < tab.length
      · rw [List.getElem_append_left hin]; exact ht i hin hi'
      · have hin' : i = n := by simp at hi; omega
        subst hin'
        rw [List.getElem_append_right (by omega)]
        simp only [hl, Nat.sub_self, List.getElem_cons_zero]
        refine ⟨by simp, hok, ?_, hmap⟩
        obtain ⟨_, _, hb⟩ := hok
        omega
  obtain ⟨tab, hl, ht⟩ := key st.defs.length (Nat.le_refl _)
  exact ⟨tab, hl, fun i hi => ⟨(ht i hi (by omega)).1, (ht i hi (by omega)).2.1, (ht i hi (by omega)).2.2.1⟩,
    fun i hi hi' => (ht i hi hi').2.2.2⟩

/-- an identifier token under the cursor -/
theorem tok_id {h ts : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) (hT : TokensAt h ts) (hc : bget h (d11 + p) = 14) :
    ∃ nm rest, toks = .id (nm.map UInt64.toNat) :: rest ∧ NameOK h p nm ∧ TokAt h (p + 2 + 2 * nm.length.toUInt64) rest := by
  cases r with
  | nil e => exfalso; rw [e, hT.2.2.2, hT.2.1] at hc; exact absurd hc (by decide)
  | kw t _ b t5 t14 _ _ => rw [b] at hc; exact absurd hc t14
  | num _ _ b => rw [b] at hc; exact absurd hc (by decide)
  | id nm a x => exact ⟨nm, _, rfl, a, x⟩

/-- **def lookup**: scanning the finished rows for the identifier at `p` finds nothing iff B's `findD` finds nothing; only the
scratch cells 22 and 31 change -/
theorem v8_findD {h : Buf} {st : St} {bb : Bool} {p : UInt64} {nm : List UInt64} (hD : DefsRep h st bb)
    (h7 : (bget h 7).toNat < 2 ^ 24) (hl : 31 < h.length) (hn : NameOK h p nm) :
    Same 22 h (v8 16777216 h (bget h 12) p) ∧
      (bget (v8 16777216 h (bget h 12) p) 22 = 0 ↔ findD st.defs (nm.map UInt64.toNat) = none) := by
  obtain ⟨tab, htl, hTab, hnames⟩ := defTab_of hD h7
  obtain ⟨e12, hlt, _⟩ := hD
  have hnm : nm.length < 2 ^ 24 := by obtain ⟨_, _, hb⟩ := hn; omega
  obtain ⟨hS, h22⟩ := v8_lookup tab p nm st.defs.length 16777216 h (bget h 12) e12 (by omega) (by omega) (by omega) hl
    (by omega) hTab hn hnm
  refine ⟨hS, ?_⟩
  rw [h22, idxOf_findD tab st.defs nm _ rfl htl (fun i hi hi' => hnames i hi hi') _ (Nat.le_refl _), List.take_length]
  cases hf : findD st.defs (nm.map UInt64.toNat) with
  | none => simp
  | some j =>
    simp only [Option.map_some, Option.getD_some, reduceCtorEq, iff_false]
    intro e
    have := congrArg UInt64.toNat e
    have hj := findD_lt hf
    simp [Nat.toUInt64] at this; omega

end ParInv
