/- Nano/V2Self/Proof/ParInvDefs: def-level machine lemmas (parser lead): the identifier skip `v86`, the def-table lookup `v8`
against box B's `findD`, and the def-start task 60 (`v127`). -/
import Nano.V2Self.Proof.ParInvValRep
import Nano.V2Self.Proof.ParInvTy
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

/-! ## opening a def (task 60's success branch) -/
/-- a row whose own 8 cells and the parameter-code region agree -/
theorem rowRep_frame' {h h' : Buf} {j : Nat} {d : DefR} (hj : j < 512) (r : RowRep h j d)
    (c : ∀ k : UInt64, k.toNat < 8 → bget h' (d7 + 8 * j.toUInt64 + k) = bget h (d7 + 8 * j.toUInt64 + k))
    (cc : RegAgree h h' 151616 155712) (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') :
    RowRep h' j d := by
  have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
  obtain ⟨a0, a1, a2, a3, a4, a6, a5, ap⟩ := r
  refine ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1, by rw [c 2 (by decide)]; exact a2,
    by rw [c 3 (by decide)]; exact a3.frame es, by rw [c 4 (by decide)]; exact a4, by rw [c 6 (by decide)]; exact a6,
    by rw [c 5 (by decide)]; exact a5, fun i hi => ?_⟩
  rw [c 5 (by decide), cc _ (by rw [parCell _ _ (by omega)]; omega) (by rw [parCell _ _ (by omega)]; omega)]
  exact (ap i hi).frame es

/-- the cells task 60 writes when it opens def row `j = h[12]` for the name at token position `p` -/
def openW (G : Buf) (p : UInt64) : Buf :=
  let j := bget G 12
  bset (bset (bset (bset (bset (bset (bset (bset G (d7 + 8 * j + 0) p) (d7 + 8 * j + 5) (bget G 27)) (d7 + 8 * j + 2) 0)
    4 0) 8 0) 9 0) 11 0) 30 0

theorem rowIdx (j : UInt64) (hj : j.toNat < 512) (k : UInt64) (hk : k.toNat < 8) :
    (d7 + 8 * j + k).toNat = 147520 + 8 * j.toNat + k.toNat := by
  have := defCell j.toNat hj k hk
  have e : j.toNat.toUInt64 = j := by apply UInt64.toNat_inj.mp; simp [Nat.toUInt64]
  rwa [e] at this

/-- cells task 60 does not write are unchanged -/
theorem openW_other (G : Buf) (p : UInt64) (hj : (bget G 12).toNat < 512) (i : UInt64)
    (h1 : i.toNat ≠ 4) (h2 : i.toNat ≠ 8) (h3 : i.toNat ≠ 9) (h4 : i.toNat ≠ 11) (h5 : i.toNat ≠ 30)
    (h6 : i.toNat ≠ 147520 + 8 * (bget G 12).toNat) (h7 : i.toNat ≠ 147520 + 8 * (bget G 12).toNat + 2)
    (h8 : i.toNat ≠ 147520 + 8 * (bget G 12).toNat + 5) : bget (openW G p) i = bget G i := by
  have r0 := rowIdx (bget G 12) hj 0 (by decide)
  have r2 := rowIdx (bget G 12) hj 2 (by decide)
  have r5 := rowIdx (bget G 12) hj 5 (by decide)
  simp only [show (0 : UInt64).toNat = 0 from rfl, show (2 : UInt64).toNat = 2 from rfl,
    show (5 : UInt64).toNat = 5 from rfl, Nat.add_zero] at r0 r2 r5
  unfold openW
  rw [bget_bset' _ _ _ _ (by simp; omega), bget_bset' _ _ _ _ (by simp; omega), bget_bset' _ _ _ _ (by simp; omega),
    bget_bset' _ _ _ _ (by simp; omega), bget_bset' _ _ _ _ (by simp; omega), bget_bset' _ _ _ _ (by rw [r2]; omega),
    bget_bset' _ _ _ _ (by rw [r5]; omega), bget_bset' _ _ _ _ (by rw [r0]; omega)]

theorem openW_len (G : Buf) (p : UInt64) : (openW G p).length = G.length := by simp [openW, length_bset]

/-- the cells task 60 writes -/
theorem openW_vals (G : Buf) (p : UInt64) (hj : (bget G 12).toNat < 512) (hl : 184384 ≤ G.length) :
    let r := d7 + 8 * bget G 12
    bget (openW G p) 4 = 0 ∧ bget (openW G p) 8 = 0 ∧ bget (openW G p) 9 = 0 ∧ bget (openW G p) 11 = 0 ∧
    bget (openW G p) 30 = 0 ∧ bget (openW G p) r = p ∧ bget (openW G p) (r + 2) = 0 ∧ bget (openW G p) (r + 5) = bget G 27 ∧
    bget (openW G p) 12 = bget G 12 ∧ bget (openW G p) 27 = bget G 27 := by
  intro r
  have r0 := rowIdx (bget G 12) hj 0 (by decide)
  have r2 := rowIdx (bget G 12) hj 2 (by decide)
  have r5 := rowIdx (bget G 12) hj 5 (by decide)
  simp only [show (0 : UInt64).toNat = 0 from rfl, show (2 : UInt64).toNat = 2 from rfl,
    show (5 : UInt64).toNat = 5 from rfl, Nat.add_zero, UInt64.add_zero] at r0 r2 r5
  have L : ∀ (b : Buf) (i v : UInt64), (bset b i v).length = b.length := fun _ _ _ => length_bset _ _ _
  have e12 := openW_other G p hj 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by simp; omega) (by simp; omega) (by simp; omega)
  have e27 := openW_other G p hj 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by simp; omega) (by simp; omega) (by simp; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, e12, e27⟩ <;> unfold openW <;> simp only [UInt64.add_zero]
  · rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide),
      bget_bset' _ _ _ _ (by decide), bget_bset_eq _ _ _ _ rfl (by simp only [L]; (try simp) <;> omega)]
  · rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide),
      bget_bset_eq _ _ _ _ rfl (by simp only [L]; (try simp) <;> omega)]
  · rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide), bget_bset_eq _ _ _ _ rfl (by simp only [L]; (try simp) <;> omega)]
  · rw [bget_bset' _ _ _ _ (by decide), bget_bset_eq _ _ _ _ rfl (by simp only [L]; (try simp) <;> omega)]
  · rw [bget_bset_eq _ _ _ _ rfl (by simp only [L]; (try simp) <;> omega)]
  · rw [bget_bset' _ _ _ _ (by rw [r0]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [r0]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by rw [r0]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [r0]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by rw [r0]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [r0, r2]; omega),
      bget_bset' _ _ _ _ (by rw [r0, r5]; omega), bget_bset_eq _ _ _ _ rfl (by rw [r0]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [r2]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [r2]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by rw [r2]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [r2]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by rw [r2]; (try simp) <;> omega), bget_bset_eq _ _ _ _ rfl (by simp only [L]; rw [r2]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [r5]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [r5]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by rw [r5]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [r5]; (try simp) <;> omega),
      bget_bset' _ _ _ _ (by rw [r5]; (try simp) <;> omega), bget_bset' _ _ _ _ (by rw [r2, r5]; omega),
      bget_bset_eq _ _ _ _ rfl (by simp only [L]; rw [r5]; omega)]

/-- **open a def**: from the between-defs representation (current row zero) to the representation inside the new def, for any
final heap that agrees with `openW` outside the cursor, the task count and the task records -/
theorem rep_open {G H ts : Buf} {st : St} {fs' : List Frame} {p : UInt64} {x : List Nat} {toks' : List Tok}
    (R : Rep G ts st []) (hE : inDefF [] = false) (hx : NameAt G p x) (hj : (bget G 12).toNat < 512)
    (hl : H.length = G.length)
    (ag : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 3 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) → bget H i = bget (openW G p) i)
    (ed : H.drop 184384 = G.drop 184384) (hK : TokAt H (bget H 3) toks')
    (hT : TasksRep H [] fs') (hD : inDefF fs' = true) :
    Rep H ts { st with toks := toks', cur := DefR.fresh x, binds := [], vals := [], arena := [], nx := 0, arm := false } fs' := by
  obtain ⟨hn, hlen, har⟩ := rep_bounds R
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := R
  rw [hE] at rD
  obtain ⟨d12, dlt, d27, drows, dcur, dz, d0⟩ := rD
  simp only [Bool.false_eq_true, if_false] at dcur
  have hjN : (bget G 12).toNat = st.defs.length := d12
  obtain ⟨v4, v8, v9, v11, v30, vR0, vR2, vR5, v12, v27⟩ := openW_vals G p hj hlen
  -- agreement with G outside the written cells
  have oth : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 3 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) → i.toNat ≠ 4 → i.toNat ≠ 8 →
      i.toNat ≠ 9 → i.toNat ≠ 11 → i.toNat ≠ 30 → i.toNat ≠ 147520 + 8 * st.defs.length → i.toNat ≠ 147520 + 8 * st.defs.length + 2 →
      i.toNat ≠ 147520 + 8 * st.defs.length + 5 → bget H i = bget G i := by
    intro i a5 a3 a64 a4 a8 a9 a11 a30 b0 b2 b5
    rw [ag i a5 a3 a64]; exact openW_other G p hj i a4 a8 a9 a11 a30 (by omega) (by omega) (by omega)
  have big : ∀ i : UInt64, 151616 ≤ i.toNat → bget H i = bget G i := fun i hi =>
    oth i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have cell : ∀ i : UInt64, i.toNat < 64 → i.toNat ≠ 3 → i.toNat ≠ 4 → i.toNat ≠ 5 → i.toNat ≠ 8 → i.toNat ≠ 9 → i.toNat ≠ 11 →
      i.toNat ≠ 30 → bget H i = bget G i :=
    fun i hk a3 a4 a5 a8 a9 a11 a30 => oth i a5 a3 (by omega) a4 a8 a9 a11 a30 (by omega) (by omega) (by omega)
  have et : TokAgree G H := ⟨cell 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    fun i hi => big i (by omega)⟩
  have es : ShTabAgree G H := fun i a _ => big i (by omega)
  have w : ∀ i : UInt64, (i.toNat = 4 ∨ i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 11 ∨ i.toNat = 30 ∨ i.toNat = 12 ∨ i.toNat = 27) →
      bget H i = bget (openW G p) i := fun i hi => ag i (by omega) (by omega) (by omega)
  have u : ∀ n : Nat, n < 64 → (n.toUInt64).toNat = n := fun n hn => by simp [Nat.toUInt64]; omega
  -- the row cells
  have rc : ∀ k : UInt64, k.toNat < 8 → bget H (d7 + 8 * st.defs.length.toUInt64 + k) = bget (openW G p) (d7 + 8 * st.defs.length.toUInt64 + k) :=
    fun k hk => ag _ (by rw [defCell _ dlt k hk]; omega) (by rw [defCell _ dlt k hk]; omega) (by rw [defCell _ dlt k hk]; omega)
  have hj' : bget G 12 = st.defs.length.toUInt64 := by apply UInt64.toNat_inj.mp; rw [d12]; simp [Nat.toUInt64]; omega
  have rz : ∀ k : UInt64, k.toNat < 8 → k.toNat ≠ 0 → k.toNat ≠ 2 → k.toNat ≠ 5 → bget H (d7 + 8 * st.defs.length.toUInt64 + k) = 0 :=
    fun k hk a0 a2 a5 => by
      rw [rc k hk, ← hj', openW_other G p hj _ (by rw [rowIdx _ hj k hk]; omega) (by rw [rowIdx _ hj k hk]; omega)
        (by rw [rowIdx _ hj k hk]; omega) (by rw [rowIdx _ hj k hk]; omega) (by rw [rowIdx _ hj k hk]; omega)
        (by rw [rowIdx _ hj k hk]; omega) (by rw [rowIdx _ hj k hk]; omega) (by rw [rowIdx _ hj k hk]; omega), hj']
      exact dcur k hk
  refine ⟨tokensAt_frame rT et rts, rts, ?_, hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT⟩
  · rw [cell 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact r0
  · rw [w 11 (by decide), v11]; rfl
  · exact ⟨by rw [w 4 (by decide), v4]; rfl, by simp, fun i hi => absurd hi (by simp)⟩
  · rw [hD]
    refine ⟨by rw [w 12 (by decide), v12]; exact d12, dlt, by rw [w 27 (by decide), v27]; exact d27, fun j hj => ?_, ?_, fun j h1 h2 => ?_, ?_⟩
    · have hj : j < st.defs.length := hj
      obtain ⟨rr, rs⟩ := drows j hj
      refine ⟨rowRep_frame' (by omega) rr (fun k hk => ?_) (fun i a b => big i a) et hn es, ?_⟩
      · exact oth _ (by rw [defCell j (by omega) k hk]; omega) (by rw [defCell j (by omega) k hk]; omega)
          (by rw [defCell j (by omega) k hk]; omega) (by rw [defCell j (by omega) k hk]; omega) (by rw [defCell j (by omega) k hk]; omega)
          (by rw [defCell j (by omega) k hk]; omega) (by rw [defCell j (by omega) k hk]; omega) (by rw [defCell j (by omega) k hk]; omega)
          (by rw [defCell j (by omega) k hk]; omega) (by rw [defCell j (by omega) k hk]; omega) (by rw [defCell j (by omega) k hk]; omega)
      · rw [w 27 (by decide), v27, oth (d7 + 8 * j.toUInt64 + 5) (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega) (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega)
          (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega) (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega)
          (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega) (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega)
          (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega) (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega)
          (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega) (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega)
          (by rw [defCell j (by omega) 5 (by decide)]; (try simp) <;> omega)]
        exact rs
    · simp only [if_true]
      rw [hj'] at vR0 vR2 vR5
      have c0 : bget H (d7 + 8 * st.defs.length.toUInt64) = p := by
        have := rc 0 (by decide); simp only [UInt64.add_zero] at this; rw [this]; exact vR0
      have c2 : bget H (d7 + 8 * st.defs.length.toUInt64 + 2) = 0 := by rw [rc 2 (by decide)]; exact vR2
      have c5 : bget H (d7 + 8 * st.defs.length.toUInt64 + 5) = bget G 27 := by rw [rc 5 (by decide)]; exact vR5
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by simp [DefR.fresh])⟩, ?_⟩
      · rw [c0]; exact nameAt_frame et (by omega) hx
      · rw [rz 1 (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [c2]; rfl
      · rw [rz 3 (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [rz 4 (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [rz 6 (by decide) (by decide) (by decide) (by decide)]; rfl
      · rw [c5]; simp [DefR.fresh]; omega
      · rw [c5, w 27 (by decide), v27]; simp [DefR.fresh]
    · have h1 : st.defs.length < j := h1
      exact fun k hk => by
        rw [oth _ (by rw [defCell j h2 k hk]; omega) (by rw [defCell j h2 k hk]; omega) (by rw [defCell j h2 k hk]; omega)
          (by rw [defCell j h2 k hk]; omega) (by rw [defCell j h2 k hk]; omega) (by rw [defCell j h2 k hk]; omega)
          (by rw [defCell j h2 k hk]; omega) (by rw [defCell j h2 k hk]; omega) (by rw [defCell j h2 k hk]; omega)
          (by rw [defCell j h2 k hk]; omega) (by rw [defCell j h2 k hk]; omega)]
        exact dz j h1 h2 k hk
    · intro i h1 h2
      rw [w 27 (by decide), v27] at h1
      have e : (d7 + 4096 + i.toUInt64).toNat = 151616 + i := by
        rw [UInt64.toNat_add]; simp [Nat.toUInt64, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; omega
      rw [big _ (by rw [e]; omega)]
      exact d0 i h1 h2
  · refine ⟨by rw [w 9 (by decide), v9]; rfl, by simp, by rw [w 8 (by decide), v8]; rfl, by simp, fun _ => [],
      fun u hu => absurd hu (by simp), fun k hk => absurd hk (by simp), fun k1 _ h1 => absurd h1 (by simp),
      fun k1 _ h1 => absurd h1 (by simp)⟩
  · intro s hs
    rw [cell 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact (r25 s hs).frame es
  · intro y hy hne
    rw [cell 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact nameAt_frame et (by omega) (r29 y hy hne)
  · rw [w 30 (by decide), v30]; rfl
  · rw [cell 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact r32
  · exact out_frame rO ed

end ParInv
