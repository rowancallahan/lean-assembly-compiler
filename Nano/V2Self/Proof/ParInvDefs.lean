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

/-! ## between defs: the representation without the task stack, current row zero -/
/-- C's `Rep` components except the task stack, with the def table BETWEEN defs (current row zero) -/
def RepZ (h : Buf) (ts : Buf) (st : St) : Prop :=
  TokensAt h ts ∧ ts.length < 2 ^ 24 ∧
  bget h 0 = (if st.acc then 2 else 1) ∧
  TokAt h (bget h 3) st.toks ∧
  bget h 11 = st.nx.toUInt64 ∧
  BindsRep h st.binds ∧
  DefsRep h st false ∧
  ArenaRep h st.arena st.vals ∧
  (∀ s, st.ty = some s → ShapeCode h (bget h 25) s) ∧
  (∀ x, st.stash = x → x ≠ [] → NameAt h (bget h 29) x) ∧
  bget h 30 = b01 st.arm ∧
  bget h 32 = st.sslot.toUInt64 ∧
  OutRep h ts st.out

theorem repZ_of {h ts : Buf} {st : St} (r : Rep h ts st [.defs]) : RepZ h ts st ∧ TasksRep h st.arena [.defs] :=
  ⟨⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.1,
    r.2.2.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.2.2.2.2.1⟩,
    r.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem repZ_bounds {h ts : Buf} {st : St} (r : RepZ h ts st) :
    (bget h 7).toNat < 2 ^ 32 ∧ 184384 ≤ h.length ∧ st.arena.length ≤ 16384 := by
  obtain ⟨rT, rts, _, _, _, _, _, rA, _, _, _, _, rO⟩ := r
  exact ⟨by rw [rT.2.2.2]; simp; omega, by rw [rO.1]; omega, rA.2.1⟩

/-- RepZ only reads cells other than the cursor 3, the task count 5 and the scratch cells 22, 31 (the cursor through `toks`) -/
theorem repZ_frame {h h' ts : Buf} {st : St} {toks' : List Tok} (r : RepZ h ts st)
    (e : ∀ i : UInt64, i.toNat ≠ 3 → i.toNat ≠ 5 → i.toNat ≠ 22 → i.toNat ≠ 31 → bget h' i = bget h i)
    (ed : h'.drop 184384 = h.drop 184384) (hK : TokAt h' (bget h' 3) toks') : RepZ h' ts { st with toks := toks' } := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have c : ∀ n : UInt64, n.toNat ≠ 3 → n.toNat ≠ 5 → n.toNat ≠ 22 → n.toNat ≠ 31 → bget h' n = bget h n := e
  have et : TokAgree h h' := ⟨c 7 (by decide) (by decide) (by decide) (by decide), fun i hi => e i (by omega) (by omega) (by omega) (by omega)⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (by omega) (by omega) (by omega)
  exact ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide) (by decide) (by decide)]; exact r0, hK,
    by rw [c 11 (by decide) (by decide) (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide) (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega) (by omega) (by omega)) et hn es,
    defs_frame rD (c 12 (by decide) (by decide) (by decide) (by decide)) (c 27 (by decide) (by decide) (by decide) (by decide)) (c 26 (by decide) (by decide) (by decide) (by decide))
      (fun i a _ => e i (by omega) (by omega) (by omega) (by omega)) et hn es,
    arena_frame rA (c 8 (by decide) (by decide) (by decide) (by decide)) (c 9 (by decide) (by decide) (by decide) (by decide))
      (fun i a _ => e i (by omega) (by omega) (by omega) (by omega)) es,
    fun s hs => by rw [c 25 (by decide) (by decide) (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx hne => by rw [c 29 (by decide) (by decide) (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
    by rw [c 30 (by decide) (by decide) (by decide) (by decide)]; exact r30,
    by rw [c 32 (by decide) (by decide) (by decide) (by decide)]; exact r32, out_frame rO ed⟩

/-- move the cursor in the between-defs representation -/
theorem repZ_cursor {g ts : Buf} {st : St} (R : RepZ g ts st) (p' : UInt64) {rest : List Tok} (hK : TokAt g p' rest) :
    RepZ (bset g 3 p') ts { st with toks := rest } := by
  obtain ⟨hn, hl, _⟩ := repZ_bounds R
  have cells : ∀ i : UInt64, i.toNat ≠ 3 → bget (bset g 3 p') i = bget g i := fun i a => bget_bset' _ _ _ _ (by simp; omega)
  have et : TokAgree g (bset g 3 p') := ⟨cells 7 (by decide), fun i hi => cells i (by omega)⟩
  exact repZ_frame R (fun i a _ _ _ => cells i a) (drop_bset _ _ _ (by decide))
    (by rw [bget_bset_eq _ _ _ _ rfl (by simp; omega)]; exact tokAt_frame et hn hK)

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
    (R : RepZ G ts st) (hx : NameAt G p x) (hj : (bget G 12).toNat < 512)
    (hl : H.length = G.length)
    (ag : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 3 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) → bget H i = bget (openW G p) i)
    (ed : H.drop 184384 = G.drop 184384) (hK : TokAt H (bget H 3) toks')
    (hT : TasksRep H [] fs') (hD : inDefF fs' = true) :
    Rep H ts { st with toks := toks', cur := DefR.fresh x, binds := [], vals := [], arena := [], nx := 0, arm := false } fs' := by
  obtain ⟨hn, hlen, har⟩ := repZ_bounds R
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO⟩ := R
  obtain ⟨d12, dlt, d27, drows, dcur, dz, d0, ds26, ds⟩ := rD
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
    · have c26 : bget H 26 = bget G 26 := cell 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      refine ⟨fun i h1 h2 => ?_, by rw [c26]; exact ds26, fun k h1 h2 => by
        rw [big _ (by rw [shRow0 k h2]; omega)]; exact ds k (by rw [← c26]; exact h1) h2⟩
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

/-! ## task 60 -/
/-- Rep ignores the scratch cells 22 and 31 (the def-lookup result) -/
theorem rep_scratch22 {h h' ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs)
    (e : ∀ i : UInt64, i.toNat ≠ 22 → i.toNat ≠ 31 → bget h' i = bget h i)
    (ed : h'.drop 184384 = h.drop 184384) : Rep h' ts st fs := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have et : TokAgree h h' := ⟨e 7 (by decide) (by decide), fun i hi => e i (by omega) (by omega)⟩
  have es : ShTabAgree h h' := fun i a _ => e i (by omega) (by omega)
  have c : ∀ n : UInt64, n.toNat ≠ 22 → n.toNat ≠ 31 → bget h' n = bget h n := e
  exact ⟨tokensAt_frame rT et rts, rts, by rw [c 0 (by decide) (by decide)]; exact r0,
    by rw [c 3 (by decide) (by decide)]; exact tokAt_frame et hn r3, by rw [c 11 (by decide) (by decide)]; exact r11,
    binds_frame rB (c 4 (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega)) et hn es,
    defs_frame rD (c 12 (by decide) (by decide)) (c 27 (by decide) (by decide)) (c 26 (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega)) et hn es,
    arena_frame rA (c 8 (by decide) (by decide)) (c 9 (by decide) (by decide)) (fun i a _ => e i (by omega) (by omega)) es,
    fun s hs => by rw [c 25 (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx hne => by rw [c 29 (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
    by rw [c 30 (by decide) (by decide)]; exact r30, by rw [c 32 (by decide) (by decide)]; exact r32, out_frame rO ed,
    tasks_frame rK (c 5 (by decide) (by decide)) (fun i _ _ => e i (by omega) (by omega)) et hn es
      (fun i a _ => e i (by omega) (by omega)) rA.2.1⟩

/-- the accepting write: status 2 -/
theorem rep_accept {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) :
    Rep (bset h 0 2) ts { st with acc := true } fs := by
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  have hn : (bget h 7).toNat < 2 ^ 32 := by rw [rT.2.2.2]; simp; omega
  have hl : 184384 ≤ h.length := by rw [rO.1]; omega
  have e : ∀ i : UInt64, i.toNat ≠ 0 → bget (bset h 0 2) i = bget h i := fun i a => bget_bset' _ _ _ _ (by simp; omega)
  have et : TokAgree h (bset h 0 2) := ⟨e 7 (by decide), fun i hi => e i (by omega)⟩
  have es : ShTabAgree h (bset h 0 2) := fun i a _ => e i (by omega)
  exact ⟨tokensAt_frame rT et rts, rts, by rw [bget_bset_eq _ _ _ _ rfl (by simp; omega)]; rfl,
    by rw [e 3 (by decide)]; exact tokAt_frame et hn r3, by rw [e 11 (by decide)]; exact r11,
    binds_frame rB (e 4 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    defs_frame rD (e 12 (by decide)) (e 27 (by decide)) (e 26 (by decide)) (fun i a _ => e i (by omega)) et hn es,
    arena_frame rA (e 8 (by decide)) (e 9 (by decide)) (fun i a _ => e i (by omega)) es,
    fun s hs => by rw [e 25 (by decide)]; exact (r25 s hs).frame es,
    fun x hx hne => by rw [e 29 (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
    by rw [e 30 (by decide)]; exact r30, by rw [e 32 (by decide)]; exact r32, out_frame rO (drop_bset _ _ _ (by decide)),
    tasks_frame rK (e 5 (by decide)) (fun i _ _ => e i (by omega)) et hn es (fun i a _ => e i (by omega)) rA.2.1⟩

/-- a token list at the end of the token region is empty -/
theorem tokAt_end {h : Buf} {p : UInt64} {toks : List Tok} (r : TokAt h p toks) (he : p = bget h 7) : toks = [] := by
  cases r with
  | nil _ => rfl
  | kw _ hp => rw [he] at hp; exact absurd hp (by simp)
  | num _ hp => rw [he] at hp; exact absurd hp (by simp)
  | id _ hn =>
    obtain ⟨_, _, hb⟩ := hn
    rw [he] at hb; omega

/-- task 60's write sequence, as Par1 spells it, is `openW` -/
theorem openW_eq (G : Buf) (x : UInt64) (hj : (bget G 12).toNat < 512) :
    (let h := bset G (d7 + 8 * bget G 12 + 0) x
     let h := bset h (d7 + 8 * bget h 12 + 5) (bget h 27)
     let h := bset h (d7 + 8 * bget h 12 + 2) 0
     bset (bset (bset (bset (bset h 4 0) 8 0) 9 0) 11 0) 30 0) = openW G x := by
  have r0 := rowIdx (bget G 12) hj 0 (by decide)
  have r5 := rowIdx (bget G 12) hj 5 (by decide)
  simp only [show (0 : UInt64).toNat = 0 from rfl, show (5 : UInt64).toNat = 5 from rfl, Nat.add_zero] at r0 r5
  have a12 : bget (bset G (d7 + 8 * bget G 12 + 0) x) 12 = bget G 12 := bget_bset' _ _ _ _ (by rw [r0]; simp; omega)
  have a27 : bget (bset G (d7 + 8 * bget G 12 + 0) x) 27 = bget G 27 := bget_bset' _ _ _ _ (by rw [r0]; simp; omega)
  have b12 : bget (bset (bset G (d7 + 8 * bget G 12 + 0) x) (d7 + 8 * bget G 12 + 5) (bget G 27)) 12 = bget G 12 := by
    rw [bget_bset' _ _ _ _ (by rw [r5]; simp; omega), a12]
  simp only [a12, a27, b12, openW]

theorem drop_openW (G : Buf) (p : UInt64) (hj : (bget G 12).toNat < 512) : (openW G p).drop 184384 = G.drop 184384 := by
  have r0 := rowIdx (bget G 12) hj 0 (by decide)
  have r2 := rowIdx (bget G 12) hj 2 (by decide)
  have r5 := rowIdx (bget G 12) hj 5 (by decide)
  simp only [show (0 : UInt64).toNat = 0 from rfl, show (2 : UInt64).toNat = 2 from rfl, show (5 : UInt64).toNat = 5 from rfl,
    Nat.add_zero] at r0 r2 r5
  unfold openW
  rw [drop_bset _ _ _ (by decide), drop_bset _ _ _ (by decide), drop_bset _ _ _ (by decide), drop_bset _ _ _ (by decide),
    drop_bset _ _ _ (by decide), drop_bset _ _ _ (by rw [r2]; omega), drop_bset _ _ _ (by rw [r5]; omega),
    drop_bset _ _ _ (by rw [r0]; omega)]

/-- cells that agree from 184384 on give equal tails -/
theorem drop_of_cells {h h' : Buf} (hl : h'.length = h.length) (e : ∀ i : UInt64, 184384 ≤ i.toNat → bget h' i = bget h i)
    (h64 : h.length < 2 ^ 64) : h'.drop 184384 = h.drop 184384 := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have := e (184384 + i).toUInt64 (by simp [Nat.toUInt64]; simp at h1; omega)
  simp only [bget, List.getD, Nat.toUInt64] at this
  have hn : (UInt64.ofNat (184384 + i)).toNat = 184384 + i := by
    simp only [UInt64.toNat_ofNat']; simp at h1; omega
  rw [hn] at this
  simp only [List.getElem_drop]
  rw [List.getElem?_eq_getElem (by simp at h1; omega), List.getElem?_eq_getElem (by simp at h2; omega)] at this
  simpa using this

theorem drop_v85 : ∀ (n : Nat) (h : Buf) (a b : UInt64), (v85 n h a b).drop 184384 = h.drop 184384
  | 0, h, a, b => by simp only [v85]; exact drop_bset _ _ _ (by decide)
  | n + 1, h, a, b => by
    simp only [v85]
    split
    · split
      · split
        · split
          · exact drop_bset _ _ _ (by decide)
          · split
            · exact drop_v85 n h _ _
            · exact drop_bset _ _ _ (by decide)
        · exact drop_bset _ _ _ (by decide)
      · exact drop_bset _ _ _ (by decide)
    · exact drop_bset _ _ _ (by decide)

theorem drop_v8 : ∀ (n : Nat) (h : Buf) (j x : UInt64), (v8 n h j x).drop 184384 = h.drop 184384
  | 0, h, j, x => by simp only [v8]; exact drop_bset _ _ _ (by decide)
  | n + 1, h, j, x => by
    simp only [v8]
    split
    · exact drop_bset _ _ _ (by decide)
    · split
      · rw [drop_bset _ _ _ (by decide), drop_v85]
      · rw [drop_v8 n, drop_v85]

/-- **task 60** (`v127`, between defs): validation of the previous def's arena, then either ACCEPT (end of tokens: status 2, the
heap facts the glue needs) or OPEN the next def (`def` NAME, name not yet defined, row capacity) and push 61/73 (`: …` header) or
66 (binders).  `hW`: B's input test mod 2^64; `hI`/`hC`: the pure arena invariants of reachable states; `hne`: def names non-empty. -/
theorem h_defs {h ts : Buf} {st : St} (r : Rep h ts st [.defs]) (hW : IsInpW) (hI : ArenaInv st) (hC : CallInv st)
    (hacc0 : st.acc = false) (hs : bget (step h) 0 ≠ 0) :
    (bget (step h) 0 = 1 → ∃ fr st', stepF .defs st = some (fr, st') ∧ Rep (step h) ts st' fr) ∧
    (bget (step h) 0 = 2 → ∃ st', stepF .defs st = some ([], st') ∧ st'.acc = true ∧
      (step h).length = 184385 + ts.length + st'.out.length ∧ (step h).drop (184385 + ts.length) = st'.out ∧
      DefsRep (step h) st' false) := by
  obtain ⟨RZ, rK0⟩ := repZ_of r
  obtain ⟨hn0, hl0, har0⟩ := repZ_bounds RZ
  obtain ⟨E, _, _⟩ := step_top (ts := ts) rK0 (by omega) hn0 har0
  have R1 : RepZ (bset h 5 ([] : List Frame).length.toUInt64) ts st := by
    have e5 : ∀ i : UInt64, i.toNat ≠ 5 → bget (bset h 5 ([] : List Frame).length.toUInt64) i = bget h i :=
      fun i a5 => bget_bset' h 5 i _ (fun e => a5 (by rw [← e]; rfl))
    have et : TokAgree h (bset h 5 ([] : List Frame).length.toUInt64) := ⟨e5 7 (by decide), fun i hi => e5 i (by omega)⟩
    have := repZ_frame (toks' := st.toks) RZ (fun i _ a5 _ _ => e5 i a5) (drop_bset _ _ _ (by decide))
      (by rw [e5 3 (by decide)]; exact tokAt_frame et hn0 RZ.2.2.2.1)
    exact this
  have g5 : bget (bset h 5 ([] : List Frame).length.toUInt64) 5 = 0 := bget_bset_eq _ _ _ _ rfl (by simp; omega)
  generalize (taskAt h ([] : List Frame).length).a = a at E
  generalize (taskAt h ([] : List Frame).length).b = b at E
  generalize bset h 5 ([] : List Frame).length.toUInt64 = g at E R1 g5
  have ev : step h = v127 g a b := by rw [E]; rfl
  rw [ev] at hs ⊢
  obtain ⟨hn, hlen, har⟩ := repZ_bounds R1
  have rT := R1.1; have rts := R1.2.1; have r3 := R1.2.2.2.1
  have rD := R1.2.2.2.2.2.2.1; have rA := R1.2.2.2.2.2.2.2.1
  have h7 : bget g 7 = ts.length.toUInt64 := rT.2.2.2
  have h7n : (bget g 7).toNat < 2 ^ 24 := by rw [h7]; simp [Nat.toUInt64]; omega
  have s0 : ∀ g' : Buf, bget (bset g' 0 0) 0 = 0 := status_bset0
  -- validation
  have hv : v209 16777216 g 0 = 1 := by
    have h9 : (bget g 9).toNat ≤ 16384 := by rw [rA.1]; exact har
    rcases (v209_eq g (bget g 9).toNat 16777216 0 (by simp) (by simp) (by omega)).2 with e | e
    · exact e
    · exfalso; apply hs; unfold v127; rw [e]; exact s0 g
  have hall := v209_nodeOK hW rA rD hI hC hv
  have c0 : ¬ ((v209 16777216 g 0 == 0) = true) := by rw [hv]; decide
  -- accept
  by_cases hacc : bget g 3 = bget g 7
  · have ca : (bget g 3 == bget g 7) = true := by simp [hacc]
    have htk := tokAt_end r3 hacc
    have ev2 : v127 g a b = bset g 0 2 := by unfold v127; rw [if_neg c0, if_pos ca]
    rw [ev2]
    have L : (bset g 0 2).length = g.length := length_bset _ _ _
    refine ⟨fun e => absurd e (by rw [bget_bset_eq _ _ _ _ rfl (by simp; omega)]; decide), fun _ => ⟨{ st with acc := true }, by simp [stepF, hall, htk], rfl, ?_, ?_, ?_⟩⟩
    · rw [L, R1.2.2.2.2.2.2.2.2.2.2.2.2.1]; simp; omega
    · have := R1.2.2.2.2.2.2.2.2.2.2.2.2.2
      simp only [bset]
      rw [List.drop_set_of_lt (by simp; omega), show 184385 + ts.length = 184384 + ts.length + 1 by omega]; exact this
    · exact defs_frame rD (bget_bset' _ _ _ _ (by decide)) (bget_bset' _ _ _ _ (by decide)) (bget_bset' _ _ _ _ (by decide))
        (fun i a _ => bget_bset' _ _ _ _ (by simp; omega)) ⟨bget_bset' _ _ _ _ (by decide), fun i hi => bget_bset' _ _ _ _ (by simp; omega)⟩ hn
        (fun i a _ => bget_bset' _ _ _ _ (by simp; omega))
  have ca : ¬ ((bget g 3 == bget g 7) = true) := by simpa using hacc
  have hk1 : bget g (d11 + bget g 3 + 0) = 1 := by
    by_cases hc : bget g (d11 + bget g 3 + 0) = 1
    · exact hc
    · exfalso; apply hs; unfold v127; rw [if_neg c0, if_neg ca, if_neg (by simpa using hc)]; exact s0 g
  have c1 : (bget g (d11 + bget g 3 + 0) == 1) = true := by rw [hk1]; rfl
  have hk1' : bget g (d11 + bget g 3) = 1 := by simpa using hk1
  obtain ⟨rest, et1, hK1⟩ := tok_kw (t := 1) r3 rT rts hk1' (by decide) (by decide) (by decide)
  have R2 := repZ_cursor R1 (bget g 3 + 1) hK1
  unfold v127 at hs ⊢
  rw [if_neg c0, if_neg ca, if_pos c1] at hs ⊢
  simp only [] at hs ⊢
  have hl3 : 3 < g.length := by omega
  have g13 : bget (bset g 3 (bget g 3 + 1)) 3 = bget g 3 + 1 := bget_bset_eq _ _ _ _ rfl (by simpa using hl3)
  have tok1 : ∀ i : UInt64, i.toNat ≠ 3 → bget (bset g 3 (bget g 3 + 1)) i = bget g i := fun i a => bget_bset' _ _ _ _ (by simp; omega)
  have r3' := R2.2.2.2.1
  simp only at r3'
  rw [g13] at hs ⊢ r3'
  generalize hg1 : bset g 3 (bget g 3 + 1) = g1 at hs ⊢ R2 tok1 r3'
  generalize hp : bget g 3 + 1 = p at hs ⊢ R2 hK1 r3' hg1
  have hlen1 : g1.length = g.length := by rw [← hg1]; simp [length_bset]
  -- the name token
  have hk14 : bget g1 (d11 + p + 0) = 14 := by
    by_cases hc : bget g1 (d11 + p + 0) = 14
    · exact hc
    · exfalso; apply hs; rw [if_neg (by simpa using hc)]; exact s0 _
  rw [if_pos (by rw [hk14]; rfl)] at hs ⊢
  obtain ⟨nm, r', et2, hnm, hK2⟩ := tok_id r3' R2.1 (by simpa using hk14)
  have h7' : (bget g1 7).toNat < 2 ^ 24 := by rw [tok1 7 (by decide)]; exact h7n
  obtain ⟨hS, hiff⟩ := v8_findD R2.2.2.2.2.2.2.1 h7' (by omega) hnm
  generalize hg2 : v8 16777216 g1 (bget g1 12) p = g2 at hs ⊢ hS hiff
  have hz : bget g2 22 = 0 := by
    by_cases hc : bget g2 22 = 0
    · exact hc
    · exfalso; apply hs; rw [if_neg (by simpa using hc)]; exact s0 _
  rw [if_pos (by rw [hz]; rfl)] at hs ⊢
  have hj : bget g2 12 < 512 := by
    by_cases hc : bget g2 12 < 512
    · exact hc
    · exfalso; apply hs; rw [if_neg hc]; exact s0 _
  rw [if_pos hj] at hs ⊢
  have hfd : findD st.defs (nm.map UInt64.toNat) = none := hiff.mp hz
  have hl2 : g2.length = g.length := by rw [hS.1, hlen1]
  have et12a : TokAgree g1 g2 := ⟨hS.2 7 (by decide) (by decide), fun i hi => hS.2 i (by omega) (by omega)⟩
  have hK2a : TokAt g2 (bget g2 3) rest := by rw [hS.2 3 (by decide) (by decide)]; exact tokAt_frame et12a (repZ_bounds R2).1 R2.2.2.2.1
  have R3 := repZ_frame (toks' := rest) R2 (fun i _ _ a22 a31 => hS.2 i a22 a31) (by rw [← hg2, drop_v8]) hK2a
  have g23 : bget g2 3 = p := by rw [hS.2 3 (by decide) (by decide)]; rw [← hg1]; exact bget_bset_eq _ _ _ _ rfl (by simpa using hl3)
  rw [g23] at hs ⊢
  have hpb : p.toNat + 1 + 2 * nm.length < (bget g1 7).toNat := hnm.2.2
  have hp1 : (p + 1).toNat = p.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hseq : NameSeq g2 (p + 1) nm := nameSeq_same hS (by decide) nm (p + 1) (by rw [hp1]; omega) hnm.2.1
  have g27 : bget g2 7 = bget g1 7 := hS.2 7 (by decide) (by decide)
  have hv86 := v86_skip nm 16777216 g2 (p + 1) hseq (by rw [hp1, g27]; omega) (by omega)
  rw [hv86] at hs ⊢
  have hq' : p + 1 + 2 * nm.length.toUInt64 + 1 = p + 2 + 2 * nm.length.toUInt64 := by grind
  rw [hq'] at hs ⊢
  have et12 : TokAgree g1 g2 := ⟨g27, fun i hi => hS.2 i (by omega) (by omega)⟩
  have hK2' : TokAt g2 (p + 2 + 2 * nm.length.toUInt64) r' := tokAt_frame et12 (by omega) hK2
  have R4 := repZ_cursor R3 _ hK2'
  generalize hq : p + 2 + 2 * nm.length.toUInt64 = q at hs ⊢ R4 hK2'
  have hG12 : bget (bset g2 3 q) 12 = bget g2 12 := bget_bset' _ _ _ _ (by decide)
  have hjG : (bget (bset g2 3 q) 12).toNat < 512 := by rw [hG12]; exact UInt64.lt_iff_toNat_lt.mp hj
  generalize hG : bset g2 3 q = G at hs ⊢ R4 hG12 hjG
  have eW := openW_eq G p hjG
  simp only [] at eW
  rw [eW] at hs ⊢
  have hlG : G.length = g.length := by rw [← hG, length_bset, hl2]
  have G3 : bget G 3 = q := by rw [← hG]; exact bget_bset_eq _ _ _ _ rfl (by rw [hl2]; simpa using hl3)
  have rowne : ∀ i : UInt64, i.toNat < 64 → i.toNat ≠ 4 → i.toNat ≠ 8 → i.toNat ≠ 9 → i.toNat ≠ 11 → i.toNat ≠ 30 →
      bget (openW G p) i = bget G i := fun i hi a4 a8 a9 a11 a30 =>
    openW_other G p hjG i a4 a8 a9 a11 a30 (by omega) (by omega) (by omega)
  have big : ∀ i : UInt64, 184384 ≤ i.toNat → bget (openW G p) i = bget G i := fun i hi =>
    openW_other G p hjG i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have W3 : bget (openW G p) 3 = q := by rw [rowne 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact G3
  rw [W3] at hs ⊢
  have rKG : (bget G 5).toNat = 0 := by
    rw [← hG, bget_bset' _ _ _ _ (by decide), hS.2 5 (by decide) (by decide), ← hg1, bget_bset' _ _ _ _ (by decide), g5]; rfl
  have hW5 : (bget (openW G p) 5).toNat = 0 := by rw [rowne 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rKG
  have hlW : 12352 ≤ (openW G p).length := by rw [openW_len]; omega
  have hn' : (bget G 7).toNat < 2 ^ 32 := (repZ_bounds R4).1
  have hx : NameAt G p (nm.map UInt64.toNat) := by
    have et1G : TokAgree g1 G := ⟨by rw [← hG, bget_bset' _ _ _ _ (by decide)]; exact g27, fun i hi => by
      rw [← hG, bget_bset' _ _ _ _ (by simp; omega)]; exact hS.2 i (by omega) (by omega)⟩
    exact ⟨nm, nameOK_frame et1G (by omega) hnm, rfl⟩
  have rKG' := R4.2.2.2.1
  simp only [G3] at rKG'
  have hqle : q.toNat ≤ (bget G 7).toNat := TokAt.le rKG'
  have hq184 : 184384 ≤ (d11 + q).toNat := by rw [UInt64.toNat_add, d11v]; simp; omega
  have tokq : bget (openW G p) (d11 + q + 0) = bget G (d11 + q) := by rw [UInt64.add_zero]; exact big _ hq184
  have hT0 : TasksRep (bset (openW G p) 3 (q + 1)) [] [] := ⟨by rw [bget_bset' _ _ _ _ (by decide)]; exact hW5, by simp,
    fun k hk => absurd hk (by simp)⟩
  by_cases h8 : bget G (d11 + q) = 8
  · obtain ⟨r2, et3, hK3⟩ := tok_kw (t := 8) rKG' R4.1 R4.2.1 h8 (by decide) (by decide) (by decide)
    have c8 : (bget (openW G p) (d11 + q + 0) == 8) = true := by rw [tokq, h8]; rfl
    rw [if_pos c8]
    have hl0 : 12352 ≤ (bset (openW G p) 3 (q + 1)).length := by rw [length_bset]; exact hlW
    have h70 : (bget (bset (openW G p) 3 (q + 1)) 7).toNat < 2 ^ 32 := by
      rw [bget_bset' _ _ _ _ (by decide), rowne 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn'
    have T1 := tasks_push .afterColon 0 0 hT0 (by simp) hl0 h70 (by simp) trivial
    have hg1 : (bget (bset (openW G p) 3 (q + 1)) 5).toNat < 4096 := by rw [bget_bset' _ _ _ _ (by decide)]; omega
    obtain ⟨L1, _, B1, U1⟩ := v1_eff (bset (openW G p) 3 (q + 1)) 73 0 0 hg1 hl0
    have g05 : (bget (bset (openW G p) 3 (q + 1)) 5).toNat = 0 := by rw [bget_bset' _ _ _ _ (by decide)]; exact hW5
    have T2 := tasks_push .tyAtom 0 0 T1 (by simp) (by rw [show (Frame.afterColon).code.toUInt64 = 73 from rfl, L1]; exact hl0)
      (by rw [show (Frame.afterColon).code.toUInt64 = 73 from rfl, U1 7 (by decide) (Or.inl (by rw [g05]; decide))]; exact h70)
      (by simp) trivial
    simp only [show (Frame.afterColon).code.toUInt64 = 73 from rfl, show (Frame.tyAtom).code.toUInt64 = 61 from rfl] at T2
    have g15 : (bget (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 5).toNat = 1 := by rw [B1, UInt64.toNat_add, g05]; simp
    have hg2 : (bget (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 5).toNat < 4096 := by rw [g15]; decide
    obtain ⟨L2, _, _, U2⟩ := v1_eff (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 61 0 0 hg2 (by rw [L1]; exact hl0)
    have agH : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 3 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) →
        bget (v1 (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 61 0 0) i = bget (openW G p) i := by
      intro i a5 a3 a64
      rw [U2 i a5 (by rw [g15]; omega), U1 i a5 (by rw [g05]; omega), bget_bset' _ _ _ _ (by simp; omega)]
    have H3 : bget (v1 (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 61 0 0) 3 = q + 1 := by
      rw [U2 3 (by decide) (by rw [g15]; decide), U1 3 (by decide) (by rw [g05]; decide)]
      exact bget_bset_eq _ _ _ _ rfl (by rw [openW_len, hlG]; simpa using hl3)
    have etH : TokAgree G (v1 (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 61 0 0) :=
      ⟨by rw [agH 7 (by decide) (by decide) (by decide)]; exact rowne 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
       fun i hi => by rw [agH i (by omega) (by omega) (by omega)]; exact big i hi⟩
    have hK : TokAt (v1 (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 61 0 0) (bget (v1 (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 61 0 0) 3) r2 := by
      rw [H3]; exact tokAt_frame etH hn' hK3
    have ed : (v1 (v1 (bset (openW G p) 3 (q + 1)) 73 0 0) 61 0 0).drop 184384 = G.drop 184384 := by
      rw [drop_v1 _ _ _ _ (by rw [L1, length_bset, openW_len]; omega), drop_v1 _ _ _ _ (by rw [length_bset, openW_len]; omega),
        drop_bset _ _ _ (by decide), drop_openW _ _ hjG]
    have RF := rep_open R4 hx hjG (by rw [L2, L1, length_bset, openW_len]) agH ed hK T2 (by decide)
    refine ⟨fun _ => ⟨_, _, ?_, RF⟩, fun e => absurd e (by rw [RF.2.2.1]; simp [hacc0])⟩
    simp [stepF, hall, et1, et2, et3, hfd]
  · have c8 : ¬ ((bget (openW G p) (d11 + q + 0) == 8) = true) := by rw [tokq]; simpa using h8
    rw [if_neg c8]
    have hT0' : TasksRep (openW G p) [] [] := ⟨hW5, by simp, fun k hk => absurd hk (by simp)⟩
    have h70 : (bget (openW G p) 7).toNat < 2 ^ 32 := by
      rw [rowne 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hn'
    have T1 := tasks_push .binders 0 0 hT0' (by simp) hlW h70 (by simp) trivial
    simp only [show (Frame.binders).code.toUInt64 = 66 from rfl] at T1
    obtain ⟨L1, _, _, U1⟩ := v1_eff (openW G p) 66 0 0 (by rw [hW5]; decide) hlW
    have agH : ∀ i : UInt64, i.toNat ≠ 5 → i.toNat ≠ 3 → (i.toNat < 64 ∨ 12352 ≤ i.toNat) →
        bget (v1 (openW G p) 66 0 0) i = bget (openW G p) i := fun i a5 a3 a64 => U1 i a5 (by rw [hW5]; omega)
    have H3 : bget (v1 (openW G p) 66 0 0) 3 = q := by rw [U1 3 (by decide) (by rw [hW5]; decide)]; exact W3
    have etH : TokAgree G (v1 (openW G p) 66 0 0) :=
      ⟨by rw [agH 7 (by decide) (by decide) (by decide)]; exact rowne 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
       fun i hi => by rw [agH i (by omega) (by omega) (by omega)]; exact big i hi⟩
    have hK : TokAt (v1 (openW G p) 66 0 0) (bget (v1 (openW G p) 66 0 0) 3) r' := by rw [H3]; exact tokAt_frame etH hn' rKG'
    have ed : (v1 (openW G p) 66 0 0).drop 184384 = G.drop 184384 := by
      rw [drop_v1 _ _ _ _ (by rw [openW_len]; omega), drop_openW _ _ hjG]
    have RF := rep_open R4 hx hjG (by rw [L1, openW_len]) agH ed hK T1 (by decide)
    refine ⟨fun _ => ⟨_, _, ?_, RF⟩, fun e => absurd e (by rw [RF.2.2.1]; simp [hacc0])⟩
    have hr' : ∀ r2, r' ≠ Tok.k 8 :: r2 := fun r2 e => h8 (UInt64.toNat_inj.mp (by rw [tok_cell_k rKG' e]; rfl))
    simp only [stepF, hall, et1, et2, hfd, Bool.not_true, Bool.false_eq_true, if_false, UInt64.toNat_ofNat]
    all_goals (try split) <;> (try (rename_i r2 he; exact absurd he (hr' r2))) <;> (try rfl)

end ParInv
