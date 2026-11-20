import Legacy.Nano.V2.Blocks
/- nano v2 small backend: the input invariant (t3/t4 = the immutable input block) **`isize_node`**, and **`iget_node`** (input read:
in range = the byte via `lbu`, out of range = 0, as `List.getD`). -/
namespace Nano.V2B

/-- t3/t4 hold the input block -/
structure InpRep (c : Cfg) (s : St) : Prop where
  ib : (s.get 28).toNat = c.ib
  il : s.get 29 = c.inp.length.toUInt64
  fit : c.ib + c.inp.length < 2 ^ 64

theorem InpRep.keep {c : Cfg} {s s' : St} (h : InpRep c s) (k : Keep s s') : InpRep c s' :=
  ⟨k.ib ▸ h.ib, k.il ▸ h.il, h.fit⟩

def inpW (c : Cfg) : List UInt64 := c.inp.map (·.toUInt64)

/-- **input read** (per-construct lemma): the index pushed by `ci`, replaced by the byte (0 out of range) -/
theorem igetT_ok {c : Cfg} {s2 : St} {h : Nat} {L : List UInt64} {i : UInt64} (hc : c.Good)
    (hs2 : Stk c s2 h (L ++ [i])) (hin2 : InpRep c s2) :
    ∃ s5, SC.Ex c (.seq (.ins [.ld T1 SP 0])
        (.seq (.ite .bltu T1 IL (.ins [.r .add T0 IB T1, .lbu T0 T0 0]) (.ins [mv T0 0])) (.ins [.sd T0 SP 0])))
        s2 (.ok s5) ∧ Stk c s5 h (L ++ [(inpW c).getD i.toNat 0]) ∧ Keep s2 s5 := by
    have hin := hin2
    have e1 := ld_slot hc hs2 T1 0 (by simp)
    rw [show (L ++ [i]).getD ((L ++ [i]).length - 1 - 0) 0 = i by simp] at e1
    let s3 := s2.set T1 i
    have hs3 : Stk c s3 h (L ++ [i]) := hs2.set T1 i (by decide) (by decide)
    have k3 : Keep s2 s3 := Keep.set _ _ _ (by decide) (by decide)
    have g1 : s3.get T1 = i := get_set_eq _ _ _ (by decide)
    have hin3 := hin2.keep k3
    let v := (inpW c).getD i.toNat 0
    -- the branch leaves t0 = v and keeps the stack
    have hbr : ∃ s4, SC.Ex c (.ite .bltu T1 IL (.ins [.r .add T0 IB T1, .lbu T0 T0 0]) (.ins [mv T0 0])) s3 (.ok s4) ∧
        Stk c s4 h (L ++ [i]) ∧ Keep s3 s4 ∧ s4.get T0 = v ∧ s4.get 30 = s3.get 30 := by
      by_cases hlt : i.toNat < c.inp.length
      · have hb : BOp.eval .bltu (s3.get T1) (s3.get IL) = true := by
          simp only [BOp.eval, decide_eq_true_eq, g1, show IL = 29 from rfl, hin3.il, UInt64.lt_iff_toNat_lt]
          rw [UInt64.toNat_ofNat']; have := hin.fit; omega
        let s5 := s3.set T0 (s3.get IB + s3.get T1)
        have ha : (s5.get T0 + UInt64.ofInt 0).toNat = c.ib + i.toNat := by
          simp only [s5]; rw [get_set_eq _ _ _ (by decide), g1, show IB = 28 from rfl]
          have := toNat_addK (s3.get 28 + i) 0 (by rw [UInt64.toNat_add, hin3.ib]; have := hin.fit; omega)
          simp only [Int.natCast_zero] at this; rw [this, UInt64.toNat_add, hin3.ib]; have := hin.fit; omega
        have hok : c.ib ≤ ea s5 T0 0 ∧ ea s5 T0 0 < c.ib + c.inp.length := by
          unfold ea; rw [ha]; omega
        let s6 := s5.set T0 (c.inp.getD (ea s5 T0 0 - c.ib) 0).toUInt64
        have e6 : runL c [.r .add T0 IB T1, .lbu T0 T0 0] s3 = some s6 := by
          simp only [runL, I.run, ROp.eval, Option.bind_some]
          split
          · rfl
          · next hn => exact absurd hok hn
        refine ⟨s6, .iteT hb (.ins e6), ?_, ?_, ?_, ?_⟩
        · exact (hs3.set T0 _ (by decide) (by decide)).set T0 _ (by decide) (by decide)
        · exact (Keep.set _ _ _ (by decide) (by decide)).trans (Keep.set _ _ _ (by decide) (by decide))
            (get_set_ne _ _ _ _ (by decide))
        · simp only [s6]; rw [get_set_eq _ _ _ (by decide)]
          unfold ea; rw [ha, show c.ib + i.toNat - c.ib = i.toNat by omega]
          simp [v, inpW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
        · simp only [s6, s5]; rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide)]
      · have hb : BOp.eval .bltu (s3.get T1) (s3.get IL) = false := by
          simp only [BOp.eval, decide_eq_false_iff_not, g1, show IL = 29 from rfl, hin3.il, UInt64.lt_iff_toNat_lt]
          rw [UInt64.toNat_ofNat']; have := hin.fit; omega
        refine ⟨s3.set T0 (s3.get 0 + UInt64.ofInt 0), .iteF hb (.ins rfl), hs3.set T0 _ (by decide) (by decide),
          Keep.set _ _ _ (by decide) (by decide), ?_, get_set_ne _ _ _ _ (by decide)⟩
        rw [get_set_eq _ _ _ (by decide)]
        simp [v, inpW, List.getD_eq_getElem?_getD, List.getElem?_map, St.get, List.getElem?_eq_none (show c.inp.length ≤ i.toNat by omega)]
        rfl
    obtain ⟨s4, e4, hs4, k4, g4, p4⟩ := hbr
    obtain ⟨s5, e5, hs5, k5, _⟩ := sd_top hc (M := L) (x := i) hs4 T0
    rw [g4] at hs5
    refine ⟨s5, .seq (.ins e1) (.seq e4 (.ins e5)), hs5, ?_⟩
    have hp3 : s3.get 30 = s2.get 30 := get_set_ne _ _ _ _ (by decide)
    exact k3.trans (k4.trans k5 p4) hp3

/-- **input read** (per-construct lemma): the index pushed by `ci`, replaced by the byte (0 out of range) -/
theorem iget_node {c : Cfg} {ci : SC} {s : St} {h : Nat} {L : List UInt64} {i : UInt64} (hc : c.Good)
    (hs : Stk c s h L) (hin : InpRep c s) (hi : ∃ r, SC.Ex c ci s r ∧ Post c s h L [i] r) :
    ∃ r, SC.Ex c (.seq (.seq ci (.ins [.ld T1 SP 0]))
        (.seq (.ite .bltu T1 IL (.ins [.r .add T0 IB T1, .lbu T0 T0 0]) (.ins [mv T0 0])) (.ins [.sd T0 SP 0]))) s r ∧
      Post c s h L [(inpW c).getD i.toNat 0] r := by
  obtain ⟨r, e, p⟩ := hi
  cases r with
  | jmp t s2 => exact ⟨_, .seqJ (.seqJ e), p⟩
  | ok s2 =>
    obtain ⟨hs2, k2⟩ := p
    obtain ⟨s5, e5, hs5, k5⟩ := igetT_ok hc hs2 (hin.keep k2)
    cases e5 with
    | seq e1 e2 => exact ⟨.ok s5, .seq (.seq e e1) e2, hs5, k2.trans k5 (by apply UInt64.toNat.inj; rw [hs2.hp, hs.hp])⟩

/-- **input size** (per-construct lemma) -/
theorem isize_node {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L)
    (hin : InpRep c s) :
    ∃ r, SC.Ex c (.seq (.ins [mv T0 IL]) pushC) s r ∧ Post c s h L [(inpW c).length.toUInt64] r := by
  let s1 := s.set T0 (s.get IL + UInt64.ofInt 0)
  have g : s1.get 5 = (inpW c).length.toUInt64 := by
    show (s.set T0 _).get T0 = _
    rw [get_set_eq _ _ _ (by decide), show IL = 29 from rfl, hin.il]; simp [inpW]; rfl
  have hp := pushC_ok hc (hs.set T0 (s.get IL + UInt64.ofInt 0) (by decide) (by decide))
  rw [g] at hp
  exact pre_ok rfl (hs.set T0 _ (by decide) (by decide)) (Keep.set s T0 _ (by decide) (by decide))
    (get_set_ne _ _ _ _ (by decide)) hp

end Nano.V2B
