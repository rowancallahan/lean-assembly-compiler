import Nano.V2.Comp
/- nano v2 increment 5 (buffers), proof layer: the buffer REPRESENTATION on the abstract machine (Nano/V2/Sem.lean),
after Testing/notes/NANO_V2_SKELETONS6.lean `Round6.MultiBuffer` (`BufferRep`, footprints, `SameOutside`), and the
node lemmas of the buffer blocks of `cE` (Nano/V2/Gen.lean).  Layout: `[len][cap][cap data words]` at `a`.
Here: the BORROW nodes (`size`, `get`: memory unchanged).  Next: `set`/`push` (one footprint changes,
`SameOutside`), `mk` (the heap top grows), then the generalised `Post`/`EnvRep` for `cE_ok`. -/
namespace Nano.V2B

/-- the buffer `l` (capacity `cap`) at address `a` -/
structure BufRep (c : Cfg) (s : St) (a cap : Nat) (l : List UInt64) : Prop where
  al : a % 8 = 0
  lo : c.lo ≤ a
  cap_lt : cap < 2 ^ 20
  len_le : l.length ≤ cap
  hd : s.w a = UInt64.ofNat l.length
  hc : s.w (a + 8) = UInt64.ofNat cap
  el : ∀ i < l.length, s.w (a + 16 + 8 * i) = l.getD i 0

/-- the end of the footprint `[a, a + 16 + 8·cap)` -/
def foot (a cap : Nat) : Nat := a + 16 + 8 * cap

/-- a buffer below the heap top survives every block that keeps the heap -/
theorem BufRep.keep {c : Cfg} {s s' : St} {a cap : Nat} {l : List UInt64} (hr : BufRep c s a cap l)
    (hf : foot a cap ≤ (s.get 30).toNat) (k : Keep s s') : BufRep c s' a cap l where
  al := hr.al
  lo := hr.lo
  cap_lt := hr.cap_lt
  len_le := hr.len_le
  hd := by rw [k.heap a (by unfold foot at hf; omega)]; exact hr.hd
  hc := by rw [k.heap (a + 8) (by unfold foot at hf; omega)]; exact hr.hc
  el := fun i hi => by
    rw [k.heap _ (by have := hr.len_le; unfold foot at hf; omega)]; exact hr.el i hi

theorem run1 {c : Cfg} {i : I} {s s' : St} (e : runL c [i] s = some s') : i.run c s = some s' := by
  simp only [runL] at e
  cases h : i.run c s with
  | none => rw [h] at e; simp at e
  | some x => rw [h] at e; simpa using e

/-- loading the word at address `p` (a word inside the heap) through register `rs` holding `p` -/
theorem ld_heap {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L) (rd rs : Nat)
    (p : Nat) (hp : (s.get rs).toNat = p) (h8 : p % 8 = 0) (hlo : c.lo ≤ p) (hh : p + 8 ≤ h) :
    I.run c s (.ld rd rs 0) = some (s.set rd (s.w p)) := by
  have hea : ea s rs 0 = p := by
    unfold ea; rw [show UInt64.ofInt (0 : Int) = 0 from rfl, UInt64.add_zero, hp]
  have hw : c.wok p := ⟨hlo, by have := hs.hsp; omega, h8⟩
  simp only [I.run, hea, if_pos hw]

/-- **`size`** (borrow): the block `cb` pushes the buffer's address -/
theorem size_node {c : Cfg} {cb : SC} {s : St} {h : Nat} {L : List UInt64} {a cap : Nat} {l : List UInt64}
    (hc : c.Good) (hs : Stk c s h L) (hr : BufRep c s a cap l) (hf : foot a cap ≤ h)
    (hb : ∃ r, SC.Ex c cb s r ∧ Post c s h L [UInt64.ofNat a] r) :
    ∃ r, SC.Ex c (.seq cb (.ins [.ld T0 SP 0, .ld T0 T0 0, .sd T0 SP 0])) s r ∧
      Post c s h L [l.length.toUInt64] r := by
  obtain ⟨r, e, p⟩ := hb
  cases r with
  | jmp t s1 => exact ⟨_, .seqJ e, p⟩
  | ok s1 =>
    obtain ⟨hs1, k1⟩ := p
    have hr1 := hr.keep (by rw [hs.hp]; exact hf) k1
    have ha : a < 2 ^ 64 := by have := hs.hsp; have := hc.hi_lt; unfold foot at hf; omega
    have e1 := run1 (ld_slot hc hs1 T0 0 (by simp))
    rw [show (L ++ [UInt64.ofNat a]).getD ((L ++ [UInt64.ofNat a]).length - 1 - 0) 0 = UInt64.ofNat a by simp] at e1
    let s2 := s1.set T0 (UInt64.ofNat a)
    have hs2 : Stk c s2 h (L ++ [UInt64.ofNat a]) := hs1.set T0 _ (by decide) (by decide)
    have e2 := ld_heap hc hs2 T0 T0 a
      (by simp only [s2]; rw [get_set_eq _ _ _ (by decide), UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha])
      hr1.al hr1.lo (by unfold foot at hf; omega)
    let s3 := s2.set T0 (s2.w a)
    have hs3 : Stk c s3 h (L ++ [UInt64.ofNat a]) := hs2.set T0 _ (by decide) (by decide)
    obtain ⟨s4, e3, hs4, k4, _⟩ := sd_top hc hs3 T0
    have g3 : s3.get T0 = l.length.toUInt64 := by
      simp only [s3, s2]; rw [get_set_eq _ _ _ (by decide)]; simp only [set_w]; rw [hr1.hd]
    rw [g3] at hs4
    have k3 : Keep s1 s3 :=
      (Keep.set s1 T0 _ (by decide) (by decide)).trans (Keep.set s2 T0 _ (by decide) (by decide))
        (get_set_ne _ _ _ _ (by decide))
    have e1' : I.run c s1 (I.ld T0 SP 0) = some s2 := by simpa using e1
    have run3 : runL c [.ld T0 SP 0, .ld T0 T0 0, .sd T0 SP 0] s1 = some s4 := by
      simp only [runL]; rw [e1']; simp only [Option.bind_some]; rw [e2]; simp only [Option.bind_some]
      rw [show s2.set T0 (s2.w a) = s3 from rfl, run1 e3]; rfl
    refine ⟨_, .seq e (.ins run3), hs4, ?_⟩
    exact (k1.trans k3 (hp_eq hs hs1)).trans k4 (hp_eq hs hs3)

theorem keep_sets {s1 s2 : St} (hw : s2.w = s1.w) (ho : s2.o = s1.o) (h28 : s2.get 28 = s1.get 28)
    (h29 : s2.get 29 = s1.get 29) : Keep s1 s2 :=
  ⟨h28, h29, fun _ _ => by rw [hw], ho⟩

/-- **`get`** (borrow, bounds-checked: `l.getD i 0`): `cab` pushes the address and the index -/
theorem get_node {c : Cfg} {cab : SC} {s : St} {h : Nat} {L : List UInt64} {a cap : Nat} {l : List UInt64}
    {i : UInt64} (hc : c.Good) (hs : Stk c s h L) (hr : BufRep c s a cap l) (hf : foot a cap ≤ h)
    (hab : ∃ r, SC.Ex c cab s r ∧ Post c s h L [UInt64.ofNat a, i] r) :
    ∃ r, SC.Ex c (.seq (.seq cab (.ins [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .ld T2 T0 0]))
        (.seq (.ite .bltu T1 T2 (.ins [.i .slli T1 T1 3, .r .add T0 T0 T1, .ld T0 T0 16]) (.ins [mv T0 0]))
          (.ins [.sd T0 SP 0]))) s r ∧
      Post c s h L [l.getD i.toNat 0] r := by
  obtain ⟨r, e, p⟩ := hab
  cases r with
  | jmp t s1 => exact ⟨_, .seqJ (.seqJ e), p⟩
  | ok s1 =>
    obtain ⟨hs1, k1⟩ := p
    have hr1 := hr.keep (by rw [hs.hp]; exact hf) k1
    have ha : a + 16 + 8 * cap < 2 ^ 62 := by have := hs.hsp; have := hc.hi_lt; unfold foot at hf; omega
    let A := UInt64.ofNat a
    have hA : A.toNat = a := by simp only [A, UInt64.toNat_ofNat']; omega
    have hs1' : Stk c s1 h ((L ++ [A]) ++ [i]) := by simpa using hs1
    have e1 := run1 (ld_slot hc hs1 T1 0 (by simp))
    rw [show (L ++ [UInt64.ofNat a, i]).getD ((L ++ [UInt64.ofNat a, i]).length - 1 - 0) 0 = i by simp] at e1
    let s2 := s1.set T1 i
    have hs2 : Stk c s2 h ((L ++ [A]) ++ [i]) := hs1'.set T1 i (by decide) (by decide)
    have e2 := run1 (ld_slot hc hs2 T0 1 (by simp))
    rw [show ((L ++ [A]) ++ [i]).getD (((L ++ [A]) ++ [i]).length - 1 - 1) 0 = A by simp] at e2
    let s3 := s2.set T0 A
    have hs3 : Stk c s3 h ((L ++ [A]) ++ [i]) := hs2.set T0 A (by decide) (by decide)
    let s4 := s3.set 31 (s3.get 31 + UInt64.ofInt ((8 : Nat) : Int))
    have hs4 : Stk c s4 h (L ++ [A]) := hs3.pop1 hc
    have e3 : I.run c s3 (.i .addi SP SP 8) = some s4 := rfl
    have g4T0 : s4.get T0 = A := by
      simp only [s4, s3]; rw [get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
    have g4T1 : s4.get T1 = i := by
      simp only [s4, s3, s2]
      rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
    have w4 : s4.w = s1.w := by simp [s4, s3, s2]
    have e4 := ld_heap hc hs4 T2 T0 a (by rw [g4T0, hA]) hr1.al hr1.lo (by unfold foot at hf; omega)
    let s5 := s4.set T2 (s4.w a)
    have hs5 : Stk c s5 h (L ++ [A]) := hs4.set T2 _ (by decide) (by decide)
    have g5T2 : s5.get T2 = UInt64.ofNat l.length := by
      simp only [s5]; rw [get_set_eq _ _ _ (by decide), w4, hr1.hd]
    have g5T1 : s5.get T1 = i := by simp only [s5]; rw [get_set_ne _ _ _ _ (by decide), g4T1]
    have g5T0 : s5.get T0 = A := by simp only [s5]; rw [get_set_ne _ _ _ _ (by decide), g4T0]
    have w5 : s5.w = s1.w := by simp [s5, w4]
    have k5 : Keep s1 s5 := keep_sets w5 (by simp [s5, s4, s3, s2])
      (by simp only [s5, s4, s3, s2]; repeat rw [get_set_ne _ _ _ _ (by decide)])
      (by simp only [s5, s4, s3, s2]; repeat rw [get_set_ne _ _ _ _ (by decide)])
    have e1' : I.run c s1 (.ld T1 SP 0) = some s2 := by simpa using e1
    have e2' : I.run c s2 (.ld T0 SP 8) = some s3 := by simpa using e2
    have run4 : runL c [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .ld T2 T0 0] s1 = some s5 := by
      simp only [runL]; rw [e1']; simp only [Option.bind_some]; rw [e2']; simp only [Option.bind_some]
      rw [e3]; simp only [Option.bind_some]; rw [e4]; rfl
    have hlen : l.length < 2 ^ 20 := by have := hr1.len_le; have := hr1.cap_lt; omega
    -- the branch: T0 := the element (in range) or 0
    have br : ∃ s6, SC.Ex c (.ite .bltu T1 T2 (.ins [.i .slli T1 T1 3, .r .add T0 T0 T1, .ld T0 T0 16])
        (.ins [mv T0 0])) s5 (.ok s6) ∧ s6.get T0 = l.getD i.toNat 0 ∧ Stk c s6 h (L ++ [A]) ∧ Keep s5 s6 := by
      by_cases hlt : i.toNat < l.length
      · have hcond : (BOp.bltu).eval (s5.get T1) (s5.get T2) = true := by
          rw [g5T1, g5T2]; simp only [BOp.eval, decide_eq_true_eq]
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hlt
        let sa := s5.set T1 (s5.get T1 <<< UInt64.ofNat ((3 : Int).toNat % 64))
        let sb := sa.set T0 (sa.get T0 + sa.get T1)
        have hsh : (s5.get T1 <<< UInt64.ofNat ((3 : Int).toNat % 64)).toNat = 8 * i.toNat := by
          have hI : i.toNat < 2 ^ 20 := by omega
          rw [g5T1, UInt64.toNat_shiftLeft]
          simp [Nat.shiftLeft_eq]
          omega
        have g0 : (sb.get T0).toNat = a + 8 * i.toNat := by
          simp only [sb, sa]
          rw [get_set_eq _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide), g5T0,
            UInt64.toNat_add, hA, hsh]
          have := hr1.len_le; omega
        have hea : ea sb T0 16 = a + 16 + 8 * i.toNat := by
          unfold ea
          rw [show (16 : Int) = ((16 : Nat) : Int) from rfl, toNat_addK _ _ (by rw [g0]; have := hr1.len_le; omega),
            g0]; omega
        have hw : c.wok (ea sb T0 16) := by
          rw [hea]; refine ⟨by have := hr1.lo; omega, by have := hs5.hsp; have := hr1.len_le; unfold foot at hf; omega, ?_⟩
          have := hr1.al; omega
        let sc := sb.set T0 (sb.w (ea sb T0 16))
        have wb : sb.w = s1.w := by simp [sb, sa, w5]
        refine ⟨sc, .iteT hcond (.ins ?_), ?_, ?_, ?_⟩
        · simp only [runL, I.run, IOp.eval, ROp.eval, Option.bind_some]; rw [if_pos hw]; rfl
        · simp only [sc]; rw [get_set_eq _ _ _ (by decide), hea, wb, hr1.el _ hlt]
        · exact ((hs5.set T1 _ (by decide) (by decide)).set T0 _ (by decide) (by decide)).set T0 _
            (by decide) (by decide)
        · exact keep_sets (by simp [sc, sb, sa]) (by simp [sc, sb, sa])
            (by simp only [sc, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)])
            (by simp only [sc, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)])
      · have hcond : (BOp.bltu).eval (s5.get T1) (s5.get T2) = false := by
          rw [g5T1, g5T2]; simp only [BOp.eval, decide_eq_false_iff_not]
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hlt
        let sa := s5.set T0 (s5.get 0 + UInt64.ofInt 0)
        refine ⟨sa, .iteF hcond (.ins rfl), ?_, hs5.set T0 _ (by decide) (by decide),
          Keep.set s5 T0 _ (by decide) (by decide)⟩
        simp only [sa]; rw [get_set_eq _ _ _ (by decide)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show l.length ≤ i.toNat by omega)]; rfl
    obtain ⟨s6, e6, g6, hs6, k6⟩ := br
    obtain ⟨s7, e7, hs7, k7, _⟩ := sd_top hc hs6 T0
    rw [g6] at hs7
    refine ⟨_, .seq (.seq e (.ins run4)) (.seq e6 (.ins e7)), hs7, ?_⟩
    exact ((k1.trans k5 (hp_eq hs hs1)).trans k6 (hp_eq hs hs5)).trans k7 (hp_eq hs hs6)

end Nano.V2B
