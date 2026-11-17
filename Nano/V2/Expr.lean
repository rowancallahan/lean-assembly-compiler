import Nano.V2.Sem
/- nano v2 small backend, proof layer 2: blocks of stack code on the abstract machine (Nano/V2/Sem.lean).
The value stack `Stk c s h L`: t6 = hi - 8·|L|, slot q (deepest = 0) at hi - 8(q+1) holds L[q], heap top t5 = h
below the stack. -/
namespace Nano.V2B

/-- the run's blocks: aligned, away from address 0 and from 2^64 -/
structure Cfg.Good (c : Cfg) : Prop where
  lo8 : c.lo % 8 = 0
  hi8 : c.hi % 8 = 0
  lo_pos : 8 ≤ c.lo
  lohi : c.lo ≤ c.hi
  hi_lt : c.hi < 2 ^ 62

def slotA (c : Cfg) (q : Nat) : Nat := c.hi - 8 * (q + 1)

/-- the value stack holds `L` (deepest first) and the heap ends at `h` -/
structure Stk (c : Cfg) (s : St) (h : Nat) (L : List UInt64) : Prop where
  sp : (s.get 31).toNat = c.hi - 8 * L.length
  hp : (s.get 30).toNat = h
  hlo : c.lo ≤ h
  hsp : h + 8 * L.length ≤ c.hi
  slots : ∀ q < L.length, s.w (slotA c q) = L.getD q 0

theorem get_set (s : St) (r j : Nat) (v : UInt64) :
    (s.set r v).get j = if j = r ∧ r ≠ 0 then v else s.get j := by
  unfold St.set St.get
  by_cases h0 : r = 0
  · subst h0; simp
  · by_cases hj : j = r
    · subst hj; simp [h0]
    · simp [hj, h0]

@[simp] theorem set_w (s : St) (r : Nat) (v : UInt64) : (s.set r v).w = s.w := by
  unfold St.set; split <;> rfl
@[simp] theorem set_o (s : St) (r : Nat) (v : UInt64) : (s.set r v).o = s.o := by
  unfold St.set; split <;> rfl

theorem ofInt_nat (k : Nat) : (UInt64.ofInt k).toNat = k % 2 ^ 64 := by
  unfold UInt64.ofInt; simp; omega

theorem toNat_sub8 (a : UInt64) (h : 8 ≤ a.toNat) : (a + UInt64.ofInt (-8)).toNat = a.toNat - 8 := by
  have : (UInt64.ofInt (-8)).toNat = 18446744073709551608 := by decide
  rw [UInt64.toNat_add, this]; have := a.toNat_lt; omega

theorem toNat_addK (a : UInt64) (k : Nat) (h : a.toNat + k < 2 ^ 64) :
    (a + UInt64.ofInt (k : Int)).toNat = a.toNat + k := by
  rw [UInt64.toNat_add, ofInt_nat]; omega

/-- what every stack block keeps: input registers, the heap, the output -/
structure Keep (s s' : St) : Prop where
  ib : s'.get 28 = s.get 28
  il : s'.get 29 = s.get 29
  heap : ∀ a < (s.get 30).toNat, s'.w a = s.w a
  o : s'.o = s.o

theorem Keep.refl (s : St) : Keep s s := ⟨rfl, rfl, fun _ _ => rfl, rfl⟩
theorem Keep.trans {s1 s2 s3 : St} (h₁ : Keep s1 s2) (h₂ : Keep s2 s3) (hp : s2.get 30 = s1.get 30) :
    Keep s1 s3 :=
  ⟨h₂.ib.trans h₁.ib, h₂.il.trans h₁.il, fun a ha => (h₂.heap a (hp ▸ ha)).trans (h₁.heap a ha), h₂.o.trans h₁.o⟩

/-- the uniform expression contract's outcome: `vs` pushed, or out of memory -/
def Post (c : Cfg) (s : St) (h : Nat) (L vs : List UInt64) : Res → Prop
  | .ok s' => Stk c s' h (L ++ vs) ∧ Keep s s'
  | .jmp t _ => t = .oom

/-- sequencing two contracted blocks -/
theorem seq_ok {c : Cfg} {a b : SC} {s : St} {h : Nat} {L A B : List UInt64}
    (ha : ∃ r, SC.Ex c a s r ∧ Post c s h L A r)
    (hb : ∀ s1, Stk c s1 h (L ++ A) → Keep s s1 → ∃ r, SC.Ex c b s1 r ∧ Post c s1 h (L ++ A) B r)
    (hs : Stk c s h L) : ∃ r, SC.Ex c (.seq a b) s r ∧ Post c s h L (A ++ B) r := by
  obtain ⟨r1, e1, p1⟩ := ha
  cases r1 with
  | ok s1 =>
    obtain ⟨st1, k1⟩ := p1
    obtain ⟨r, e2, p2⟩ := hb s1 st1 k1
    refine ⟨r, .seq e1 e2, ?_⟩
    cases r with
    | ok s2 =>
      obtain ⟨st2, k2⟩ := p2
      refine ⟨by simpa using st2, k1.trans k2 ?_⟩
      apply UInt64.toNat.inj; rw [st1.hp, hs.hp]
    | jmp t s2 => exact p2
  | jmp t s1 => exact ⟨_, .seqJ e1, p1⟩

theorem Stk.sp8 {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L) :
    8 ≤ (s.get 31).toNat := by
  have := hs.sp; have := hs.hsp; have := hs.hlo; have := hc.lo_pos; omega

theorem get_set_eq (s : St) (r : Nat) (v : UInt64) (h : r ≠ 0) : (s.set r v).get r = v := by
  rw [get_set, if_pos ⟨rfl, h⟩]
theorem get_set_ne (s : St) (r j : Nat) (v : UInt64) (h : j ≠ r) : (s.set r v).get j = s.get j := by
  rw [get_set, if_neg (fun h' => h h'.1)]

theorem getD_append_lt (L : List UInt64) (v : UInt64) (q : Nat) (h : q < L.length) :
    (L ++ [v]).getD q 0 = L.getD q 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_append_eq (L : List UInt64) (v : UInt64) : (L ++ [v]).getD L.length 0 = v := by
  simp [List.getD_eq_getElem?_getD]

/-- storing `v` at the new top slot of a stack with room for it -/
theorem Stk.push {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hs : Stk c s h L) (v : UInt64)
    (hfit : h + 8 * (L.length + 1) ≤ c.hi) (s' : St) (hsp : (s'.get 31).toNat = c.hi - 8 * (L.length + 1))
    (hhp : s'.get 30 = s.get 30) (hw : s'.w = fun j => if j = slotA c L.length then v else s.w j) :
    Stk c s' h (L ++ [v]) where
  sp := by rw [hsp]; simp
  hp := by rw [hhp, hs.hp]
  hlo := hs.hlo
  hsp := by simp; omega
  slots := by
    intro q hq
    simp only [List.length_append, List.length_cons, List.length_nil] at hq
    rw [hw]
    by_cases hqe : q = L.length
    · subst hqe; simp
    · have hq' : q < L.length := by omega
      have : slotA c q ≠ slotA c L.length := by
        unfold slotA; have := hs.hsp; omega
      simp only [this, if_false]; rw [hs.slots q hq', getD_append_lt _ _ _ hq']

/-- `pushC`: t6 -= 8, bound check, [t6] := t0 -/
theorem pushC_ok {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L) :
    ∃ r, SC.Ex c pushC s r ∧ Post c s h L [s.get 5] r := by
  have h8 := hs.sp8 hc
  let s1 := s.set 31 (s.get 31 + UInt64.ofInt (-8))
  have e1 : runL c [.i .addi SP SP (-8)] s = some s1 := rfl
  have g31 : (s1.get 31).toNat = c.hi - 8 * L.length - 8 := by
    simp only [s1]; rw [get_set_eq _ _ _ (by decide), toNat_sub8 _ h8, hs.sp]
  have g30 : s1.get 30 = s.get 30 := get_set_ne _ _ _ _ (by decide)
  have g5 : s1.get 5 = s.get 5 := get_set_ne _ _ _ _ (by decide)
  by_cases hfit : h + 8 * (L.length + 1) ≤ c.hi
  · have hb : BOp.eval .bgeu (s1.get SP) (s1.get HP) = true := by
      simp only [BOp.eval, decide_eq_true_eq, UInt64.le_iff_toNat_le, SP, HP]
      rw [g31, g30, hs.hp]; omega
    have hea : ea s1 SP 0 = c.hi - 8 * L.length - 8 := by
      unfold ea; have := toNat_addK (s1.get SP) 0 (by have := hc.hi_lt; simp only [SP]; omega)
      simpa [SP, g31] using this
    have hwok : c.wok (ea s1 SP 0) := by
      rw [hea]; unfold Cfg.wok; have := hc.hi8; have := hs.hsp; have := hs.hlo; have := hc.lo8; omega
    let s2 : St := { s1 with w := fun j => if j = ea s1 SP 0 then s1.get T0 else s1.w j }
    have e2 : runL c [.sd T0 SP 0] s1 = some s2 := by
      simp only [runL, I.run, if_pos hwok]; rfl
    refine ⟨.ok s2, SC.Ex.seq (SC.Ex.ins e1) (SC.Ex.seq (SC.Ex.iteT hb (SC.Ex.ins rfl)) (SC.Ex.ins e2)), ?_, ?_⟩
    · refine hs.push _ hfit s2 ?_ ?_ ?_
      · show (s1.get 31).toNat = _; rw [g31]; omega
      · exact g30
      · show (fun j => if j = ea s1 SP 0 then s1.get T0 else s1.w j) = _
        funext j; rw [hea, show T0 = 5 from rfl, g5]
        have : slotA c L.length = c.hi - 8 * L.length - 8 := by unfold slotA; omega
        rw [this]; simp [s1]
    · refine ⟨?_, ?_, ?_, rfl⟩
      · show s1.get 28 = _; exact get_set_ne _ _ _ _ (by decide)
      · show s1.get 29 = _; exact get_set_ne _ _ _ _ (by decide)
      · intro a ha; show (if a = ea s1 SP 0 then _ else s1.w a) = _
        rw [hs.hp] at ha
        have hne : a ≠ ea s1 SP 0 := by rw [hea]; omega
        rw [if_neg hne]; simp [s1]
  · have hb : BOp.eval .bgeu (s1.get SP) (s1.get HP) = false := by
      simp only [BOp.eval, decide_eq_false_iff_not, UInt64.le_iff_toNat_le, SP, HP]
      rw [g31, g30, hs.hp]; have := hs.hlo; have := hc.lo_pos; have := hs.hsp; omega
    exact ⟨_, SC.Ex.seq (SC.Ex.ins e1) (SC.Ex.seqJ (SC.Ex.iteF hb SC.Ex.jmp)), rfl⟩

end Nano.V2B
