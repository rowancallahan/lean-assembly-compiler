import Nano.Base.V2.Sem
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

theorem set_set (s : St) (r : Nat) (a b : UInt64) : (s.set r a).set r b = s.set r b := by
  unfold St.set; split
  · rfl
  · simp only [St.mk.injEq, and_true]; funext j; split <;> rfl

theorem shl8 (a : UInt64) : (a <<< UInt64.ofNat (Int.toNat 8 % 64)).toNat = a.toNat * 256 % 2 ^ 64 := by
  rw [show UInt64.ofNat (Int.toNat 8 % 64) = 8 from rfl, UInt64.toNat_shiftLeft]
  simp [Nat.shiftLeft_eq]

theorem li_step (acc : UInt64) (q : Nat) (h : acc.toNat = q / 256) (hq : q < 2 ^ 64) :
    (acc <<< UInt64.ofNat (Int.toNat 8 % 64) + UInt64.ofInt ↑(q % 256)).toNat = q := by
  rw [UInt64.toNat_add, shl8, ofInt_nat, h]; omega

theorem div_succ (q k : Nat) : q / 256 ^ k / 256 = q / 256 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem li_ok (c : Cfg) (s : St) (r : Nat) (hr : r ≠ 0) (n : UInt64) : runL c (li r n) s = some (s.set r n) := by
  unfold li
  split
  · next h =>
    simp only [runL, I.run, IOp.eval, Option.bind_some]
    congr 1; congr 1; unfold St.get; simp only [if_true]
    apply UInt64.toNat.inj; rw [UInt64.toNat_add, ofInt_nat]; simp
  · next h =>
    simp only [List.range, List.range.loop, List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.append_nil, runL, I.run, IOp.eval, Option.bind_some,
      get_set_eq _ _ _ hr, set_set]
    congr 1; congr 1
    unfold St.get; simp only [if_true]
    apply UInt64.toNat.inj
    have hn := n.toNat_lt
    have hk : ∀ k, n.toNat / 256 ^ k < 2 ^ 64 := fun k => Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
    have e0 : n.toNat / 256 ^ 0 = n.toNat := by simp
    conv => rhs; rw [← e0]
    iterate 8 (refine li_step _ _ ?_ (hk _); rw [div_succ])
    show (0 + UInt64.ofInt 0).toNat = n.toNat / 256 ^ (7 + 1)
    rw [show (0 + UInt64.ofInt 0).toNat = 0 from rfl]; simp only [Nat.reduceAdd, Nat.reducePow]; omega
/-- a straight prefix that keeps the stack, then a contracted block -/
theorem pre_ok {c : Cfg} {l : List I} {b : SC} {s s' : St} {h : Nat} {L vs : List UInt64}
    (e : runL c l s = some s') (hs' : Stk c s' h L) (k : Keep s s') (hp : s'.get 30 = s.get 30)
    (hb : ∃ r, SC.Ex c b s' r ∧ Post c s' h L vs r) : ∃ r, SC.Ex c (.seq (.ins l) b) s r ∧ Post c s h L vs r := by
  obtain ⟨r, eb, pb⟩ := hb
  refine ⟨r, .seq (.ins e) eb, ?_⟩
  cases r with
  | ok s2 => exact ⟨pb.1, k.trans pb.2 hp⟩
  | jmp t s2 => exact pb

/-- setting a scratch register keeps the stack -/
theorem Stk.set {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hs : Stk c s h L) (r : Nat) (v : UInt64)
    (h31 : r ≠ 31) (h30 : r ≠ 30) : Stk c (s.set r v) h L where
  sp := by rw [get_set_ne _ _ _ _ (Ne.symm h31)]; exact hs.sp
  hp := by rw [get_set_ne _ _ _ _ (Ne.symm h30)]; exact hs.hp
  hlo := hs.hlo
  hsp := hs.hsp
  slots := by simpa using hs.slots

theorem Keep.set (s : St) (r : Nat) (v : UInt64) (h28 : r ≠ 28) (h29 : r ≠ 29) : Keep s (s.set r v) :=
  ⟨get_set_ne _ _ _ _ (Ne.symm h28), get_set_ne _ _ _ _ (Ne.symm h29), fun _ _ => by simp, by simp⟩

/-- **literal**: pushes `n` -/
theorem lit_ok {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L) (n : UInt64) :
    ∃ r, SC.Ex c (.seq (.ins (li T0 n)) pushC) s r ∧ Post c s h L [n] r := by
  have hp := pushC_ok hc (hs.set T0 n (by decide) (by decide))
  rw [show (s.set T0 n).get 5 = n from get_set_eq _ _ _ (by decide)] at hp
  exact pre_ok (li_ok c s T0 (by decide) n) (hs.set T0 n (by decide) (by decide)) (Keep.set s T0 n (by decide) (by decide))
    (get_set_ne _ _ _ _ (by decide)) hp

/-- loading the slot `o` below the top -/
theorem ld_slot {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L) (rd o : Nat)
    (ho : o < L.length) :
    runL c [.ld rd SP (8 * o)] s = some (s.set rd (L.getD (L.length - 1 - o) 0)) := by
  have hea : ea s SP (8 * o) = slotA c (L.length - 1 - o) := by
    unfold ea slotA
    have := toNat_addK (s.get SP) (8 * o) (by have := hc.hi_lt; have := hs.hsp; simp only [SP]; rw [hs.sp]; omega)
    rw [show ((8 * o : Nat) : Int) = 8 * (o : Int) by push_cast; rfl] at this
    rw [this]; simp only [SP]; rw [hs.sp]; have := hs.hsp; omega
  have hwok : c.wok (ea s SP (8 * o)) := by
    rw [hea]; unfold Cfg.wok slotA; have := hc.hi8; have := hs.hsp; have := hs.hlo; have := hc.lo8; omega
  rw [hea] at hwok
  have hq := hs.slots (L.length - 1 - o) (by omega)
  simp only [runL, I.run, hea, if_pos hwok, Option.bind_some, hq]

/-- the `m` slots from `|M| - 1 - o` on -/
def seg (M : List UInt64) (o m : Nat) : List UInt64 := (M.drop (M.length - 1 - o)).take m

theorem seg_succ (M : List UInt64) (o m : Nat) (x : UInt64) (hm : m + 1 ≤ o + 1) (ho : o < M.length) :
    seg M o (m + 1) = M.getD (M.length - 1 - o) 0 :: seg (M ++ [x]) o m := by
  unfold seg
  rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show M.length - 1 - o < M.length by omega),
    Option.getD_some, List.length_append, List.length_cons, List.length_nil]
  congr 1
  rw [show M.length + 1 - 1 - o = M.length - 1 - o + 1 by omega, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

/-- **variable**: copies the `m ≤ o + 1` slots from `o` below the top -/
theorem varC_ok {c : Cfg} {h : Nat} (hc : c.Good) (o : Nat) (ho : o ≤ 255) :
    ∀ m (M : List UInt64) (s : St), Stk c s h M → o < M.length → m ≤ o + 1 →
      ∃ r, SC.Ex c (varC o m) s r ∧ Post c s h M (seg M o m) r := by
  intro m
  induction m with
  | zero => intro M s hs _ _; exact ⟨_, .ins rfl, by simpa [seg] using hs, Keep.refl s⟩
  | succ m ih =>
    intro M s hs hoM hm
    let x := M.getD (M.length - 1 - o) 0
    have e1 := ld_slot hc hs T0 o hoM
    have hs1 := hs.set T0 x (by decide) (by decide)
    have hp := pushC_ok hc hs1
    rw [show (s.set T0 x).get 5 = x from get_set_eq _ _ _ (by decide)] at hp
    have h1 := pre_ok e1 hs1 (Keep.set s T0 x (by decide) (by decide)) (get_set_ne _ _ _ _ (by decide)) hp
    rw [seg_succ M o m x hm hoM]
    exact seq_ok (A := [x]) h1 (fun s2 hs2 _ => ih (M ++ [x]) s2 hs2 (by simp; omega) (by omega)) hs

end Nano.V2B
