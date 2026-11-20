import Nano.V2.Expr
/- nano v2 small backend, proof layer 2 (continued): per-construct block lemmas on the abstract machine.
`sd_slot` (store to a stack slot), `copies_ok`/**`slide_ok`** (result slots slide over a dropped frame: let, snd,
split, loop exit/next), `Stk.pop1`/`Stk.popk`, `drop_node` (fst), `sd_top`, `binT_ok`, **`bin_node`** (binary operation from its
operands' contracts), **`ite_node`** (branching `if` from the operands' and both branches' contracts). -/
namespace Nano.V2B

theorem getD_set_ne (T : List UInt64) (i q : Nat) (v : UInt64) (h : q ≠ i) : (T.set i v).getD q 0 = T.getD q 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]
theorem getD_set_eq (T : List UInt64) (i : Nat) (v : UInt64) (h : i < T.length) : (T.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

/-- storing a register into the slot `o` below the top -/
theorem sd_slot {c : Cfg} {s : St} {h : Nat} {T : List UInt64} (hc : c.Good) (hs : Stk c s h T) (rs o : Nat)
    (ho : o < T.length) : ∃ s', runL c [.sd rs SP (8 * o)] s = some s' ∧
      Stk c s' h (T.set (T.length - 1 - o) (s.get rs)) ∧ Keep s s' ∧ (∀ r, s'.get r = s.get r) := by
  have H := hs.hsp
  have hea : ea s SP (8 * o) = slotA c (T.length - 1 - o) := by
    unfold ea slotA
    have := toNat_addK (s.get SP) (8 * o) (by have := hc.hi_lt; simp only [SP]; rw [hs.sp]; omega)
    rw [show ((8 * o : Nat) : Int) = 8 * (o : Int) by push_cast; rfl] at this
    rw [this]; simp only [SP]; rw [hs.sp]; omega
  have hwok : c.wok (ea s SP (8 * o)) := by
    rw [hea]; unfold Cfg.wok slotA; have := hc.hi8; have := hs.hlo; have := hc.lo8; omega
  let s' : St := { s with w := fun j => if j = ea s SP (8 * o) then s.get rs else s.w j }
  have e : runL c [.sd rs SP (8 * o)] s = some s' := by simp only [runL, I.run, if_pos hwok, Option.bind_some]; rfl
  have gs : ∀ r, s'.get r = s.get r := fun r => rfl
  refine ⟨s', e, ?_, ?_, gs⟩
  · refine ⟨by rw [gs 31, hs.sp]; simp, by rw [gs 30, hs.hp], hs.hlo, by simpa using H, ?_⟩
    intro q hq; simp only [List.length_set] at hq
    show (if slotA c q = ea s SP (8 * o) then s.get rs else s.w (slotA c q)) = _
    rw [hea]
    by_cases hqe : q = T.length - 1 - o
    · subst hqe; rw [if_pos rfl, getD_set_eq _ _ _ (by omega)]
    · have : slotA c q ≠ slotA c (T.length - 1 - o) := by unfold slotA; omega
      rw [if_neg this, hs.slots q hq, getD_set_ne _ _ _ _ hqe]
  · refine ⟨rfl, rfl, ?_, rfl⟩
    intro a ha
    show (if a = ea s SP (8 * o) then s.get rs else s.w a) = _
    rw [hs.hp] at ha
    have : a ≠ ea s SP (8 * o) := by rw [hea]; unfold slotA; omega
    rw [if_neg this]

theorem slide_get (A B C : List UInt64) (j : Nat) (hj : j < C.length) :
    (A ++ C.take j ++ (B ++ C).drop j).getD (A.length + B.length + j) 0 = C.getD j 0 := by
  have h1 : (A ++ C.take j).length = A.length + j := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h1]; omega), h1, List.getElem?_drop,
    show j + (A.length + B.length + j - (A.length + j)) = B.length + j by omega,
    List.getElem?_append_right (by omega), show B.length + j - B.length = j by omega, ← List.getD_eq_getElem?_getD]

theorem slide_set (A B C : List UInt64) (j : Nat) (hj : j < C.length) :
    (A ++ C.take j ++ (B ++ C).drop j).set (A.length + j) (C.getD j 0) =
      A ++ C.take (j + 1) ++ (B ++ C).drop (j + 1) := by
  have h1 : (A ++ C.take j).length = A.length + j := by simp; omega
  rw [List.set_append_right _ _ (by rw [h1]; omega), h1, Nat.sub_self,
    List.drop_eq_getElem_cons (show j < (B ++ C).length by simp; omega), List.set_cons_zero]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
    List.take_succ_eq_append_getElem hj, List.append_assoc, List.cons_append, List.nil_append]

/-- the copy loop of `slide`: after `j` copies the first `j` result slots sit over `B` -/
theorem copies_ok {c : Cfg} {h : Nat} (hc : c.Good) (A B C : List UInt64) (s : St) (hs : Stk c s h (A ++ B ++ C))
    (hm : B.length ≤ 255) (hk : C.length ≤ 255) :
    ∀ j ≤ C.length, ∃ sj, runL c ((List.range j).flatMap fun (j : Nat) =>
        [I.ld T0 SP (8 * ((C.length : Int) - 1 - (j : Int))),
          I.sd T0 SP (8 * ((C.length : Int) - 1 - (j : Int) + (B.length : Int)))]) s = some sj ∧
      Stk c sj h (A ++ C.take j ++ (B ++ C).drop j) ∧ Keep s sj ∧ sj.get 31 = s.get 31 ∧ sj.get 30 = s.get 30 := by
  intro j
  induction j with
  | zero => intro _; exact ⟨s, rfl, by simpa using hs, Keep.refl s, rfl, rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨sj, ej, hsj, kj, g31, g30⟩ := ih (by omega)
    let T := A ++ C.take j ++ (B ++ C).drop j
    have hT : T.length = A.length + B.length + C.length := by simp [T]; omega
    have e1 := ld_slot hc hsj T0 (C.length - 1 - j) (by show _ < T.length; rw [hT]; omega)
    rw [hT, show A.length + B.length + C.length - 1 - (C.length - 1 - j) = A.length + B.length + j by omega,
      slide_get A B C j (by omega)] at e1
    have hs1 := hsj.set T0 (C.getD j 0) (by decide) (by decide)
    obtain ⟨s2, e2, hs2, k2, g2⟩ := sd_slot hc hs1 T0 (C.length - 1 - j + B.length) (by rw [hT]; omega)
    rw [show (sj.set T0 (C.getD j 0)).get T0 = C.getD j 0 from get_set_eq _ _ _ (by decide)] at hs2
    rw [show T.length - 1 - (C.length - 1 - j + B.length) = A.length + j by omega, slide_set A B C j (by omega)] at hs2
    refine ⟨s2, ?_, hs2, ?_, ?_, ?_⟩
    · rw [List.range_succ, List.flatMap_append, runL_append, ej]; simp only [Option.bind_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      rw [show ([I.ld T0 SP (8 * ((C.length : Int) - 1 - (j : Int))),
          I.sd T0 SP (8 * ((C.length : Int) - 1 - (j : Int) + (B.length : Int)))] : List I) =
        [I.ld T0 SP (8 * ((C.length - 1 - j : Nat) : Int))] ++ [I.sd T0 SP (8 * ((C.length - 1 - j + B.length : Nat) : Int))] by
          simp only [List.cons_append, List.nil_append, I.sd.injEq, I.ld.injEq, List.cons.injEq, and_true, true_and]
          constructor <;> omega]
      rw [runL_append, e1]; simp only [Option.bind_some]; exact e2
    · have k1 : Keep sj (sj.set T0 (C.getD j 0)) := Keep.set _ _ _ (by decide) (by decide)
      exact kj.trans (k1.trans k2 (get_set_ne _ _ _ _ (by decide))) g30
    · rw [g2, get_set_ne _ _ _ _ (by decide), g31]
    · rw [g2, get_set_ne _ _ _ _ (by decide), g30]

/-- dropping the top `|X|` slots -/
theorem Stk.popk {c : Cfg} {s : St} {h : Nat} {M X : List UInt64} (hc : c.Good) (hs : Stk c s h (M ++ X)) :
    Stk c (s.set 31 (s.get 31 + UInt64.ofInt ((8 * X.length : Nat) : Int))) h M where
  sp := by
    have H := hs.hsp; simp only [List.length_append] at H
    rw [get_set_eq _ _ _ (by decide), toNat_addK _ _ (by have := hc.hi_lt; rw [hs.sp]; omega), hs.sp]
    simp only [List.length_append]; omega
  hp := by rw [get_set_ne _ _ _ _ (by decide)]; exact hs.hp
  hlo := hs.hlo
  hsp := by have := hs.hsp; simp at this; omega
  slots := by
    intro q hq; simp only [set_w]; rw [hs.slots q (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hq]

/-- **slide**: the top `|C|` slots move down over the `|B|` slots below them -/
theorem slide_ok {c : Cfg} {h : Nat} (hc : c.Good) (A B C : List UInt64) (s : St) (hs : Stk c s h (A ++ B ++ C))
    (hm : B.length ≤ 255) (hk : C.length ≤ 255) :
    ∃ s', runL c (slide C.length B.length) s = some s' ∧ Stk c s' h (A ++ C) ∧ Keep s s' := by
  unfold slide
  split
  · next h0 =>
    have : B = [] := List.eq_nil_of_length_eq_zero h0
    subst this; exact ⟨s, rfl, by simpa using hs, Keep.refl s⟩
  · next h0 =>
    obtain ⟨sk, ek, hsk, kk, g31, g30⟩ := copies_ok hc A B C s hs hm hk C.length (Nat.le_refl _)
    rw [List.take_length] at hsk
    have hX : ((B ++ C).drop C.length).length = B.length := by simp
    have hsk' := hsk.popk (M := A ++ C) (X := (B ++ C).drop C.length) hc
    rw [hX] at hsk'
    refine ⟨_, ?_, hsk', ?_⟩
    · rw [runL_append, ek]; simp only [Option.bind_some, runL, I.run, IOp.eval]
      congr 2
    · have : Keep sk (sk.set 31 (sk.get 31 + UInt64.ofInt ((8 * B.length : Nat) : Int))) :=
        Keep.set _ _ _ (by decide) (by decide)
      exact kk.trans this g30

/-- dropping the top slot (t6 += 8) -/
theorem Stk.pop1 {c : Cfg} {s : St} {h : Nat} {M : List UInt64} {x : UInt64} (hc : c.Good) (hs : Stk c s h (M ++ [x])) :
    Stk c (s.set 31 (s.get 31 + UInt64.ofInt ((8 : Nat) : Int))) h M where
  sp := by
    rw [get_set_eq _ _ _ (by decide), toNat_addK _ _ (by have := hc.hi_lt; rw [hs.sp]; omega), hs.sp]
    have := hs.hsp; simp at this ⊢; omega
  hp := by rw [get_set_ne _ _ _ _ (by decide)]; exact hs.hp
  hlo := hs.hlo
  hsp := by have := hs.hsp; simp at this; omega
  slots := by
    intro q hq; simp only [set_w]; rw [hs.slots q (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hq]

theorem Stk.hsp' {c : Cfg} {s : St} {h : Nat} {M : List UInt64} {x : UInt64} (hs : Stk c s h (M ++ [x])) :
    h + 8 * (M.length + 1) ≤ c.hi := by have := hs.hsp; simpa using this

/-- overwriting the top slot -/
theorem sd_top {c : Cfg} {s : St} {h : Nat} {M : List UInt64} {x : UInt64} (hc : c.Good) (hs : Stk c s h (M ++ [x]))
    (rs : Nat) : ∃ s', runL c [.sd rs SP 0] s = some s' ∧ Stk c s' h (M ++ [s.get rs]) ∧ Keep s s' ∧
      (∀ r, s'.get r = s.get r) := by
  have H := hs.hsp'
  have hea : ea s SP 0 = slotA c M.length := by
    unfold ea slotA
    have := toNat_addK (s.get SP) 0 (by have := hc.hi_lt; simp only [SP]; rw [hs.sp]; omega)
    simp only [Int.natCast_zero] at this; rw [this]; simp only [SP]; rw [hs.sp]; simp
  have hwok : c.wok (ea s SP 0) := by
    rw [hea]; unfold Cfg.wok slotA; have := hc.hi8; have := hs.hlo; have := hc.lo8; omega
  let s' : St := { s with w := fun j => if j = ea s SP 0 then s.get rs else s.w j }
  have e : runL c [.sd rs SP 0] s = some s' := by simp only [runL, I.run, if_pos hwok, Option.bind_some]; rfl
  have gs : ∀ r, s'.get r = s.get r := fun r => rfl
  refine ⟨s', e, ?_, ?_, gs⟩
  · refine ⟨by rw [gs 31, hs.sp]; simp, by rw [gs 30, hs.hp], hs.hlo, by simpa using H, ?_⟩
    intro q hq; simp only [List.length_append, List.length_cons, List.length_nil] at hq
    show (if slotA c q = ea s SP 0 then s.get rs else s.w (slotA c q)) = _
    rw [hea]
    by_cases hqe : q = M.length
    · subst hqe; simp
    · have : slotA c q ≠ slotA c M.length := by unfold slotA; omega
      rw [if_neg this, hs.slots q (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show q < M.length by omega)]
  · refine ⟨rfl, rfl, ?_, rfl⟩
    intro a ha
    show (if a = ea s SP 0 then s.get rs else s.w a) = _
    rw [hs.hp] at ha
    have : a ≠ ea s SP 0 := by rw [hea]; unfold slotA; omega
    rw [if_neg this]

theorem getD_two (L : List UInt64) (a b : UInt64) :
    (L ++ [a, b]).getD ((L ++ [a, b]).length - 1 - 0) 0 = b ∧ (L ++ [a, b]).getD ((L ++ [a, b]).length - 1 - 1) 0 = a := by
  constructor <;> simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- the tail of a binary operation: pops b, a; pushes `f a b` -/
theorem binT_ok {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {a b : UInt64} (hc : c.Good)
    (hs : Stk c s h (L ++ [a, b])) (f : ROp) :
    ∃ s', runL c [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .r f T0 T0 T1, .sd T0 SP 0] s = some s' ∧
      Stk c s' h (L ++ [f.eval a b]) ∧ Keep s s' := by
  have hl : 1 < (L ++ [a, b]).length := by simp
  have e1 := ld_slot hc hs T1 0 (by omega)
  rw [(getD_two L a b).1] at e1
  have hs1 := hs.set T1 b (by decide) (by decide)
  have e2 := ld_slot hc hs1 T0 1 hl
  rw [(getD_two L a b).2] at e2
  let s2 := (s.set T1 b).set T0 a
  have hs2 : Stk c s2 h ((L ++ [a]) ++ [b]) := by simpa using hs1.set T0 a (by decide) (by decide)
  have hs3 := hs2.pop1 hc
  let s3 := s2.set 31 (s2.get 31 + UInt64.ofInt ((8 : Nat) : Int))
  let s4 := s3.set T0 (f.eval (s3.get T0) (s3.get T1))
  have g0 : s3.get T0 = a := by simp only [s3, s2]; rw [get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
  have g1 : s3.get T1 = b := by
    simp only [s3, s2]; rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
  have hs4 : Stk c s4 h (L ++ [a]) := hs3.set T0 _ (by decide) (by decide)
  obtain ⟨s5, e5, hs5, k5, _⟩ := sd_top hc hs4 T0
  have g4 : s4.get T0 = f.eval a b := by simp only [s4]; rw [get_set_eq _ _ _ (by decide), g0, g1]
  rw [g4] at hs5
  refine ⟨s5, ?_, hs5, ?_⟩
  · have e3 : runL c [.i .addi SP SP 8, .r f T0 T0 T1] s2 = some s4 := rfl
    rw [show ([.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .r f T0 T0 T1, .sd T0 SP 0] : List I) =
      [.ld T1 SP (8 * ((0 : Nat) : Int))] ++ [.ld T0 SP (8 * ((1 : Nat) : Int))] ++
        [.i .addi SP SP 8, .r f T0 T0 T1] ++ [.sd T0 SP 0] from rfl]
    rw [runL_append, runL_append, runL_append, e1]; simp only [Option.bind_some]; rw [e2]
    simp only [Option.bind_some]; rw [e3]; simp only [Option.bind_some]; exact e5
  · have k4 : Keep s s4 := by
      refine ⟨?_, ?_, fun _ _ => by simp [s4, s3, s2], by simp [s4, s3, s2]⟩
      all_goals simp only [s4, s3, s2]; repeat rw [get_set_ne _ _ _ _ (by decide)]
    have hp : s4.get 30 = s.get 30 := by simp only [s4, s3, s2]; repeat rw [get_set_ne _ _ _ _ (by decide)]
    exact k4.trans k5 hp

/-- **binary operation** (per-construct lemma): the operands' contracts give the node's -/
theorem bin_node {c : Cfg} {ca cb : SC} {s : St} {h : Nat} {L : List UInt64} {x y : UInt64} (hc : c.Good)
    (hs : Stk c s h L) (f : ROp)
    (ha : ∃ r, SC.Ex c ca s r ∧ Post c s h L [x] r)
    (hb : ∀ s1, Stk c s1 h (L ++ [x]) → Keep s s1 → ∃ r, SC.Ex c cb s1 r ∧ Post c s1 h (L ++ [x]) [y] r) :
    ∃ r, SC.Ex c (.seq (.seq ca cb) (.ins [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .r f T0 T0 T1, .sd T0 SP 0])) s r ∧
      Post c s h L [f.eval x y] r := by
  obtain ⟨r, e, p⟩ := seq_ok ha hb hs
  cases r with
  | ok s2 =>
    obtain ⟨hs2, k2⟩ := p
    obtain ⟨s3, e3, hs3, k3⟩ := binT_ok hc (by simpa using hs2) f
    refine ⟨.ok s3, .seq e (.ins e3), hs3, k2.trans k3 ?_⟩
    apply UInt64.toNat.inj; rw [hs2.hp, hs.hp]
  | jmp t s2 => exact ⟨_, .seqJ e, p⟩

theorem BOp.ofCmp_eval (k : Cmp) (a b : UInt64) : (BOp.ofCmp k).eval a b = k.eval a b := by
  cases k <;> rfl

/-- **if** (per-construct lemma): condition operands x, y pushed by `ca; cb`, popped, then the taken branch -/
theorem ite_node {c : Cfg} {cab ct ce : SC} {s : St} {h : Nat} {L V V' : List UInt64} {x y : UInt64} (hc : c.Good)
    (hs : Stk c s h L) (k : Cmp)
    (hab : ∃ r, SC.Ex c cab s r ∧ Post c s h L [x, y] r)
    (ht : k.eval x y = true → ∀ s1, Stk c s1 h L → Keep s s1 → ∃ r, SC.Ex c ct s1 r ∧ Post c s1 h L V r)
    (he : k.eval x y = false → ∀ s1, Stk c s1 h L → Keep s s1 → ∃ r, SC.Ex c ce s1 r ∧ Post c s1 h L V' r) :
    ∃ r, SC.Ex c (.seq (.seq cab (.ins pop2)) (.ite (BOp.ofCmp k) T0 T1 ct ce)) s r ∧
      Post c s h L (if k.eval x y then V else V') r := by
  obtain ⟨r, e, p⟩ := hab
  cases r with
  | jmp t s2 => exact ⟨_, .seqJ (.seqJ e), p⟩
  | ok s2 =>
    obtain ⟨hs2, k2⟩ := p
    have hl : 1 < (L ++ [x, y]).length := by simp
    have e1 := ld_slot hc hs2 T1 0 (by omega)
    rw [(getD_two L x y).1] at e1
    have hs1 := hs2.set T1 y (by decide) (by decide)
    have e2 := ld_slot hc hs1 T0 1 hl
    rw [(getD_two L x y).2] at e2
    let s3 := (s2.set T1 y).set T0 x
    have hs3 : Stk c s3 h (L ++ [x, y]) := hs1.set T0 x (by decide) (by decide)
    have hs4 := hs3.popk (M := L) (X := [x, y]) hc
    let s4 := s3.set 31 (s3.get 31 + UInt64.ofInt ((8 * [x, y].length : Nat) : Int))
    have e4 : runL c pop2 s2 = some s4 := by
      rw [show pop2 = [.ld T1 SP (8 * ((0 : Nat) : Int))] ++ [.ld T0 SP (8 * ((1 : Nat) : Int))] ++
        [.i .addi SP SP ((8 * [x, y].length : Nat) : Int)] from rfl]
      rw [runL_append, runL_append, e1]; simp only [Option.bind_some]; rw [e2]; rfl
    have g0 : s4.get T0 = x := by
      simp only [s4, s3]; rw [get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
    have g1 : s4.get T1 = y := by
      simp only [s4, s3]
      rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
    have k4 : Keep s s4 := by
      have : Keep s2 s4 := by
        refine ⟨?_, ?_, fun _ _ => by simp [s4, s3], by simp [s4, s3]⟩
        all_goals simp only [s4, s3]; repeat rw [get_set_ne _ _ _ _ (by decide)]
      exact k2.trans this (by apply UInt64.toNat.inj; rw [hs2.hp, hs.hp])
    have hp4 : s4.get 30 = s.get 30 := by apply UInt64.toNat.inj; rw [hs4.hp, hs.hp]
    have pre : SC.Ex c (.seq cab (.ins pop2)) s (.ok s4) := .seq e (.ins e4)
    cases hk : k.eval x y with
    | true =>
      obtain ⟨r, e5, p5⟩ := ht hk s4 hs4 k4
      refine ⟨r, .seq pre (.iteT (by rw [g0, g1, BOp.ofCmp_eval, hk]) e5), ?_⟩
      cases r with
      | ok s5 => exact ⟨p5.1, k4.trans p5.2 hp4⟩
      | jmp t s5 => exact p5
    | false =>
      obtain ⟨r, e5, p5⟩ := he hk s4 hs4 k4
      refine ⟨r, .seq pre (.iteF (by rw [g0, g1, BOp.ofCmp_eval, hk]) e5), ?_⟩
      cases r with
      | ok s5 => exact ⟨p5.1, k4.trans p5.2 hp4⟩
      | jmp t s5 => exact p5


/-- a block pushing `B ++ C`, then `slide`: pushes `C` (let, snd, split, loop exits) -/
theorem slide_node {c : Cfg} {a : SC} {s : St} {h : Nat} {L B C : List UInt64} (hc : c.Good) (hs : Stk c s h L)
    (hm : B.length ≤ 255) (hk : C.length ≤ 255) (ha : ∃ r, SC.Ex c a s r ∧ Post c s h L (B ++ C) r) :
    ∃ r, SC.Ex c (.seq a (.ins (slide C.length B.length))) s r ∧ Post c s h L C r := by
  obtain ⟨r, e, p⟩ := ha
  cases r with
  | jmp t s2 => exact ⟨_, .seqJ e, p⟩
  | ok s2 =>
    obtain ⟨hs2, k2⟩ := p
    obtain ⟨s3, e3, hs3, k3⟩ := slide_ok hc L B C s2 (by simpa using hs2) hm hk
    exact ⟨.ok s3, .seq e (.ins e3), hs3, k2.trans k3 (by apply UInt64.toNat.inj; rw [hs2.hp, hs.hp])⟩

/-- **let** (per-construct lemma): `v` pushes `V`, the body (on the extended stack) pushes `R` -/
theorem let_node {c : Cfg} {cv cb : SC} {s : St} {h : Nat} {L V R : List UInt64} (hc : c.Good) (hs : Stk c s h L)
    (hm : V.length ≤ 255) (hk : R.length ≤ 255) (hv : ∃ r, SC.Ex c cv s r ∧ Post c s h L V r)
    (hb : ∀ s1, Stk c s1 h (L ++ V) → Keep s s1 → ∃ r, SC.Ex c cb s1 r ∧ Post c s1 h (L ++ V) R r) :
    ∃ r, SC.Ex c (.seq (.seq cv cb) (.ins (slide R.length V.length))) s r ∧ Post c s h L R r :=
  slide_node hc hs hm hk (seq_ok hv hb hs)


/-- a block pushing `A ++ B`, then dropping `B` (the `fst` projection) -/
theorem drop_node {c : Cfg} {a : SC} {s : St} {h : Nat} {L A B : List UInt64} (hc : c.Good) (hs : Stk c s h L)
    (ha : ∃ r, SC.Ex c a s r ∧ Post c s h L (A ++ B) r) :
    ∃ r, SC.Ex c (.seq a (.ins [.i .addi SP SP (8 * (B.length : Int))])) s r ∧ Post c s h L A r := by
  obtain ⟨r, e, p⟩ := ha
  cases r with
  | jmp t s2 => exact ⟨_, .seqJ e, p⟩
  | ok s2 =>
    obtain ⟨hs2, k2⟩ := p
    have hs3 := (show Stk c s2 h ((L ++ A) ++ B) by simpa using hs2).popk (M := L ++ A) (X := B) hc
    refine ⟨_, .seq e (.ins (by simp only [runL, I.run, IOp.eval, Option.bind_some]; push_cast; rfl)), hs3, ?_⟩
    exact k2.trans (Keep.set _ _ _ (by decide) (by decide)) (by apply UInt64.toNat.inj; rw [hs2.hp, hs.hp])

end Nano.V2B
