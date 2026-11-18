import Nano.V2.OwnP
/- nano v2 increment 5 (buffers): composition of the heap contract `PB` (Nano/V2/Heap.lean) and the node lemmas of
the buffer blocks that write memory (`mk`, `set`, `push`). -/
namespace Nano.V2B

/-- a pure block (memory below the heap top kept, heap top kept) has the heap contract -/
theorem liftP {c : Cfg} {code : SC} {s : St} {h : Nat} {L W : List UInt64} {R : Rg} {τ : Ty} {v : Val} {F : Rg}
    (hs : Stk c s h L) (h8 : h % 8 = 0) (hP : ∃ r, SC.Ex c code s r ∧ Post c s h L W r)
    (hv : ∀ s', Keep s s' → VR c s' τ v W F) (hF : ∀ y, F y → R y) :
    ∃ r, SC.Ex c code s r ∧ PB c s h L R τ v r := by
  obtain ⟨r, e, p⟩ := hP
  refine ⟨r, e, ?_⟩
  cases r with
  | ok s' => exact ⟨h, W, F, Nat.le_refl _, h8, p.1, hv s' p.2, fun y hy => .inl (hF y hy), p.2.toB hs.hp R⟩
  | jmp t _ => exact .inl p

/-- sequencing: a contracted block, then any continuation from its successful states -/
theorem thenB {c : Cfg} {a b : SC} {s : St} {h : Nat} {L : List UInt64} {R : Rg} {τ : Ty} {v : Val}
    {P : Res → Prop} (hP : ∀ t s', t = .oom ∨ t = .cap → P (.jmp t s'))
    (ha : ∃ r, SC.Ex c a s r ∧ PB c s h L R τ v r)
    (hb : ∀ s1, OB c s h L R τ v s1 → ∃ r, SC.Ex c b s1 r ∧ P r) : ∃ r, SC.Ex c (.seq a b) s r ∧ P r := by
  obtain ⟨r, e, p⟩ := ha
  cases r with
  | ok s1 => obtain ⟨r2, e2, p2⟩ := hb s1 p; exact ⟨r2, .seq e e2, p2⟩
  | jmp t s1 => exact ⟨_, .seqJ e, hP t s1 p⟩

theorem PB.abort {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {R : Rg} {τ : Ty} {v : Val} (t : Tg) (s' : St)
    (ht : t = .oom ∨ t = .cap) : PB c s h L R τ v (.jmp t s') := ht

/-- **pairing**: `a` then `b` (on the stack extended by `a`'s words) push the pair of their values -/
theorem pairB {c : Cfg} {a b : SC} {s : St} {h : Nat} {L : List UInt64} {env : List (Ty × Nat)} {vals : List Val}
    {d d1 d2 : List Nat} {Fs : Nat → Rg} {τa τb : Ty} {va vb : Val}
    (he : EnvB c s h L env vals d Fs) (st1 : Step (env.map (·.1)) d d1) (st2 : Step (env.map (·.1)) d1 d2)
    (hl1 : d1.length = d.length)
    (ha : ∃ r, SC.Ex c a s r ∧ PB c s h L (RgC env.length d d1 Fs) τa va r)
    (hb : ∀ s1 h1 W, h ≤ h1 → Stk c s1 h1 (L ++ W) → W.length = τa.size →
      EnvB c s1 h1 (L ++ W) env vals d1 Fs →
      ∃ r, SC.Ex c b s1 r ∧ PB c s1 h1 (L ++ W) (RgC env.length d1 d2 Fs) τb vb r) :
    ∃ r, SC.Ex c (.seq a b) s r ∧ PB c s h L (RgC env.length d d2 Fs) (.prod τa τb) (.pr va vb) r := by
  refine thenB (fun t s' ht => ht) ha ?_
  rintro s1 ⟨h1, W, F, hh1, h81, hs1, hv1, hF1, k1⟩
  have he1 := he.after (M := W) st1 hl1 k1 hh1 h81
  obtain ⟨r, e, p⟩ := hb s1 h1 W hh1 hs1 hv1.len he1
  refine ⟨r, e, ?_⟩
  cases r with
  | jmp t _ => exact p
  | ok s2 =>
    obtain ⟨h2, W', F', hh2, h82, hs2, hv2, hF2, k2⟩ := p
    refine ⟨h2, W ++ W', fun y => F y ∨ F' y, by omega, h82, by simpa using hs2, ?_, ?_, ?_⟩
    · refine ⟨W, W', F, F', rfl, hv1.across he st1 hF1 k2 hh1, hv2, ?_, fun _ => Iff.rfl⟩
      intro y hy hy'
      rcases hF1 y hy with r1 | r1 <;> rcases hF2 y hy' with r2 | r2
      · exact RgC.disj he st1 r1 r2
      · have := r1.low he; omega
      · obtain ⟨k, hk, a0, _, f⟩ := r2
        have : fl d k = 0 := by rcases st1 k with h' | ⟨h', _⟩ <;> omega
        have := he.low k hk (by omega) y f; omega
      · omega
    · rintro y (hy | hy)
      · rcases hF1 y hy with r1 | r1
        · exact .inl (RgC.trans st1 st2 (.inl r1))
        · exact .inr ⟨r1.1, by omega⟩
      · rcases hF2 y hy with r2 | r2
        · exact .inl (RgC.trans st1 st2 (.inr r2))
        · exact .inr ⟨by omega, r2.2⟩
    · exact k1.trans k2 hh1 fun y _ hy => RgC.trans st1 st2 hy

/-- `pop2`: t1 := top, t0 := below, both popped -/
theorem pop2_ok {c : Cfg} {s2 : St} {h : Nat} {L : List UInt64} {x y : UInt64} (hc : c.Good)
    (hs2 : Stk c s2 h (L ++ [x, y])) :
    ∃ s4, runL c pop2 s2 = some s4 ∧ s4.get T0 = x ∧ s4.get T1 = y ∧ Stk c s4 h L ∧ Keep s2 s4 := by
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
  refine ⟨s4, ?_, ?_, ?_, hs4, ?_⟩
  · rw [show pop2 = [.ld T1 SP (8 * ((0 : Nat) : Int))] ++ [.ld T0 SP (8 * ((1 : Nat) : Int))] ++
      [.i .addi SP SP ((8 * [x, y].length : Nat) : Int)] from rfl]
    rw [runL_append, runL_append, e1]; simp only [Option.bind_some]; rw [e2]; rfl
  · simp only [s4, s3]; rw [get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
  · simp only [s4, s3]
    rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
  · refine ⟨?_, ?_, fun _ _ => by simp [s4, s3], by simp [s4, s3]⟩
    all_goals simp only [s4, s3]; repeat rw [get_set_ne _ _ _ _ (by decide)]

theorem ld_top3 {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {A i x : UInt64} (hc : c.Good)
    (hs : Stk c s h (L ++ [A, i, x])) :
    runL c [.ld A4 SP 0, .ld T1 SP 8, .ld T0 SP 16] s = some (((s.set A4 x).set T1 i).set T0 A) := by
  have hl : (L ++ [A, i, x]).length = L.length + 3 := by simp
  have e1 := ld_slot hc hs A4 0 (by omega)
  rw [show (L ++ [A, i, x]).getD ((L ++ [A, i, x]).length - 1 - 0) 0 = x by rw [hl]; simp [List.getD_eq_getElem?_getD]] at e1
  have hs1 := hs.set A4 x (by decide) (by decide)
  have e2 := ld_slot hc hs1 T1 1 (by omega)
  rw [show (L ++ [A, i, x]).getD ((L ++ [A, i, x]).length - 1 - 1) 0 = i by rw [hl]; simp [List.getD_eq_getElem?_getD]] at e2
  have hs2 := hs1.set T1 i (by decide) (by decide)
  have e3 := ld_slot hc hs2 T0 2 (by omega)
  rw [show (L ++ [A, i, x]).getD ((L ++ [A, i, x]).length - 1 - 2) 0 = A by rw [hl]; simp [List.getD_eq_getElem?_getD]] at e3
  rw [show ([.ld A4 SP 0, .ld T1 SP 8, .ld T0 SP 16] : List I) = [.ld A4 SP (8 * ((0 : Nat) : Int))] ++
    [.ld T1 SP (8 * ((1 : Nat) : Int))] ++ [.ld T0 SP (8 * ((2 : Nat) : Int))] from rfl]
  rw [runL_append, runL_append, e1]; simp only [Option.bind_some]; rw [e2]; simp only [Option.bind_some]; exact e3

theorem toNat_ofNat_lt {a : Nat} (h : a < 2 ^ 64) : (UInt64.ofNat a).toNat = a := by
  rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-- **`set`** tail (in place, bounds-checked = `lset`): writes inside the buffer's footprint only -/
theorem setT_ok {c : Cfg} {s1 : St} {h : Nat} {L : List UInt64} {a cap : Nat} {l : List UInt64} {i x : UInt64}
    (hc : c.Good) (hs1 : Stk c s1 h (L ++ [UInt64.ofNat a, i, x])) (hr1 : BufRep c s1 a cap l) (hf : foot a cap ≤ h) :
    ∃ s2 s3, runL c [.ld A4 SP 0, .ld T1 SP 8, .ld T0 SP 16, .i .addi SP SP 16, .ld T2 T0 0] s1 = some s2 ∧
      SC.Ex c (.ite .bltu T1 T2 (.ins [.i .slli T1 T1 3, .r .add T1 T0 T1, .sd A4 T1 16]) (.ins [])) s2 (.ok s3) ∧
      Stk c s3 h (L ++ [UInt64.ofNat a]) ∧ BufRep c s3 a cap (lset l i x) ∧ KeepB s1 s3 h (blk a cap) := by
  have hsp := hs1.hsp; simp at hsp
  have ha : a + 16 + 8 * cap < 2 ^ 62 := by have := hc.hi_lt; unfold foot at hf; omega
  let A := UInt64.ofNat a
  have hA : A.toNat = a := toNat_ofNat_lt (by omega)
  have e3 := ld_top3 hc hs1
  let sa := ((s1.set A4 x).set T1 i).set T0 A
  have hsa : Stk c sa h ((L ++ [A]) ++ [i, x]) := by
    simpa using ((hs1.set A4 x (by decide) (by decide)).set T1 i (by decide) (by decide)).set T0 A (by decide) (by decide)
  have hsb := hsa.popk (M := L ++ [A]) (X := [i, x]) hc
  let sb := sa.set 31 (sa.get 31 + UInt64.ofInt ((8 * [i, x].length : Nat) : Int))
  have gb0 : sb.get T0 = A := by simp only [sb, sa]; rw [get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
  have gb1 : sb.get T1 = i := by
    simp only [sb, sa]; rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
  have gb4 : sb.get A4 = x := by
    simp only [sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)]
    rw [get_set_eq _ _ _ (by decide)]
  have wb : sb.w = s1.w := by simp [sb, sa]
  have e4 := ld_heap hc hsb T2 T0 a (by rw [gb0, hA]) hr1.al hr1.lo (by unfold foot at hf; omega)
  let s2 := sb.set T2 (sb.w a)
  have hs2 : Stk c s2 h (L ++ [A]) := hsb.set T2 _ (by decide) (by decide)
  have g2T2 : s2.get T2 = UInt64.ofNat l.length := by simp only [s2]; rw [get_set_eq _ _ _ (by decide), wb, hr1.hd]
  have g2T1 : s2.get T1 = i := by simp only [s2]; rw [get_set_ne _ _ _ _ (by decide), gb1]
  have g2T0 : s2.get T0 = A := by simp only [s2]; rw [get_set_ne _ _ _ _ (by decide), gb0]
  have g2A4 : s2.get A4 = x := by simp only [s2]; rw [get_set_ne _ _ _ _ (by decide), gb4]
  have w2 : s2.w = s1.w := by simp [s2, wb]
  have k2 : Keep s1 s2 := keep_sets w2 (by simp [s2, sb, sa])
    (by simp only [s2, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)])
    (by simp only [s2, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)])
  have run2 : runL c [.ld A4 SP 0, .ld T1 SP 8, .ld T0 SP 16, .i .addi SP SP 16, .ld T2 T0 0] s1 = some s2 := by
    rw [show ([.ld A4 SP 0, .ld T1 SP 8, .ld T0 SP 16, .i .addi SP SP 16, .ld T2 T0 0] : List I) =
      [.ld A4 SP 0, .ld T1 SP 8, .ld T0 SP 16] ++ [.i .addi SP SP ((8 * [i, x].length : Nat) : Int), .ld T2 T0 0]
      from rfl, runL_append, e3]
    simp only [Option.bind_some, runL]
    rw [show I.run c sa (.i .addi SP SP ((8 * [i, x].length : Nat) : Int)) = some sb from rfl]
    simp only [Option.bind_some]; rw [e4]; rfl
  have hlen : l.length < 2 ^ 20 := by have := hr1.len_le; have := hr1.cap_lt; omega
  refine ⟨s2, ?_⟩; refine Exists.imp (fun _ h => ⟨run2, h⟩) ?_
  by_cases hlt : i.toNat < l.length
  · have hcond : (BOp.bltu).eval (s2.get T1) (s2.get T2) = true := by
      rw [g2T1, g2T2]; simp only [BOp.eval, decide_eq_true_eq]
      rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega)]; exact hlt
    let sc := s2.set T1 (s2.get T1 <<< UInt64.ofNat ((3 : Int).toNat % 64))
    let sd := sc.set T1 (sc.get T0 + sc.get T1)
    have hsh : (s2.get T1 <<< UInt64.ofNat ((3 : Int).toNat % 64)).toNat = 8 * i.toNat := by
      have hI : i.toNat < 2 ^ 20 := by omega
      rw [g2T1, UInt64.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
    have g1 : (sd.get T1).toNat = a + 8 * i.toNat := by
      simp only [sd, sc]
      rw [get_set_eq _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide), g2T0,
        UInt64.toNat_add, hA, hsh]
      have := hr1.len_le; omega
    have hea : ea sd T1 16 = a + 16 + 8 * i.toNat := by
      unfold ea
      rw [show (16 : Int) = ((16 : Nat) : Int) from rfl, toNat_addK _ _ (by rw [g1]; have := hr1.len_le; omega), g1]
      omega
    have hw : c.wok (ea sd T1 16) := by
      rw [hea]; refine ⟨by have := hr1.lo; omega, by have := hs2.hsp; have := hr1.len_le; unfold foot at hf; omega, ?_⟩
      have := hr1.al; omega
    have gdA4 : sd.get A4 = x := by simp only [sd, sc]; repeat rw [get_set_ne _ _ _ _ (by decide)]
                                    exact g2A4
    let se : St := { sd with w := fun j => if j = ea sd T1 16 then sd.get A4 else sd.w j }
    have wd : sd.w = s1.w := by simp [sd, sc, w2]
    have hin : blk a cap (a + 16 + 8 * i.toNat) := ⟨by omega, by have := hr1.len_le; unfold foot; omega⟩
    have hse : Stk c se h (L ++ [A]) := by
      have hsd : Stk c sd h (L ++ [A]) := (hs2.set T1 _ (by decide) (by decide)).set T1 _ (by decide) (by decide)
      refine ⟨hsd.sp, hsd.hp, hsd.hlo, hsd.hsp, fun q hq => ?_⟩
      show (if slotA c q = ea sd T1 16 then _ else sd.w (slotA c q)) = _
      rw [if_neg (by rw [hea]; unfold slotA; have := hsd.hsp; simp at hq this; have := hr1.len_le; unfold foot at hf; omega)]
      exact hsd.slots q hq
    refine ⟨se, .iteT hcond (.ins ?_), hse, ?_, ?_⟩
    · simp only [runL, I.run, IOp.eval, ROp.eval, Option.bind_some]; rw [if_pos hw]; rfl
    · refine ⟨hr1.al, hr1.lo, hr1.cap_lt, by unfold lset; split <;> simp [hr1.len_le], ?_, ?_, ?_⟩
      · show (if a = ea sd T1 16 then _ else sd.w a) = _
        rw [if_neg (by rw [hea]; omega), wd, hr1.hd]; unfold lset; split <;> simp
      · show (if a + 8 = ea sd T1 16 then _ else sd.w (a + 8)) = _
        rw [if_neg (by rw [hea]; omega), wd, hr1.hc]
      · intro j hj
        have hj' : j < l.length := by unfold lset at hj; split at hj <;> simp_all
        show (if a + 16 + 8 * j = ea sd T1 16 then _ else sd.w (a + 16 + 8 * j)) = _
        rw [hea, gdA4]
        unfold lset; rw [if_pos hlt]
        by_cases hji : j = i.toNat
        · subst hji; rw [if_pos rfl]; simp [List.getD_eq_getElem?_getD, hlt]
        · rw [if_neg (by omega), wd, hr1.el j hj']
          simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm hji]
    · refine ⟨?_, ?_, fun y hy hn => ?_, by simp [se, sd, sc, k2.o]⟩
      · show sd.get 28 = _; simp only [sd, sc]; repeat rw [get_set_ne _ _ _ _ (by decide)]
      · show sd.get 29 = _; simp only [sd, sc]; repeat rw [get_set_ne _ _ _ _ (by decide)]
      · show (if y = ea sd T1 16 then _ else sd.w y) = _
        rw [if_neg (fun h' : y = ea sd T1 16 => hn (by rw [h', hea]; exact hin)), wd]
  · have hcond : (BOp.bltu).eval (s2.get T1) (s2.get T2) = false := by
      rw [g2T1, g2T2]; simp only [BOp.eval, decide_eq_false_iff_not]
      rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega)]; exact hlt
    refine ⟨s2, .iteF hcond (.ins rfl), hs2, ?_, k2.toB (by rw [hs1.hp]) _⟩
    have : lset l i x = l := by unfold lset; rw [if_neg hlt]
    rw [this]; exact hr1.frame fun y _ => by rw [w2]

/-- loading the word at `p + k` through a register holding `p` -/
theorem ld_heapK {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L) (rd rs : Nat)
    (p k : Nat) (hp : (s.get rs).toNat = p) (h8 : (p + k) % 8 = 0) (hlo : c.lo ≤ p + k) (hh : p + k + 8 ≤ h) :
    I.run c s (.ld rd rs k) = some (s.set rd (s.w (p + k))) := by
  have hea : ea s rs k = p + k := by
    unfold ea; rw [toNat_addK _ _ (by have := hs.hsp; have := hc.hi_lt; omega), hp]
  have hw : c.wok (p + k) := ⟨hlo, by have := hs.hsp; omega, h8⟩
  simp only [I.run, hea, if_pos hw]

/-- storing at `p + k` through a register holding `p` -/
theorem sd_heapK {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hc : c.Good) (hs : Stk c s h L) (rv rs : Nat)
    (p k : Nat) (hp : (s.get rs).toNat = p) (h8 : (p + k) % 8 = 0) (hlo : c.lo ≤ p + k) (hh : p + k + 8 ≤ h) :
    I.run c s (.sd rv rs k) = some { s with w := fun j => if j = p + k then s.get rv else s.w j } := by
  have hea : ea s rs k = p + k := by
    unfold ea; rw [toNat_addK _ _ (by have := hs.hsp; have := hc.hi_lt; omega), hp]
  have hw : c.wok (p + k) := ⟨hlo, by have := hs.hsp; omega, h8⟩
  simp only [I.run, hea, if_pos hw]

/-- a store below the heap top keeps the stack -/
theorem Stk.store {c : Cfg} {s : St} {h : Nat} {L : List UInt64} (hs : Stk c s h L) (q : Nat) (v : UInt64)
    (hq : q < h) : Stk c { s with w := fun j => if j = q then v else s.w j } h L :=
  ⟨hs.sp, hs.hp, hs.hlo, hs.hsp, fun j hj => by
    show (if slotA c j = q then v else s.w (slotA c j)) = _
    rw [if_neg (by unfold slotA; have := hs.hsp; omega)]; exact hs.slots j hj⟩

/-- **`push`** tail (in place): appends inside the buffer's footprint, or jumps to the capacity abort -/
theorem pushT_ok {c : Cfg} {s1 : St} {h : Nat} {L : List UInt64} {a cap : Nat} {l : List UInt64} {x : UInt64}
    (hc : c.Good) (hs1 : Stk c s1 h (L ++ [UInt64.ofNat a, x])) (hr1 : BufRep c s1 a cap l) (hf : foot a cap ≤ h) :
    ∃ s2, runL c [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .ld T2 T0 0, .ld A4 T0 8] s1 = some s2 ∧
      ((∃ s3, SC.Ex c (.ite .bltu T2 A4 (.ins [.i .slli A5 T2 3, .r .add A5 A5 T0, .sd T1 A5 16, .i .addi T2 T2 1,
          .sd T2 T0 0]) (.jmp .cap)) s2 (.ok s3) ∧
        Stk c s3 h (L ++ [UInt64.ofNat a]) ∧ BufRep c s3 a cap (l ++ [x]) ∧ KeepB s1 s3 h (blk a cap)) ∨
       ∃ s3, SC.Ex c (.ite .bltu T2 A4 (.ins [.i .slli A5 T2 3, .r .add A5 A5 T0, .sd T1 A5 16, .i .addi T2 T2 1,
          .sd T2 T0 0]) (.jmp .cap)) s2 (.jmp .cap s3)) := by
  have hsp := hs1.hsp; simp at hsp
  have ha : a + 16 + 8 * cap < 2 ^ 62 := by have := hc.hi_lt; unfold foot at hf; omega
  let A := UInt64.ofNat a
  have hA : A.toNat = a := toNat_ofNat_lt (by omega)
  have e1 := run1 (ld_slot hc hs1 T1 0 (by simp))
  rw [show (L ++ [A, x]).getD ((L ++ [A, x]).length - 1 - 0) 0 = x by simp] at e1
  have hs1' : Stk c s1 h ((L ++ [A]) ++ [x]) := by simpa using hs1
  let sa := s1.set T1 x
  have hsa : Stk c sa h ((L ++ [A]) ++ [x]) := hs1'.set T1 x (by decide) (by decide)
  have e2 := run1 (ld_slot hc hsa T0 1 (by simp))
  rw [show ((L ++ [A]) ++ [x]).getD (((L ++ [A]) ++ [x]).length - 1 - 1) 0 = A by simp] at e2
  let sb := sa.set T0 A
  have hsb : Stk c sb h ((L ++ [A]) ++ [x]) := hsa.set T0 A (by decide) (by decide)
  let sc := sb.set 31 (sb.get 31 + UInt64.ofInt ((8 : Nat) : Int))
  have hsc : Stk c sc h (L ++ [A]) := hsb.pop1 hc
  have gc0 : sc.get T0 = A := by simp only [sc, sb]; rw [get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
  have gc1 : sc.get T1 = x := by
    simp only [sc, sb, sa]; rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide)]
  have wc : sc.w = s1.w := by simp [sc, sb, sa]
  have e4 := ld_heap hc hsc T2 T0 a (by rw [gc0, hA]) hr1.al hr1.lo (by unfold foot at hf; omega)
  let sd := sc.set T2 (sc.w a)
  have hsd : Stk c sd h (L ++ [A]) := hsc.set T2 _ (by decide) (by decide)
  have gd0 : sd.get T0 = A := by simp only [sd]; rw [get_set_ne _ _ _ _ (by decide), gc0]
  have e5 := ld_heapK hc hsd A4 T0 a 8 (by rw [gd0, hA]) (by have := hr1.al; omega) (by have := hr1.lo; omega)
    (by unfold foot at hf; omega)
  let s2 := sd.set A4 (sd.w (a + 8))
  have hs2 : Stk c s2 h (L ++ [A]) := hsd.set A4 _ (by decide) (by decide)
  have w2 : s2.w = s1.w := by simp [s2, sd, wc]
  have g2T2 : s2.get T2 = UInt64.ofNat l.length := by
    simp only [s2, sd]; rw [get_set_ne _ _ _ _ (by decide), get_set_eq _ _ _ (by decide), wc, hr1.hd]
  have g2A4 : s2.get A4 = UInt64.ofNat cap := by
    simp only [s2]; rw [get_set_eq _ _ _ (by decide)]; simp only [sd, set_w]; rw [wc, hr1.hc]
  have g2T0 : s2.get T0 = A := by simp only [s2]; rw [get_set_ne _ _ _ _ (by decide), gd0]
  have g2T1 : s2.get T1 = x := by simp only [s2, sd]; rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), gc1]
  have k2 : Keep s1 s2 := keep_sets w2 (by simp [s2, sd, sc, sb, sa])
    (by simp only [s2, sd, sc, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)])
    (by simp only [s2, sd, sc, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)])
  have run2 : runL c [.ld T1 SP 0, .ld T0 SP 8, .i .addi SP SP 8, .ld T2 T0 0, .ld A4 T0 8] s1 = some s2 := by
    simp only [runL]
    rw [show I.run c s1 (.ld T1 SP 0) = some sa by simpa using e1]; simp only [Option.bind_some]
    rw [show I.run c sa (.ld T0 SP 8) = some sb by simpa using e2]; simp only [Option.bind_some]
    rw [show I.run c sb (.i .addi SP SP 8) = some sc from rfl]; simp only [Option.bind_some]
    rw [e4]; simp only [Option.bind_some]
    rw [show I.run c sd (.ld A4 T0 8) = some (sd.set A4 (sd.w (a + 8))) from e5]; rfl
  have hlen : l.length < 2 ^ 20 := by have := hr1.len_le; have := hr1.cap_lt; omega
  refine ⟨s2, run2, ?_⟩
  by_cases hlt : l.length < cap
  · left
    have hcond : (BOp.bltu).eval (s2.get T2) (s2.get A4) = true := by
      rw [g2T2, g2A4]; simp only [BOp.eval, decide_eq_true_eq]
      rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by have := hr1.cap_lt; omega)]; exact hlt
    let t1 := s2.set A5 (s2.get T2 <<< UInt64.ofNat ((3 : Int).toNat % 64))
    let t2 := t1.set A5 (t1.get A5 + t1.get T0)
    have hsh : (s2.get T2 <<< UInt64.ofNat ((3 : Int).toNat % 64)).toNat = 8 * l.length := by
      rw [g2T2, UInt64.toNat_shiftLeft, toNat_ofNat_lt (by omega)]; simp [Nat.shiftLeft_eq]; omega
    have t1A5 : t1.get A5 = s2.get T2 <<< UInt64.ofNat ((3 : Int).toNat % 64) := get_set_eq _ _ _ (by decide)
    have t1T0 : t1.get T0 = s2.get T0 := get_set_ne _ _ _ _ (by decide)
    have t1T1 : t1.get T1 = s2.get T1 := get_set_ne _ _ _ _ (by decide)
    have t1T2 : t1.get T2 = s2.get T2 := get_set_ne _ _ _ _ (by decide)
    have t2A5 : t2.get A5 = t1.get A5 + t1.get T0 := get_set_eq _ _ _ (by decide)
    have t2T0 : t2.get T0 = t1.get T0 := get_set_ne _ _ _ _ (by decide)
    have t2T1 : t2.get T1 = t1.get T1 := get_set_ne _ _ _ _ (by decide)
    have t2T2 : t2.get T2 = t1.get T2 := get_set_ne _ _ _ _ (by decide)
    have g2A5 : (t2.get A5).toNat = a + 8 * l.length := by
      rw [t2A5, t1A5, t1T0, g2T0, UInt64.toNat_add, hA, hsh]; omega
    have ht2 : Stk c t2 h (L ++ [A]) := (hs2.set A5 _ (by decide) (by decide)).set A5 _ (by decide) (by decide)
    have e6 := sd_heapK hc ht2 T1 A5 (a + 8 * l.length) 16 g2A5 (by have := hr1.al; omega) (by have := hr1.lo; omega)
      (by unfold foot at hf; omega)
    let t3 : St := { t2 with w := fun j => if j = a + 8 * l.length + 16 then t2.get T1 else t2.w j }
    have ht3 : Stk c t3 h (L ++ [A]) := ht2.store _ _ (by unfold foot at hf; omega)
    let t4 := t3.set T2 (t3.get T2 + UInt64.ofInt 1)
    have ht4 : Stk c t4 h (L ++ [A]) := ht3.set T2 _ (by decide) (by decide)
    have g4T0 : (t4.get T0).toNat = a + 0 := by
      show ((t3.set T2 _).get T0).toNat = _
      rw [get_set_ne _ _ _ _ (by decide)]; show (t2.get T0).toNat = _
      rw [t2T0, t1T0, g2T0, hA]; rfl
    have e7 := sd_heapK hc ht4 T2 T0 a 0 g4T0 (by have := hr1.al; omega) (by have := hr1.lo; omega)
      (by unfold foot at hf; omega)
    let t5 : St := { t4 with w := fun j => if j = a + 0 then t4.get T2 else t4.w j }
    have ht5 : Stk c t5 h (L ++ [A]) := ht4.store _ _ (by unfold foot at hf; omega)
    have g4T2 : t4.get T2 = UInt64.ofNat (l.length + 1) := by
      show (t3.set T2 _).get T2 = _
      rw [get_set_eq _ _ _ (by decide)]; show t2.get T2 + _ = _
      rw [t2T2, t1T2, g2T2]
      apply UInt64.toNat.inj
      rw [show (UInt64.ofInt 1) = UInt64.ofInt ((1 : Nat) : Int) from rfl,
        toNat_addK _ 1 (by rw [toNat_ofNat_lt (show l.length < 2 ^ 64 by omega)]; omega),
        toNat_ofNat_lt (show l.length < 2 ^ 64 by omega), toNat_ofNat_lt (show l.length + 1 < 2 ^ 64 by omega)]
    have g1 : t2.get T1 = x := by rw [t2T1, t1T1, g2T1]
    have w5 : ∀ j, t5.w j = if j = a then UInt64.ofNat (l.length + 1) else
        if j = a + 16 + 8 * l.length then x else s1.w j := by
      intro j; show (if j = a + 0 then t4.get T2 else t4.w j) = _
      rw [g4T2]; simp only [Nat.add_zero]
      split
      · rfl
      · show (if j = a + 8 * l.length + 16 then t2.get T1 else t2.w j) = _
        rw [g1, show a + 8 * l.length + 16 = a + 16 + 8 * l.length by omega]
        split
        · rfl
        · simp [t2, t1, w2]
    refine ⟨t5, .iteT hcond (.ins ?_), ht5, ?_, ?_⟩
    · simp only [runL]
      rw [show I.run c s2 (.i .slli A5 T2 3) = some t1 from rfl]; simp only [Option.bind_some]
      rw [show I.run c t1 (.r .add A5 A5 T0) = some t2 from rfl]; simp only [Option.bind_some]
      rw [show I.run c t2 (.sd T1 A5 16) = some t3 from e6]; simp only [Option.bind_some]
      rw [show I.run c t3 (.i .addi T2 T2 1) = some t4 from rfl]; simp only [Option.bind_some]
      rw [show I.run c t4 (.sd T2 T0 0) = some t5 from e7]; rfl
    · refine ⟨hr1.al, hr1.lo, hr1.cap_lt, by simp; omega, ?_, ?_, ?_⟩
      · rw [w5, if_pos rfl]; simp
      · rw [w5, if_neg (by omega), if_neg (by omega), hr1.hc]
      · intro j hj
        simp only [List.length_append, List.length_cons, List.length_nil] at hj
        rw [w5, if_neg (by omega)]
        by_cases hjl : j = l.length
        · subst hjl; rw [if_pos rfl]; simp [List.getD_eq_getElem?_getD]
        · rw [if_neg (by omega), hr1.el j (by omega)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < l.length by omega)]
    · refine ⟨?_, ?_, fun y hy hn => ?_, ?_⟩
      · show t4.get 28 = _
        rw [show t4.get 28 = t3.get 28 from get_set_ne _ _ _ _ (by decide), show t3.get 28 = t2.get 28 from rfl,
          show t2.get 28 = t1.get 28 from get_set_ne _ _ _ _ (by decide),
          show t1.get 28 = s2.get 28 from get_set_ne _ _ _ _ (by decide)]
        exact k2.ib
      · show t4.get 29 = _
        rw [show t4.get 29 = t3.get 29 from get_set_ne _ _ _ _ (by decide), show t3.get 29 = t2.get 29 from rfl,
          show t2.get 29 = t1.get 29 from get_set_ne _ _ _ _ (by decide),
          show t1.get 29 = s2.get 29 from get_set_ne _ _ _ _ (by decide)]
        exact k2.il
      · rw [w5, if_neg (fun h' : y = a => hn (by rw [h']; exact ⟨Nat.le_refl _, by unfold foot; omega⟩)),
          if_neg (fun h' : y = a + 16 + 8 * l.length => hn (by rw [h']; exact ⟨by omega, by unfold foot; omega⟩))]
      · show t4.o = _; simp [t4, t3, t2, t1, k2.o]
  · right
    have hcond : (BOp.bltu).eval (s2.get T2) (s2.get A4) = false := by
      rw [g2T2, g2A4]; simp only [BOp.eval, decide_eq_false_iff_not]
      rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by have := hr1.cap_lt; omega)]; exact hlt
    exact ⟨s2, .iteF hcond .jmp⟩
  
theorem sd_okK {c : Cfg} {s : St} (rv rs : Nat) (p k : Nat) (hp : (s.get rs).toNat = p) (hk : p + k < 2 ^ 64)
    (hw : c.wok (p + k)) :
    I.run c s (.sd rv rs k) = some { s with w := fun j => if j = p + k then s.get rv else s.w j } := by
  have hea : ea s rs k = p + k := by unfold ea; rw [toNat_addK _ _ (by omega), hp]
  simp only [I.run, hea, if_pos hw]

theorem natToUInt64 (n : Nat) : n.toUInt64 = UInt64.ofNat n := rfl

/-- **`mk cap`**: a fresh empty buffer at the heap top, the heap top moves past its footprint -/
theorem mk_node {c : Cfg} {s : St} {h : Nat} {L : List UInt64} {cap : Nat} (R : Rg) (hc : c.Good)
    (hs : Stk c s h L) (h8 : h % 8 = 0) (hcap : cap < 2 ^ 20) :
    ∃ r, SC.Ex c (.seq (.seq (.ins (mv T0 HP :: li T1 (8 * (cap.toUInt64 + 2)) ++ [.r .add T1 T1 HP]))
        (.ite .bgeu SP T1 (.ins []) (.jmp .oom)))
        (.seq (.ins (li T2 cap.toUInt64 ++ [.sd 0 T0 0, .sd T2 T0 8, mv HP T1])) pushC)) s r ∧
      PB c s h L R .buf (.bf []) r := by
  have hhi := hc.hi_lt
  have hsp0 := hs.hsp
  let n : UInt64 := 8 * (cap.toUInt64 + 2)
  have hn : n.toNat = 8 * cap + 16 := by
    show (8 * (UInt64.ofNat cap + 2)).toNat = _
    rw [UInt64.toNat_mul, UInt64.toNat_add, toNat_ofNat_lt (show cap < 2 ^ 64 by omega)]
    rw [show (8 : UInt64).toNat = 8 from rfl, show (2 : UInt64).toNat = 2 from rfl]; omega
  let H := s.get 30
  have hH : H.toNat = h := hs.hp
  let sa := s.set T0 (s.get HP + UInt64.ofInt 0)
  let sb := sa.set T1 n
  let sc := sb.set T1 (sb.get T1 + sb.get HP)
  have run1 : runL c (mv T0 HP :: li T1 n ++ [.r .add T1 T1 HP]) s = some sc := by
    show runL c ([mv T0 HP] ++ li T1 n ++ [.r .add T1 T1 HP]) s = some sc
    rw [runL_append, runL_append]
    simp only [runL, mv, I.run, IOp.eval, Option.bind_some]
    rw [li_ok c sa T1 (by decide) n]; rfl
  have gsa0 : sa.get T0 = H := by
    simp only [sa]; rw [get_set_eq _ _ _ (by decide)]
    show s.get 30 + UInt64.ofInt 0 = s.get 30; rw [show UInt64.ofInt 0 = 0 from rfl, UInt64.add_zero]
  have gc1 : (sc.get T1).toNat = h + 8 * cap + 16 := by
    simp only [sc, sb]
    rw [get_set_eq _ _ _ (by decide), get_set_eq _ _ _ (by decide), get_set_ne _ _ _ _ (by decide)]
    simp only [sa]; rw [get_set_ne _ _ _ _ (by decide)]
    rw [UInt64.toNat_add, hn, show s.get HP = H from rfl, hH]; omega
  have gc0 : sc.get T0 = H := by
    simp only [sc, sb]; rw [get_set_ne _ _ _ _ (by decide), get_set_ne _ _ _ _ (by decide), gsa0]
  have gcSP : sc.get SP = s.get SP := by
    simp only [sc, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)]
  have wc : sc.w = s.w := by simp [sc, sb, sa]
  have hsc : Stk c sc h L := ((hs.set T0 _ (by decide) (by decide)).set T1 _ (by decide) (by decide)).set T1 _
    (by decide) (by decide)
  by_cases hfit : h + 8 * cap + 16 + 8 * L.length ≤ c.hi
  · have hcond : BOp.eval .bgeu (sc.get SP) (sc.get T1) = true := by
      simp only [BOp.eval, decide_eq_true_eq, UInt64.le_iff_toNat_le, gc1]
      rw [gcSP, show SP = 31 from rfl, hs.sp]; omega
    -- the header stores and the new heap top
    let capW : UInt64 := cap.toUInt64
    let sd := sc.set T2 capW
    have gd0 : (sd.get T0).toNat = h := by simp only [sd]; rw [get_set_ne _ _ _ _ (by decide), gc0, hH]
    have hw0 : c.wok (h + 0) := ⟨by have := hs.hlo; omega, by omega, by omega⟩
    have hw8 : c.wok (h + 8) := ⟨by have := hs.hlo; omega, by omega, by omega⟩
    let se : St := { sd with w := fun j => if j = h + 0 then sd.get 0 else sd.w j }
    let sf : St := { se with w := fun j => if j = h + 8 then se.get T2 else se.w j }
    let sg := sf.set HP (sf.get T1 + UInt64.ofInt 0)
    have run2 : runL c (li T2 cap.toUInt64 ++ [.sd 0 T0 0, .sd T2 T0 8, mv HP T1]) sc = some sg := by
      rw [runL_append, li_ok c sc T2 (by decide)]
      simp only [Option.bind_some, runL]
      rw [show I.run c sd (.sd 0 T0 0) = some se from sd_okK 0 T0 h 0 gd0 (by omega) hw0]
      simp only [Option.bind_some]
      rw [show I.run c se (.sd T2 T0 8) = some sf from sd_okK T2 T0 h 8 gd0 (by omega) hw8]
      rfl
    let h' := h + 8 * cap + 16
    have gg30 : (sg.get 30).toNat = h' := by
      rw [show sg.get 30 = sf.get T1 + UInt64.ofInt 0 from get_set_eq _ _ _ (by decide)]
      show (sc.get T1 + _).toNat = _
      rw [show UInt64.ofInt 0 = 0 from rfl, UInt64.add_zero, gc1]
    have wg : ∀ j, sg.w j = if j = h + 8 then UInt64.ofNat cap else if j = h then 0 else s.w j := by
      intro j; show (if j = h + 8 then se.get T2 else se.w j) = _
      rw [show se.get T2 = UInt64.ofNat cap from by
        show sd.get T2 = _; simp only [sd]; rw [get_set_eq _ _ _ (by decide)]]
      split
      · rfl
      · show (if j = h + 0 then sd.get 0 else sd.w j) = _
        simp only [Nat.add_zero]; split
        · rfl
        · simp [sd, wc]
    have hsg : Stk c sg h' L := by
      refine ⟨?_, gg30, by have := hs.hlo; omega, by omega, fun q hq => ?_⟩
      · simp only [sg, sd]; rw [get_set_ne _ _ _ _ (by decide)]
        show (sd.get 31).toNat = _; simp only [sd]; rw [get_set_ne _ _ _ _ (by decide)]
        rw [show sc.get 31 = s.get 31 from gcSP, hs.sp]
      · rw [wg, if_neg (by unfold slotA; omega), if_neg (by unfold slotA; omega)]; exact hs.slots q hq
    have g5 : sg.get 5 = UInt64.ofNat h := by
      simp only [sg]; rw [get_set_ne _ _ _ _ (by decide)]
      show sd.get 5 = _; simp only [sd]; rw [get_set_ne _ _ _ _ (by decide)]
      rw [show sc.get 5 = H from gc0]; apply UInt64.toNat.inj; rw [hH, toNat_ofNat_lt (by omega)]
    have kg : KeepB s sg h R := by
      refine ⟨?_, ?_, fun y hy _ => ?_, ?_⟩
      · simp only [sg]; rw [get_set_ne _ _ _ _ (by decide)]; show sd.get 28 = _
        simp only [sd, sc, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)]
      · simp only [sg]; rw [get_set_ne _ _ _ _ (by decide)]; show sd.get 29 = _
        simp only [sd, sc, sb, sa]; repeat rw [get_set_ne _ _ _ _ (by decide)]
      · rw [wg, if_neg (by omega), if_neg (by omega)]
      · simp [sg, sf, se, sd, sc, sb, sa]
    obtain ⟨r, e3, p3⟩ := pushC_ok hc hsg
    rw [g5] at p3
    refine ⟨r, .seq (.seq (.ins run1) (.iteT hcond (.ins rfl))) (.seq (.ins run2) e3), ?_⟩
    cases r with
    | jmp t _ => exact .inl p3
    | ok s' =>
      obtain ⟨hs', k'⟩ := p3
      have hm : ∀ y, y < h' → s'.w y = sg.w y := fun y hy => k'.heap y (by rw [gg30]; exact hy)
      refine ⟨h', [UInt64.ofNat h], blk h cap, by omega, by omega, hs', ?_, ?_, ?_⟩
      · refine ⟨h, cap, rfl, ⟨h8, hs.hlo, hcap, by simp, ?_, ?_, fun i hi => by simp at hi⟩, fun _ => Iff.rfl⟩
        · rw [hm h (by omega), wg, if_neg (by omega), if_pos rfl]; rfl
        · rw [hm (h + 8) (by omega), wg, if_pos rfl]
      · intro y hy; exact .inr ⟨hy.1, by have := hy.2; unfold foot at this; omega⟩
      · refine ⟨k'.ib.trans kg.ib, k'.il.trans kg.il, fun y hy hn => ?_, k'.o.trans kg.o⟩
        rw [hm y (by omega)]; exact kg.heap y hy hn
  · have hcond : BOp.eval .bgeu (sc.get SP) (sc.get T1) = false := by
      simp only [BOp.eval, decide_eq_false_iff_not, UInt64.le_iff_toNat_le, gc1]
      rw [gcSP, show SP = 31 from rfl, hs.sp]; omega
    exact ⟨_, .seqJ (.seq (.ins run1) (.iteF hcond .jmp)), .inl rfl⟩

end Nano.V2B
