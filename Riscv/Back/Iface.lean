/- The RISC-V back end: the Sail RV64 model as a `Machine` (`Proven/Mach/Iface.lean`).
Abstract registers `r0 .. r10 = t0 .. t6, a4 .. a7` (`T`), `r11 .. r14 = a0 .. a3` (`A`); every abstract
operation is encoded into exactly the words the existing compilers emit, and each interface law is proved
from the existing per-word step lemmas (`Words.lean`, `ArrWords.lean`, `BranchWords.lean`, `Loop.lean`). -/
import Compiler.Exp
import Riscv.Direct.Arr
import Riscv.Direct.Loop
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

def phys (r : Reg) : Fin 32 := if r.val < 11 then T r.val else A (r.val - 11)

theorem phys_T : ∀ r : Reg, r.val < 11 → phys r = T r.val := by decide
theorem phys_A : ∀ r : Reg, 11 ≤ r.val → ∃ i : Fin 4, phys r = A i.val := by decide
theorem phys_A8 : ∀ r : Reg, 7 ≤ r.val → ∃ i : Fin 8, phys r = A8 i := by decide
theorem phys_ne0 : ∀ r : Reg, phys r ≠ 0 := by decide
theorem phys_ne1 : ∀ r : Reg, (1 : Fin 32) ≠ phys r := by decide
theorem phys_inj : ∀ r q : Reg, phys r = phys q → r = q := by decide
theorem phys_avar : ∀ i : Fin 8, phys (avar i) = A8 i := by decide
theorem phys_v4 : ∀ i : Fin 4, phys (v4 i) = A i.val := by decide
theorem phys_rk {k : Nat} (h : k < 11) : phys (rk k) = T k := by
  rw [phys_T _ (by rw [rk_val (by omega)]; exact h), rk_val (by omega)]

def enc : AOp → List (BitVec 32)
  | .mov d a => [encR 0 0 (phys d) 0 (phys a)]
  | .li d c => genConst d.val c.toNat
  | .bin op d _ _ => opCode op d.val
  | .sel d _ _ _ => selCode d.val
  | .lbu _ _ => [iLbuT]
  | .sb _ _ => [iSbT]
  | .bz _ n => [iBeqz n]
  | .jmp n => [iJmp n]
  | .ret => [iRet]

def base : Base where
  S := St
  runsTo := Proven.runsTo
  ok := Cfg
  keep s s' := ∀ j : Fin 32, (∀ r : Reg, j ≠ phys r) → getX s' j = getX s j
  pcIs s pc := s.regs.get? .PC = some pc
  get s r := getX s (phys r)
  mem s a := s.mem[a]?
  ra s := getX s 1
  retOK v := v.toNat % 2 = 0
  instrAt := Proven.instrAt
  ramLo := 0x80000000
  ramHi := 0x100000000
  bzOK n := 2 * n < 2048
  jmpOK n := 0 < n ∧ 2 * n ≤ 2 ^ 19
  enc := enc
  lenBz := 1
  lenJmp := 1

def core : Core where
  toBase := base
  runsTo_of := Proven.runsTo_of
  runsTo_trans := Proven.runsTo_trans
  keep_refl _ _ _ := rfl
  keep_trans h₁ h₂ j hj := (h₂ j hj).trans (h₁ j hj)
  keep_ra h := h 1 phys_ne1
  instrAt_frame hm hi := instrAt_frame hi hm
  ramHi_lt := by decide
  len_bz _ _ := rfl
  len_jmp _ := rfl

/-! ## From `Next` to the abstract effects -/

theorem ofNext {s s' : St} {pc' : BitVec 64} {rd : Fin 32} {v m} (hn : Next s s' pc' rd v m)
    (hrd : rd = 0 ∨ ∃ r, rd = phys r) : core.Done s s' pc' := by
  refine ⟨hn.cfg, fun j hj => ?_, hn.pc⟩
  show getX s' j = getX s j
  rw [hn.x j]
  rcases hrd with rfl | ⟨r, rfl⟩
  · exact ite_neg (fun h => h.2 h.1)
  · exact ite_neg (fun h => hj r h.1)

theorem set1Of {s s' : St} {pc' : BitVec 64} {d : Reg} {v m} (hn : Next s s' pc' (phys d) v m) :
    core.Set1 s s' d v := by
  intro r
  show getX s' (phys r) = if r = d then v else getX s (phys r)
  rw [hn.x]
  by_cases h : r = d
  · subst h; rw [ite_pos ⟨rfl, phys_ne0 r⟩, ite_pos rfl]
  · rw [ite_neg (fun e => h (phys_inj _ _ e.1)), ite_neg h]

theorem sameOf {s s' : St} {pc' : BitVec 64} {v m} (hn : Next s s' pc' 0 v m) : core.Same s s' := by
  intro r; show getX s' (phys r) = getX s (phys r); rw [hn.x]; exact ite_neg (fun h => h.2 h.1)

theorem memOf {s s' : St} {pc' : BitVec 64} {rd : Fin 32} {v} (hn : Next s s' pc' rd v s.mem) :
    core.mem s' = core.mem s := by
  funext a; show s'.mem[a]? = s.mem[a]?; rw [hn.mem]

theorem run1 {s s' : St} {pc' rd v m} {P : St → Prop} (hn : Next s s' pc' rd v m) (hp : P s') : core.runsTo s P :=
  runsTo_next hn (runsTo_of hp)

/-- the first word of `At s pc (w :: ws)` -/
theorem first {s : St} {pc : BitVec 64} {w : BitVec 32} {ws} (hA : core.At s pc (w :: ws)) :
    Cfg s ∧ s.regs.get? .PC = some pc ∧ pcOK pc ∧ instrAt s pc w := by
  refine ⟨hA.ok, hA.hpc, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hA.codeOK
    have h3' : pc.toNat + 4 * (ws.length + 1) ≤ 0x100000000 := h3
    exact ⟨h1, h2, by omega⟩
  · have := hA.code 0 (by simp); simpa using this

theorem first1 {s : St} {pc : BitVec 64} {w : BitVec 32} (hA : core.At s pc [w]) :
    Cfg s ∧ s.regs.get? .PC = some pc ∧ pcOK pc ∧ instrAt s pc w := first hA

theorem n4 (pc : BitVec 64) : pc + 4 = next pc 1 := rfl

/-! ## The laws -/

theorem law_mov {d a : Reg} {s : St} {pc : BitVec 64} (hm : MovOK d a) (hA : core.At s pc (enc (.mov d a))) :
    core.runsTo s fun s' => core.Done s s' (next pc (enc (.mov d a)).length) ∧
      core.Set1 s s' d (core.get s a) ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hn⟩ : ∃ s', Next s s' (pc + 4) (phys d) (getX s (phys a)) s.mem := by
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · obtain ⟨i, ei⟩ := phys_A a h2
      rw [phys_T d (by omega)] at hi ⊢; rw [ei] at hi ⊢
      exact step_var h hpc hok i.val d.val (by omega) i.2 hi
    · obtain ⟨i, ei⟩ := phys_A8 a h2
      rw [phys_T d (by omega)] at hi ⊢; rw [ei] at hi ⊢
      exact step_var8 h hpc hok i d.val h1 hi
    · obtain ⟨v, ev⟩ := phys_A8 d h2
      have ea : phys a = 5 := by rw [phys_T a (by omega), h1]; rfl
      rw [ev, ea] at hi ⊢
      exact step_mv8 h hpc hok v hi
  exact run1 hn ⟨ofNext hn (.inr ⟨d, rfl⟩), set1Of hn, memOf hn⟩

theorem shl_ofNat' (m : Nat) : BitVec.ofNat 64 m <<< 1 = BitVec.ofNat 64 (2 * m) := shl_ofNat m

theorem li_ok {d : Reg} (hd : d.val < 11) : ∀ (n : Nat) {s : St} {pc : BitVec 64},
    core.At s pc (genConst d.val n) →
    core.runsTo s fun s' => core.Done s s' (next pc (genConst d.val n).length) ∧
      core.Set1 s s' d (BitVec.ofNat 64 n) ∧ core.mem s' = core.mem s := by
  have eT := phys_T d hd
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s pc hA
  rw [genConst] at hA ⊢
  by_cases hn : n = 0
  · subst hn
    rw [ite_pos rfl] at hA ⊢
    obtain ⟨h, hpc, hok, hi⟩ := first1 hA
    obtain ⟨s', hn⟩ := step_zero h hpc hok d.val hd hi
    rw [← eT] at hn
    exact run1 hn ⟨ofNext hn (.inr ⟨d, rfl⟩), set1Of hn, memOf hn⟩
  · rw [ite_neg hn] at hA ⊢
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    rw [List.length_append, List.length_append, ← next_add, ← next_add]
    refine core.seq_run (ih (n / 2) (by omega) hA1) fun s₁ d₁ ⟨st₁, m₁⟩ => ?_
    obtain ⟨h, hpc, hok, hi⟩ := first1 (Core.Done.at _ d₁ (core.codeAt_mem m₁ hc2) ho2)
    obtain ⟨s₂, hn₂⟩ := step_shl h hpc hok d.val hd hi
    rw [← eT] at hn₂
    have v₂ : getX s₁ (phys d) <<< 1 = BitVec.ofNat 64 (2 * (n / 2)) := by
      rw [show getX s₁ (phys d) = core.get s₁ d from rfl, Core.Set1.same _ st₁, shl_ofNat]
    rw [v₂] at hn₂
    have d₂ := ofNext hn₂ (.inr ⟨d, rfl⟩)
    have st₂ := Core.Set1.trans _ st₁ (set1Of hn₂)
    have m₂ : core.mem s₂ = core.mem s := (memOf hn₂).trans m₁
    by_cases hodd : n % 2 = 1
    · rw [ite_pos hodd] at hc3 ho3 ⊢
      obtain ⟨h₂, hpc₂, hok₂, hi₂⟩ := first1 (Core.Done.at _ d₂ (core.codeAt_mem m₂ hc3) ho3)
      obtain ⟨s₃, hn₃⟩ := step_inc h₂ hpc₂ hok₂ d.val hd hi₂
      rw [← eT, show getX s₂ (phys d) = core.get s₂ d from rfl, Core.Set1.same _ st₂, inc_ofNat] at hn₃
      refine runsTo_next hn₂ (run1 hn₃ ⟨Core.Done.trans _ d₂ (ofNext hn₃ (.inr ⟨d, rfl⟩)), ?_, (memOf hn₃).trans m₂⟩)
      have := Core.Set1.trans _ st₂ (set1Of hn₃)
      rwa [show 2 * (n / 2) + 1 = n by omega] at this
    · rw [ite_neg hodd] at hc3 ho3 ⊢
      refine run1 hn₂ ⟨?_, ?_, m₂⟩
      · rw [List.length_nil, next_zero]; exact d₂
      · rwa [show 2 * (n / 2) = n by omega] at st₂

theorem law_li {d : Reg} {c : BitVec 64} {s : St} {pc : BitVec 64} (hd : d.val < 11)
    (hA : core.At s pc (enc (.li d c))) :
    core.runsTo s fun s' => core.Done s s' (next pc (enc (.li d c)).length) ∧
      core.Set1 s s' d c ∧ core.mem s' = core.mem s := by
  have := li_ok hd c.toNat hA
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem law_bin {op : Op} {d a b : Reg} {s : St} {pc : BitVec 64} (hd : d.val < 10) (ha : a = d)
    (hb : b.val = d.val + 1) (hA : core.At s pc (enc (.bin op d a b))) :
    core.runsTo s fun s' => core.Done s s' (next pc (enc (.bin op d a b)).length) ∧
      core.Set1 s s' d (op.eval (core.get s a) (core.get s b)) ∧ core.mem s' = core.mem s := by
  subst ha
  have eT := phys_T a (by omega)
  have eb : phys b = T (a.val + 1) := by rw [phys_T b (by omega), hb]
  show core.runsTo s fun s' => _ ∧ core.Set1 s s' a (op.eval (getX s (phys a)) (getX s (phys b))) ∧ _
  change core.At s pc (opCode op a.val) at hA
  change core.runsTo s fun s' => core.Done s s' (next pc (opCode op a.val).length) ∧ _
  unfold opCode at hA ⊢
  by_cases he : op = .eq
  · subst he; rw [ite_pos rfl] at hA ⊢
    obtain ⟨h, hpc, hok, hi⟩ := first hA
    obtain ⟨s₁, hn₁⟩ := step_op h hpc hok .eq a.val hd hi
    rw [← eT, ← eb] at hn₁
    have d₁ := ofNext hn₁ (.inr ⟨a, rfl⟩)
    have hA' := Core.At.split _ (l₁ := [iOp .eq a.val]) (l₂ := [iSeqz a.val]) hA
    obtain ⟨h', hpc', hok', hi'⟩ := first1 (Core.Done.at _ d₁ (core.codeAt_mem (memOf hn₁) hA'.2.1) hA'.2.2)
    obtain ⟨s₂, hn₂⟩ := step_seqz h' hpc' hok' a.val hd hi'
    rw [← eT, show getX s₁ (phys a) = core.get s₁ a from rfl, Core.Set1.same _ (set1Of hn₁)] at hn₂
    rw [show pc + 4 + 4 = next pc 2 from next_add pc 1 1] at hn₂
    refine runsTo_next hn₁ (run1 hn₂ ⟨Core.Done.trans _ d₁ (ofNext hn₂ (.inr ⟨a, rfl⟩)), ?_, (memOf hn₂).trans (memOf hn₁)⟩)
    have := Core.Set1.trans _ (set1Of hn₁) (set1Of hn₂)
    simpa [Op.raw, Op.eval, xor_eq_zero] using this
  · rw [ite_neg he] at hA ⊢
    obtain ⟨h, hpc, hok, hi⟩ := first1 hA
    obtain ⟨s₁, hn₁⟩ := step_op h hpc hok op a.val hd hi
    rw [← eT, ← eb, Op.raw, ite_neg he] at hn₁
    exact run1 hn₁ ⟨ofNext hn₁ (.inr ⟨a, rfl⟩), set1Of hn₁, memOf hn₁⟩

/-- run the first word, then the rest -/
theorem chain {s s' : St} {pc : BitVec 64} {w : BitVec 32} {ws : List (BitVec 32)} {rd : Fin 32} {v : BitVec 64}
    {P : St → Prop} (hA : core.At s pc (w :: ws)) (hn : Next s s' (pc + 4) rd v s.mem) (hrd : rd = 0 ∨ ∃ r, rd = phys r)
    (h : core.At s' (next pc 1) ws →
      core.runsTo s' fun s'' => core.Done s' s'' (next (next pc 1) ws.length) ∧ P s'') :
    core.runsTo s fun s'' => core.Done s s'' (next pc (w :: ws).length) ∧ P s'' := by
  have sp := Core.At.split _ (l₁ := [w]) (l₂ := ws) hA
  have d₁ := ofNext hn hrd
  refine runsTo_next hn (core.runsTo_mono (h (Core.Done.at _ d₁ (core.codeAt_mem (memOf hn) sp.2.1) sp.2.2))
    fun s'' ⟨d, p⟩ => ⟨?_, p⟩)
  rw [next_add] at d
  rw [List.length_cons, Nat.add_comm]
  exact Core.Done.trans _ d₁ d

theorem xor_raw (x y : BitVec 64) : Op.raw .xor x y = x ^^^ y := rfl
theorem and_raw (x y : BitVec 64) : Op.raw .and x y = x &&& y := rfl

theorem law_sel {d c a b : Reg} {s : St} {pc : BitVec 64} (hd : d.val < 9) (hc : c = d) (ha : a.val = d.val + 1)
    (hb : b.val = d.val + 2) (hA : core.At s pc (enc (.sel d c a b))) :
    core.runsTo s fun s' => core.Done s s' (next pc (enc (.sel d c a b)).length) ∧
      core.get s' d = (if core.get s c = 0 then core.get s b else core.get s a) ∧
      (∀ r, r ≠ d → r ≠ a → core.get s' r = core.get s r) ∧ core.mem s' = core.mem s := by
  subst hc
  have eT := phys_T c (by omega)
  have ea : phys a = T (c.val + 1) := by rw [phys_T a (by omega), ha]
  have eb : phys b = T (c.val + 1 + 1) := by rw [phys_T b (by omega), hb]
  have eb' : phys b = T (c.val + 2) := eb
  have nad : a ≠ c := fun e => by subst e; omega
  have nbd : b ≠ c := fun e => by subst e; omega
  have nba : b ≠ a := fun e => by subst e; omega
  change core.At s pc [iSnez c.val, iNeg c.val, iOp .xor (c.val + 1), iOp .and c.val, iXor2 c.val] at hA
  change core.runsTo s fun s' => core.Done s s' (next pc (selCode c.val).length) ∧ _
  obtain ⟨h, hpc, hok, hi⟩ := first hA
  obtain ⟨s₁, n₁⟩ := step_snez h hpc hok c.val hd hi
  rw [← eT] at n₁
  refine chain hA n₁ (.inr ⟨c, rfl⟩) fun A₁ => ?_
  obtain ⟨h, hpc, hok, hi⟩ := first A₁
  obtain ⟨s₂, n₂⟩ := step_neg h hpc hok c.val hd hi
  rw [← eT] at n₂
  refine chain A₁ n₂ (.inr ⟨c, rfl⟩) fun A₂ => ?_
  obtain ⟨h, hpc, hok, hi⟩ := first A₂
  obtain ⟨s₃, n₃⟩ := step_op h hpc hok .xor (c.val + 1) (by omega) hi
  rw [← ea, ← eb, xor_raw] at n₃
  refine chain A₂ n₃ (.inr ⟨a, rfl⟩) fun A₃ => ?_
  obtain ⟨h, hpc, hok, hi⟩ := first A₃
  obtain ⟨s₄, n₄⟩ := step_op h hpc hok .and c.val (by omega) hi
  rw [← eT, ← ea, and_raw] at n₄
  refine chain A₃ n₄ (.inr ⟨c, rfl⟩) fun A₄ => ?_
  obtain ⟨h, hpc, hok, hi⟩ := first1 A₄
  obtain ⟨s₅, n₅⟩ := step_xor2 h hpc hok c.val hd hi
  rw [← eT, ← eb'] at n₅
  have S₁ := set1Of n₁; have S₂ := set1Of n₂; have S₃ := set1Of n₃; have S₄ := set1Of n₄; have S₅ := set1Of n₅
  refine run1 n₅ ⟨ofNext n₅ (.inr ⟨c, rfl⟩), ?_, fun r h1 h2 => ?_,
    (memOf n₅).trans ((memOf n₄).trans ((memOf n₃).trans ((memOf n₂).trans (memOf n₁))))⟩
  · have g := fun {t t' : St} {d' v'} (S : core.Set1 t t' d' v') => Core.Set1.same _ S
    have o := fun {t t' : St} {d' v' r} (S : core.Set1 t t' d' v') (hr : r ≠ d') => Core.Set1.other _ S hr
    change core.Set1 s s₁ c (if core.get s c = 0 then 0 else 1) at S₁
    change core.Set1 s₁ s₂ c (-core.get s₁ c) at S₂
    change core.Set1 s₂ s₃ a (core.get s₂ a ^^^ core.get s₂ b) at S₃
    change core.Set1 s₃ s₄ c (core.get s₃ c &&& core.get s₃ a) at S₄
    change core.Set1 s₄ s₅ c (core.get s₄ c ^^^ core.get s₄ b) at S₅
    show core.get s₅ c = _
    simp only [g S₅, g S₄, g S₃, g S₂, g S₁, o S₄ nbd, o S₃ nba, o S₂ nbd, o S₁ nbd, o S₃ nad.symm, o S₂ nad,
      o S₁ nad]
    exact sel_val _ _ _
  · have o := fun {t t' : St} {d' v' r} (S : core.Set1 t t' d' v') (hr : r ≠ d') => Core.Set1.other _ S hr
    rw [o S₅ h1, o S₄ h1, o S₃ h2, o S₂ h1, o S₁ h1]

theorem law_lbu {d a : Reg} {s : St} {pc : BitVec 64} {v : BitVec 8} (hd : d.val = 0) (ha : a.val = 0)
    (hA : core.At s pc (enc (.lbu d a))) (hr : core.inRAM (core.get s a).toNat 1)
    (hm : core.mem s (core.get s a).toNat = some v) :
    core.runsTo s fun s' => core.Done s s' (next pc (enc (.lbu d a)).length) ∧
      core.Set1 s s' d (v.setWidth 64) ∧ core.mem s' = core.mem s := by
  have ed : phys d = 5 := by rw [phys_T d (by omega), hd]; rfl
  have ea : phys a = 5 := by rw [phys_T a (by omega), ha]; rfl
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  have hr' : 0x80000000 ≤ (getX s 5).toNat ∧ (getX s 5).toNat + 1 ≤ 0x100000000 := by
    rw [← ea]; exact hr
  obtain ⟨s', hn⟩ := W8.lbuT h hpc hok hi hr' (by rw [← ea]; exact hm)
  rw [← ed] at hn
  exact run1 hn ⟨ofNext hn (.inr ⟨d, rfl⟩), set1Of hn, memOf hn⟩

theorem law_sb {v a : Reg} {s : St} {pc : BitVec 64} (hv : v.val = 1) (ha : a.val = 0)
    (hA : core.At s pc (enc (.sb v a))) (hr : core.inRAM (core.get s a).toNat 1) :
    core.runsTo s fun s' => core.Done s s' (next pc (enc (.sb v a)).length) ∧
      core.Same s s' ∧ core.mem s' = (core.mem s).upd (core.get s a).toNat ((core.get s v).setWidth 8) := by
  have ev : phys v = 6 := by rw [phys_T v (by omega), hv]; rfl
  have ea : phys a = 5 := by rw [phys_T a (by omega), ha]; rfl
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  have hr' : 0x80000000 ≤ (getX s 5).toNat ∧ (getX s 5).toNat + 1 ≤ 0x100000000 := by
    rw [← ea]; exact hr
  obtain ⟨s', hn⟩ := W8.sbT h hpc hok hi hr'
  refine run1 hn ⟨ofNext hn (.inl rfl), sameOf hn, ?_⟩
  funext x
  show s'.mem[x]? = Mem.upd (fun y => s.mem[y]?) (getX s (phys a)).toNat ((getX s (phys v)).setWidth 8) x
  rw [hn.mem, ea, ev, Std.ExtHashMap.getElem?_insert]
  unfold Mem.upd
  by_cases hx : x = (getX s 5).toNat
  · subst hx; simp
  · simp only [getX_eq] at hx; simp [Ne.symm hx, hx]

theorem law_bz {c : Reg} {n : Nat} {s : St} {pc : BitVec 64} (hc : c.val = 0) (hn : core.bzOK n)
    (hA : core.At s pc (enc (.bz c n))) :
    core.runsTo s fun s' => core.Done s s'
        (if core.get s c = 0 then next pc n else next pc (enc (.bz c n)).length) ∧
      core.Same s s' ∧ core.mem s' = core.mem s := by
  have ec : phys c = 5 := by rw [phys_T c (by omega), hc]; rfl
  have hn' : 2 * n < 2048 := hn
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  by_cases h0 : core.get s c = 0
  · rw [ite_pos h0]
    have h0' : getX s 5 = 0#64 := by rw [← ec]; exact h0
    obtain ⟨s', hx⟩ := beq_5_0_t h hpc hok _ hi h0'
    rw [boff_fwd n hn'] at hx
    exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩
  · rw [ite_neg h0]
    have h0' : ¬getX s 5 = 0#64 := by rw [← ec]; exact h0
    obtain ⟨s', hx⟩ := beq_5_0_n h hpc hok _ hi h0'
    exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩

theorem law_jmp {n : Nat} {s : St} {pc : BitVec 64} (hn : core.jmpOK n) (hA : core.At s pc (enc (.jmp n))) :
    core.runsTo s fun s' => core.Done s s' (pc - BitVec.ofNat 64 (4 * n)) ∧ core.Same s s' ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hx⟩ := step_jal_0 h hpc hok _ hi
  rw [joff_back n hn.1 hn.2, show pc + (0 - BitVec.ofNat 64 (4 * n)) = pc - BitVec.ofNat 64 (4 * n) by bv_omega] at hx
  exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩

theorem law_ret {s : St} {pc : BitVec 64} (hr : core.retOK (core.ra s)) (hA : core.At s pc (enc .ret)) :
    core.runsTo s fun s' => core.Done s s' (core.ra s) ∧ core.Same s s' ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hx⟩ := step_ret h hpc hok hi hr
  exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩

/-- **The Sail RV64 model is a `Machine`.** -/
def rv : Machine where
  toCore := core
  law_mov := law_mov
  law_li := law_li
  law_bin := law_bin
  law_sel := law_sel
  law_lbu := law_lbu
  law_sb := law_sb
  law_bz := law_bz
  law_jmp := law_jmp
  law_ret := law_ret

end Proven.Mach.Riscv
