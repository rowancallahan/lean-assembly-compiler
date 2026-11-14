/- Byte arrays with spill slots: correctness of the statement compiler `compileB` on the Sail model.

Memory: data blocks are contiguous regions `R`; the slots are the 8-byte regions `slotRegs N fp`
(`fp + 8 (j + 1)`, `j < N`); `R ++ slotRegs N fp` must be in RAM and pairwise disjoint, the code outside
all of them.  The proof is `execA_ok` (`Proven/Arr.lean`) with the variable relation `EnvRel`
(registers and slots) and stores into slots handled like 8-byte stores into a region. -/
import Riscv.Direct.Arr2Exp
import Riscv.Direct.Arr

set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Proven

def slotRegs (N fp : Nat) : List Region := (List.range N).map fun j => ⟨fp + 8 * (j + 1), 8⟩

/-- the blocks: lengths, base variables, contents -/
structure HeapRel (bv : List Nat) (R : List Region) (σ : BState) (s : St) : Prop where
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  bytes : ∀ b (hb : b < R.length), bytesAt s R[b].base R[b].len = (σ.heap[b]?.getD []).map some

structure Rel2 (N fp : Nat) (bv : List Nat) (R : List Region) (σ : BState) (s : St) : Prop where
  env : EnvRel N fp σ.env s
  heap : HeapRel bv R σ s

theorem RR_slot {R : List Region} {N fp j : Nat} (hj : j < N) :
    ∃ h : R.length + j < (R ++ slotRegs N fp).length,
      (R ++ slotRegs N fp)[R.length + j] = ⟨fp + 8 * (j + 1), 8⟩ := by
  refine ⟨by simp [slotRegs]; omega, ?_⟩
  rw [List.getElem_append_right (by omega)]; simp [slotRegs]

theorem RR_blk {R : List Region} {N fp b : Nat} (hb : b < R.length) :
    ∃ h : b < (R ++ slotRegs N fp).length, (R ++ slotRegs N fp)[b] = R[b] :=
  ⟨by simp; omega, List.getElem_append_left hb⟩

/-- memory unchanged and the variable registers / `gp` unchanged -/
theorem Rel2.regs {N fp bv R σ} {s s' : St} (r : Rel2 N fp bv R σ s) (hm : s'.mem = s.mem)
    (he : ∀ i, getX s' (A8 i) = getX s (A8 i)) (h3 : getX s' 3 = getX s 3) : Rel2 N fp bv R σ s' :=
  ⟨⟨fun i => by rw [he, r.env.reg], by rw [h3, r.env.gp], fun j hj => by rw [bytesAt_mem hm, r.env.slot j hj]⟩,
    ⟨r.heap.hlen, r.heap.bvlen, r.heap.base, r.heap.blen, fun b hb => by rw [bytesAt_mem hm, r.heap.bytes b hb]⟩⟩

theorem getD_memN {bv : List Nat} {b : Nat} (hb : b < bv.length) : bv.getD b 0 ∈ bv := by
  simp [List.getD_eq_getElem?_getD, hb]

theorem A8_ne_3 (i : Fin 8) : A8 i ≠ 3 := by revert i; decide
theorem A8_val {i : Fin 8} {v : Nat} (hv : v < 8) (h : A8 i = A8 ⟨v, hv⟩) : i.val = v := by
  have := A8_inj h; rw [this]

/-- `v := t0` (register move or slot store), for `v` not a base variable -/
theorem setV_ok {N fp : Nat} (hf : FrOK N fp) {bv : List Nat} {R : List Region} (hR : RegOK (R ++ slotRegs N fp))
    {v : Nat} (hv : v < 8 + N) (hvb : v ∉ bv) {σ : BState} {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc (setV v)) (hrel : Rel2 N fp bv R σ s) :
    ∃ s', Reach s s' ∧ AF (R ++ slotRegs N fp) s s' ∧ s'.regs.get? .PC = some (pc + 4) ∧
      Rel2 N fp bv R ⟨σ.env.set v (getX s 5), σ.heap⟩ s' := by
  have hbase : ∀ b (hb : b < R.length), (σ.env.set v (getX s 5)) (bv.getD b 0) = BitVec.ofNat 64 R[b].base :=
    fun b hb => by
      have : bv.getD b 0 ≠ v := fun e => hvb (e ▸ getD_memN (hrel.heap.bvlen ▸ hb))
      simp only [BEnv.set, if_neg this]; exact hrel.heap.base b hb
  by_cases hv8 : v < 8
  · simp only [setV, hv8, dite_true] at hi
    obtain ⟨s', hn⟩ := step_mv8 h hpc hok ⟨v, hv8⟩ hi
    refine ⟨s', Reach.next hn, AF.ofNext hn (unchangedOutside_of_mem hn.mem) (.inr (.inl ⟨_, rfl⟩)), hn.pc,
      ⟨⟨fun i => ?_, ?_, fun j hj => ?_⟩, ⟨hrel.heap.hlen, hrel.heap.bvlen, hbase, hrel.heap.blen,
        fun b hb => by rw [bytesAt_mem hn.mem, hrel.heap.bytes b hb]⟩⟩⟩
    · rw [hn.x]
      by_cases hiv : i.val = v
      · have : A8 i = A8 ⟨v, hv8⟩ := congrArg A8 (Fin.ext hiv)
        simp [this, A8_ne_0, BEnv.set, hiv]
      · have : A8 i ≠ A8 ⟨v, hv8⟩ := fun e => hiv (A8_val hv8 e)
        rw [if_neg (fun h => this h.1)]; simp only [BEnv.set, if_neg hiv]; exact hrel.env.reg i
    · rw [hn.x, if_neg (fun h => A8_ne_3 _ h.1.symm)]; exact hrel.env.gp
    · rw [bytesAt_mem hn.mem, hrel.env.slot j hj]; simp only [BEnv.set, if_neg (show 8 + j ≠ v by omega)]
  · simp only [setV, hv8, dite_false] at hi
    have hj : v - 8 < N := by omega
    obtain ⟨e1, e2, e3, e4⟩ := slot_addr hf hj hrel.env.gp
    obtain ⟨s', hn⟩ := step_sdS h hpc hok (v - 8) (by have := hf.ns; omega) hi e3 e4 e1
    rw [e2] at hn
    obtain ⟨hk, hk'⟩ := RR_slot (R := R) (fp := fp) hj
    obtain ⟨st1, st2, st3⟩ := Next.store_region8 hR.1 hR.2 hk hk' hn
    have hu : unchangedOutside s s' (R ++ slotRegs N fp) := fun a ha => st3 a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ha _ (List.getElem_mem hk)
    refine ⟨s', Reach.next hn, AF.ofNext hn hu (.inl rfl), hn.pc,
      ⟨⟨fun i => ?_, ?_, fun j hj' => ?_⟩, ⟨hrel.heap.hlen, hrel.heap.bvlen, hbase, hrel.heap.blen, fun b hb => ?_⟩⟩⟩
    · rw [hn.keep0, hrel.env.reg i]; simp only [BEnv.set, if_neg (show i.val ≠ v by omega)]
    · rw [hn.keep0]; exact hrel.env.gp
    · by_cases hjv : j = v - 8
      · subst hjv; rw [st1]; simp only [BEnv.set, if_pos (show 8 + (v - 8) = v by omega)]
      · obtain ⟨hk2, hk2'⟩ := RR_slot (R := R) (fp := fp) hj'
        have := st2 _ hk2 (by omega); rw [hk2'] at this; dsimp only at this
        rw [this, hrel.env.slot j hj']; simp only [BEnv.set, if_neg (show 8 + j ≠ v by omega)]
    · obtain ⟨hb2, hb2'⟩ := RR_blk (N := N) (fp := fp) hb
      have := st2 _ hb2 (by omega); rw [hb2'] at this
      rw [this, hrel.heap.bytes b hb]

/-- the address of an in-bounds element -/
theorem addrB_ok {N fp bv R σ} {s : St} (r : Rel2 N fp bv R σ s) (hR : RegOK R) {b : Nat} (hb : b < σ.heap.length)
    {i : BExp} (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
    ∃ hbR : b < R.length, ((addrB bv b i).denote σ.env).toNat = R[b].base + (i.denote σ.env).toNat ∧
      0x80000000 ≤ R[b].base + (i.denote σ.env).toNat ∧ R[b].base + (i.denote σ.env).toNat + 1 ≤ 0x100000000 := by
  have hbR : b < R.length := r.heap.hlen ▸ hb
  have hl := r.heap.blen b hbR; rw [hget _ hb] at hl
  have hram := hR.1 _ (List.getElem_mem hbR); unfold Region.inRAM at hram
  refine ⟨hbR, ?_, by omega, by omega⟩
  simp only [addrB, BExp.denote, Op.eval, r.heap.base b hbR]
  exact addr_toNat (len := R[b].len) (by omega) (by omega)

theorem RegOK.left {R S : List Region} (h : RegOK (R ++ S)) : RegOK R :=
  ⟨fun r hr => h.1 r (List.mem_append_left _ hr), (List.pairwise_append.mp h.2).1⟩

theorem vlt_addr {bv : List Nat} {b m : Nat} {i : BExp} (hb : b < bv.length) (hbv : ∀ x ∈ bv, x < m)
    (hi : i.vlt m) : (addrB bv b i).vlt m :=
  ⟨hbv _ (getD_memN hb), hi⟩

/-! ## Correctness -/

theorem execB_ok {N fp : Nat} (hf : FrOK N fp) (bv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N)
    {R : List Region} (hR : RegOK (R ++ slotRegs N fp)) :
    ∀ {p : BStmt} {σ σ' : BState}, BExec p σ σ' → p.wf N bv → ∀ {s : St} {pc : BitVec 64}, Cfg s →
    s.regs.get? .PC = some pc → codeAt s pc (compileB bv p) → codeOK pc (compileB bv p).length →
    (∀ r ∈ R ++ slotRegs N fp, disjoint ⟨pc.toNat, 4 * (compileB bv p).length⟩ r) → Rel2 N fp bv R σ s →
    ∃ s', Reach s s' ∧ AF (R ++ slotRegs N fp) s s' ∧
      s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (compileB bv p).length)) ∧ Rel2 N fp bv R σ' s'
  | _, σ, _, .assign (v := v) (e := e), hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [compileB, BStmt.wf] at hp hc hok ⊢
    rw [codeAt_append] at hc
    rw [List.length_append] at hok ⊢
    obtain ⟨ok1, ok2⟩ := codeOK_append hok
    obtain ⟨s₁, r₁, R₁, v₁⟩ := genB_ok hf σ.env e 0 (by omega) hp.2.1 h hpc hc.1 ok1 hrel.env
    have hrel₁ : Rel2 N fp bv R σ s₁ := hrel.regs R₁.mem R₁.keepA (R₁.keep 3 (fun i _ hi => three_ne_T i hi))
    obtain ⟨s₂, r₂, F₂, pc₂, v₂⟩ := setV_ok hf hR hp.2.2.1 hp.2.2.2 R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp))
      (codeAt_one (codeAt_mem R₁.mem hc.2)) hrel₁
    refine ⟨s₂, r₁.trans r₂, (AF.ofRan7 R₁).trans F₂, by rw [pc₂, ← pc_add]; rfl, ?_⟩
    rw [show getX s₁ 5 = e.denote σ.env from v₁] at v₂; exact v₂
  | _, σ, _, .load (v := v) (b := b) (i := i) hb hi, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [compileB, BStmt.wf] at hp hc hok ⊢
    rw [codeAt_append] at hc
    rw [List.length_append] at hok ⊢
    obtain ⟨ok1, ok2⟩ := codeOK_append hok
    obtain ⟨hbR, ha, hram1, hram2⟩ := addrB_ok hrel hR.left hb hi
    obtain ⟨s₁, r₁, R₁, v₁⟩ := genB_ok hf σ.env (addrB bv b i) 0 (by simp [addrB, BExp.depth]; omega)
      (vlt_addr hp.2.2.2.2 hbv hp.2.1) h hpc hc.1 ok1 hrel.env
    have hc2 := codeAt_mem R₁.mem hc.2
    have hbyte := mem_of_bytesAt (hrel.heap.bytes b hbR) (i := (i.denote σ.env).toNat)
      (by rw [hget _ hb]; exact hi)
    simp only [hget _ hb] at hbyte
    have h5 : (getX s₁ 5).toNat = R[b].base + (i.denote σ.env).toNat := by
      rw [show (5 : Fin 32) = T 0 from rfl, v₁, ha]
    obtain ⟨s₂, hn₂⟩ := W8.lbuT R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) (by simpa [iLbuT] using hc2 0 (by simp))
      (by rw [h5]; omega) (b := σ.heap[b][(i.denote σ.env).toNat]) (by rw [h5, R₁.mem]; exact hbyte)
    have hpc₂ : s₂.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (genB (addrB bv b i) 0).length) +
        BitVec.ofNat 64 (4 * 1)) := hn₂.pc
    have hrel₂ : Rel2 N fp bv R σ s₂ := by
      refine (hrel.regs R₁.mem R₁.keepA (R₁.keep 3 (fun i _ hi => three_ne_T i hi))).regs hn₂.mem
        (fun j => ?_) ?_
      · rw [hn₂.x (A8 j), if_neg (fun h => T_ne_A8' 0 (by omega) j h.1.symm)]
      · rw [hn₂.x 3, if_neg (by decide)]
    obtain ⟨s₃, r₃, F₃, pc₃, v₃⟩ := setV_ok hf hR hp.2.2.1 hp.2.2.2.1 hn₂.cfg hpc₂
      (codeOK_pcOK (codeOK_append (a := 1) (b := 1) ok2).2 (by simp))
      (by simpa using (codeAt_mem hn₂.mem hc2) 1 (by simp)) hrel₂
    refine ⟨s₃, (r₁.trans (Reach.next hn₂)).trans r₃,
      ((AF.ofRan7 R₁).trans (AF.ofNext hn₂ (unchangedOutside_of_mem hn₂.mem) (.inr (.inr ⟨0, by omega, rfl⟩)))).trans F₃,
      by rw [pc₃, pc4, pc_add]; exact congrArg some (pc_eq (by simp)), ?_⟩
    have : getX s₂ 5 = σ.heap[b][(i.denote σ.env).toNat].setWidth 64 := by rw [hn₂.x 5]; rfl
    rw [this] at v₃; exact v₃
  | _, σ, _, .store (b := b) (i := i) (e := e) hb hi, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [compileB, BStmt.wf] at hp hc hok hcd ⊢
    rw [codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append] at hok hcd ⊢
    obtain ⟨ok12, ok3⟩ := codeOK_append hok
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨hbR, ha, hram1, hram2⟩ := addrB_ok hrel hR.left hb hi
    obtain ⟨s₁, r₁, R₁, v₁⟩ := genB_ok hf σ.env (addrB bv b i) 0 (by simp [addrB, BExp.depth]; omega)
      (vlt_addr hp.2.2.2.2 hbv hp.2.2.1) h hpc hc.1.1 ok1 hrel.env
    obtain ⟨s₂, r₂, R₂, v₂⟩ := genB_ok hf σ.env e 1 (by omega) hp.2.2.2.1 R₁.cfg R₁.pc (codeAt_mem R₁.mem hc.1.2) ok2
      (hrel.env.ran7 R₁)
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.zero_le _)
    have h5 : (getX s₂ 5).toNat = R[b].base + (i.denote σ.env).toNat := by
      rw [R₂.keep 5 (fun j hj hj7 he => by have := T_inj (i := 0) (j := j) (by omega) (by omega) he; omega)]
      rw [show (5 : Fin 32) = T 0 from rfl, v₁, ha]
    have hc3 := codeAt_mem R₁₂.mem hc.2
    rw [List.length_append] at hc3
    obtain ⟨s₃, hn₃⟩ := W8.sbT R₁₂.cfg R₁₂.pc (codeOK_pcOK ok3 (by simp)) (by simpa [iSbT] using hc3 0 (by simp))
      (by rw [h5]; omega)
    rw [h5, show (6 : Fin 32) = T 1 from rfl, v₂] at hn₃
    obtain ⟨hk, hk'⟩ := RR_blk (N := N) (fp := fp) hbR
    have hil : (i.denote σ.env).toNat < R[b].len := by
      have := hrel.heap.blen b hbR; rw [hget _ hb] at this; omega
    rw [← hk'] at hn₃
    obtain ⟨st1, st2, st3⟩ := Next.store_region hR.1 hR.2 hk (by rw [hk']; exact hil) hn₃
    rw [hk'] at st1
    have hu : unchangedOutside s₂ s₃ (R ++ slotRegs N fp) := fun a ha' => st3 a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ha' _ (List.getElem_mem hk)
    have hx : ∀ j, getX s₃ j = getX s₂ j := fun j => hn₃.keep0 j
    have hm : ∀ a n, bytesAt s₂ a n = bytesAt s a n := fun a n => bytesAt_mem R₁₂.mem a n
    refine ⟨s₃, ((r₁.trans r₂).trans (Reach.next hn₃)), (AF.ofRan7 R₁₂).trans (AF.ofNext hn₃ hu (.inl rfl)),
      by rw [hn₃.pc, pc4]; exact congrArg some (pc_eq (by simp)), ⟨⟨fun j => ?_, ?_, fun j hj => ?_⟩,
        ⟨by rw [List.length_set, hrel.heap.hlen], hrel.heap.bvlen, hrel.heap.base, fun b' hb' => ?_, fun b' hb' => ?_⟩⟩⟩
    · rw [hx, R₁₂.keepA, hrel.env.reg]
    · rw [hx, R₁₂.keep 3 (fun i _ hi => three_ne_T i hi), hrel.env.gp]
    · obtain ⟨hk2, hk2'⟩ := RR_slot (R := R) (fp := fp) hj
      have := st2 _ hk2 (by omega); rw [hk2'] at this; dsimp only at this
      rw [this, hm, hrel.env.slot j hj]
    · by_cases hbb : b' = b
      · subst hbb
        have := hrel.heap.blen b' hb'; rw [hget _ hb] at this
        simpa [List.getElem?_set, hb] using this
      · simp only [List.getElem?_set, Ne.symm hbb, if_false]; exact hrel.heap.blen b' hb'
    · by_cases hbb : b' = b
      · subst hbb
        rw [st1, hm, hrel.heap.bytes b' hb', hget _ hb]
        simp [List.getElem?_set, hb, List.map_set]
      · obtain ⟨hb2, hb2'⟩ := RR_blk (N := N) (fp := fp) hb'
        have := st2 _ hb2 hbb; rw [hb2'] at this
        rw [this, hm, hrel.heap.bytes b' hb']
        simp only [List.getElem?_set, Ne.symm hbb, if_false]
  | _, σ, _, .seq (p := a) (q := b) ha hb, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [compileB, BStmt.wf] at hp hc hok hcd ⊢
    rw [codeAt_append] at hc
    rw [List.length_append] at hok hcd ⊢
    obtain ⟨ok1, ok2⟩ := codeOK_append hok
    have e := pc_toNat hok (a := (compileB bv a).length) (by omega)
    obtain ⟨s₁, r₁, F₁, pc₁, v₁⟩ := execB_ok hf bv hbv hR ha hp.1 h hpc hc.1 ok1
      (disj_sub hcd (Nat.le_refl _) (by omega)) hrel
    obtain ⟨s₂, r₂, F₂, pc₂, v₂⟩ := execB_ok hf bv hbv hR hb hp.2 F₁.cfg pc₁
      (codeAt_out hc.2 ok2 (disj_sub hcd (by omega) (by omega)) F₁.out) ok2 (disj_sub hcd (by omega) (by omega)) v₁
    exact ⟨s₂, r₁.trans r₂, F₁.trans F₂, by rw [pc₂, pc_add], v₂⟩
  | _, σ, _, .loopF (c := c) (b := b) hc0, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [BStmt.wf] at hp
    obtain ⟨hp1, hp1', hp2, hp3⟩ := hp
    rw [compileB] at hc hok ⊢
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    simp only [List.length_append, List.length_singleton] at hok ⊢
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨s₁, r₁, R₁, v₁⟩ := genB_ok hf σ.env c 0 (by omega) hp1' h hpc hc.1.1.1 ok1 hrel.env
    obtain ⟨s₂, hn⟩ := step_beq_5_0 R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) _
      (codeAt_one (codeAt_mem R₁.mem hc.1.1.2))
    have hcond : bcond 0 (getX s₁ 5) (getX s₁ 0) = true := by
      rw [show getX s₁ 0 = 0 from rfl, show getX s₁ 5 = c.denote σ.env from v₁, hc0]; rfl
    refine ⟨s₂, r₁.trans (Reach.next hn),
      (AF.ofRan7 R₁).trans (AF.ofNext hn (unchangedOutside_of_mem hn.mem) (.inl rfl)), ?_,
      hrel.regs (by rw [hn.mem, R₁.mem]) (fun i => by rw [hn.keep0, R₁.keepA])
        (by rw [hn.keep0, R₁.keep 3 (fun i _ hi => three_ne_T i hi)])⟩
    rw [hn.pc, if_pos hcond, boff_fwd ((compileB bv b).length + 2) (by omega), pc_add]
    congr 3; omega
  | _, σ, σ₂, .loopT (c := c) (b := b) (σ₁ := σ₁) hc0 hb hl, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    have hp' := hp
    simp only [BStmt.wf] at hp'
    obtain ⟨hp1, hp1', hp2, hp3⟩ := hp'
    have hcode := hc
    have hok0 := hok
    have hcd0 := hcd
    rw [compileB] at hc hok hcd
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    simp only [List.length_append, List.length_singleton] at hok hcd
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨s₁, r₁, R₁, v₁⟩ := genB_ok hf σ.env c 0 (by omega) hp1' h hpc hc.1.1.1 ok1 hrel.env
    obtain ⟨s₂, hn⟩ := step_beq_5_0 R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) _
      (codeAt_one (codeAt_mem R₁.mem hc.1.1.2))
    have hcond : bcond 0 (getX s₁ 5) (getX s₁ 0) = false := by
      rw [show getX s₁ 0 = 0 from rfl, show getX s₁ 5 = c.denote σ.env from v₁]; simpa [bcond] using hc0
    have F₂ : AF (R ++ slotRegs N fp) s s₂ :=
      (AF.ofRan7 R₁).trans (AF.ofNext hn (unchangedOutside_of_mem hn.mem) (.inl rfl))
    have hm₂ : s₂.mem = s.mem := by rw [hn.mem, R₁.mem]
    have hrel₂ : Rel2 N fp bv R σ s₂ := hrel.regs hm₂ (fun i => by rw [hn.keep0, R₁.keepA])
      (by rw [hn.keep0, R₁.keep 3 (fun i _ hi => three_ne_T i hi)])
    have hpc₂ : s₂.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * ((genB c 0).length + 1))) := by
      rw [hn.pc, hcond]; simp only [Bool.false_eq_true, if_false]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4 * 1) from rfl, pc_add]
    have e1 := pc_toNat hok (a := (genB c 0).length + 1) (by omega)
    have hcd3 : ∀ r ∈ R ++ slotRegs N fp, disjoint ⟨(pc + BitVec.ofNat 64 (4 * ((genB c 0).length + 1))).toNat,
        4 * (compileB bv b).length⟩ r := disj_sub hcd (by omega) (by omega)
    have hc3 : codeAt s₂ (pc + BitVec.ofNat 64 (4 * ((genB c 0).length + 1))) (compileB bv b) := by
      have := codeAt_mem hm₂ hc.1.2; rwa [List.length_append, List.length_singleton] at this
    obtain ⟨s₃, r₃, F₃, pc₃, v₃⟩ := execB_ok hf bv hbv hR hb hp2 F₂.cfg hpc₂ hc3 ok3 hcd3 hrel₂
    rw [pc_add] at pc₃
    have e4 := pc_toNat hok (a := (genB c 0).length + 1 + (compileB bv b).length) (by omega)
    have hc4 : codeAt s₃ (pc + BitVec.ofNat 64 (4 * ((genB c 0).length + 1 + (compileB bv b).length)))
        [iJmp ((genB c 0).length + 1 + (compileB bv b).length)] := by
      have := codeAt_mem hm₂ hc.2
      rw [List.length_append, List.length_append, List.length_singleton] at this
      exact codeAt_out this ok4 (disj_sub hcd (by simp; omega) (by simp; omega)) F₃.out
    obtain ⟨s₄, hn₄⟩ := step_jal_0 F₃.cfg pc₃ (codeOK_pcOK ok4 (by simp)) _ (codeAt_one hc4)
    have F₄ := (F₂.trans F₃).trans (AF.ofNext hn₄ (unchangedOutside_of_mem hn₄.mem) (.inl rfl))
    have hpc₄ : s₄.regs.get? .PC = some pc := by
      rw [hn₄.pc, joff_back _ (by omega) (by omega), pc_jmp]
    have hrel₄ : Rel2 N fp bv R σ₁ s₄ := v₃.regs hn₄.mem (fun i => by rw [hn₄.keep0]) (hn₄.keep0 3)
    obtain ⟨s₅, r₅, F₅, pc₅, v₅⟩ := execB_ok hf bv hbv hR hl hp F₄.cfg hpc₄ (codeAt_out hcode hok0 hcd0 F₄.out) hok0
      hcd0 hrel₄
    exact ⟨s₅, (((r₁.trans (Reach.next hn)).trans r₃).trans (Reach.next hn₄)).trans r₅, F₄.trans F₅, pc₅, v₅⟩

end Proven
