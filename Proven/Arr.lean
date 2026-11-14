/- Byte arrays: the statement compiler `compileA` (loads, stores, loops over `AExp`) and its correctness
proof on the Sail model.

Memory: the data blocks are contiguous regions `R` (in RAM, pairwise disjoint: `RegOK R`); block `b`'s
contents are `σ.heap[b]`, its base address is held in variable `bv[b]` (`a_(bv[b])`), which the program
never assigns (`AStmt.wf`).  The code region is disjoint from every block. -/
import Proven.ArrExp
import Proven.MemCompiler

set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Proven

/-! ## Compiler -/

def compileA (bv : List (Fin 8)) : AStmt → List (BitVec 32)
  | .assign v e => gen8 e 0 ++ [iMv8 v]
  | .load v b i => gen8 (addrE bv b i) 0 ++ [iLbuT, iMv8 v]
  | .store b i e => gen8 (addrE bv b i) 0 ++ gen8 e 1 ++ [iSbT]
  | .seq p q => compileA bv p ++ compileA bv q
  | .loop c body => gen8 c 0 ++ [iBeqz ((compileA bv body).length + 2)] ++ compileA bv body ++
      [iJmp ((gen8 c 0).length + 1 + (compileA bv body).length)]

/-- as a function: run the statement, then `ret` -/
def compileAF (bv : List (Fin 8)) (p : AStmt) : List (BitVec 32) := compileA bv p ++ [iRet]

/-- expressions fit the 7 temporaries, base variables are never assigned, blocks exist,
loop bodies fit the `beq` range -/
def AStmt.wf (bv : List (Fin 8)) : AStmt → Prop
  | .assign v e => e.depth < 7 ∧ v ∉ bv
  | .load v b i => i.depth < 6 ∧ v ∉ bv ∧ b < bv.length
  | .store b i e => i.depth < 6 ∧ e.depth < 6 ∧ b < bv.length
  | .seq p q => p.wf bv ∧ q.wf bv
  | .loop c body => c.depth < 7 ∧ body.wf bv ∧ (gen8 c 0).length + (compileA bv body).length + 2 < 1024

/-! ## Machine/source relation -/

/-- data regions: in RAM, pairwise disjoint -/
def RegOK (R : List Region) : Prop := (∀ r ∈ R, r.inRAM) ∧ R.Pairwise disjoint

/-- the machine state `s` represents `σ`: variables in `a0..a7`, block `b` = region `R[b]` holding
`σ.heap[b]`, its base address in variable `bv[b]` -/
structure Rel (bv : List (Fin 8)) (R : List Region) (σ : AState) (s : St) : Prop where
  env : ∀ i, getX s (A8 i) = σ.env i
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  bytes : ∀ b (hb : b < R.length), bytesAt s R[b].base R[b].len = (σ.heap[b]?.getD []).map some

/-- `s'` differs from `s` at most in the PC, the temporaries, the variables and the data regions -/
structure AF (R : List Region) (s s' : St) : Prop where
  cfg : Cfg s'
  out : unchangedOutside s s' R
  keep : ∀ j : Fin 32, (∀ i, i < 7 → j ≠ T i) → (∀ i : Fin 8, j ≠ A8 i) → getX s' j = getX s j

theorem AF.trans {R} {s₁ s₂ s₃ : St} (f₁ : AF R s₁ s₂) (f₂ : AF R s₂ s₃) : AF R s₁ s₃ :=
  ⟨f₂.cfg, fun a ha => by rw [f₂.out a ha, f₁.out a ha],
    fun j h1 h2 => by rw [f₂.keep j h1 h2, f₁.keep j h1 h2]⟩

theorem AF.ofRan7 {R} {s s' : St} {pc n} (r : Ran7 s s' pc n 0) : AF R s s' :=
  ⟨r.cfg, fun a _ => by rw [r.mem], fun j h1 _ => r.keep j fun i _ hi => h1 i hi⟩

theorem AF.ofNext {R} {s s' : St} {pc rd v m} (hn : Next s s' pc rd v m) (hu : unchangedOutside s s' R)
    (hrd : rd = 0 ∨ (∃ i : Fin 8, rd = A8 i) ∨ ∃ k, k < 7 ∧ rd = T k) : AF R s s' := by
  refine ⟨hn.cfg, hu, fun j h1 h2 => ?_⟩
  rw [hn.x j]
  rcases hrd with rfl | ⟨i, rfl⟩ | ⟨k, hk, rfl⟩
  · simp
  · simp [h2 i]
  · simp [h1 k hk]

theorem pc4 (pc : BitVec 64) (a : Nat) : pc + BitVec.ofNat 64 (4 * a) + 4 = pc + BitVec.ofNat 64 (4 * (a + 1)) :=
  pc_add pc a 1

theorem pc_eq {pc : BitVec 64} {a b : Nat} (h : a = b) :
    pc + BitVec.ofNat 64 (4 * a) = pc + BitVec.ofNat 64 (4 * b) := by rw [h]

theorem unchangedOutside_of_mem {s s' : St} {R} (h : s'.mem = s.mem) : unchangedOutside s s' R :=
  fun a _ => by rw [h]

theorem hget (H : Heap) {b : Nat} (hb : b < H.length) : H[b]?.getD [] = H[b] := by
  simp [hb]

theorem A8_inj {i j : Fin 8} (h : A8 i = A8 j) : i = j := by
  revert i j; decide
theorem A8_ne_0 (i : Fin 8) : A8 i ≠ 0 := by revert i; decide

theorem getD_mem {bv : List (Fin 8)} {b : Nat} (hb : b < bv.length) : bv.getD b 0 ∈ bv := by
  simp [List.getD_eq_getElem?_getD, hb]

/-- registers changed outside the variables, memory unchanged -/
theorem Rel.regs {bv R σ} {s s' : St} (r : Rel bv R σ s) (hm : s'.mem = s.mem)
    (he : ∀ i, getX s' (A8 i) = getX s (A8 i)) : Rel bv R σ s' :=
  ⟨fun i => by rw [he, r.env], r.hlen, r.bvlen, r.base, r.blen,
    fun b hb => by rw [← r.bytes b hb]; simp only [bytesAt, hm]⟩

/-- one variable (not a base variable) set -/
theorem Rel.setVar {bv R σ} {s s' : St} (r : Rel bv R σ s) (hm : s'.mem = s.mem) {v : Fin 8} (hv : v ∉ bv)
    {x : BitVec 64} (he : ∀ i, getX s' (A8 i) = σ.env.set v x i) : Rel bv R ⟨σ.env.set v x, σ.heap⟩ s' := by
  refine ⟨he, r.hlen, r.bvlen, fun b hb => ?_, r.blen, fun b hb => by rw [← r.bytes b hb]; simp only [bytesAt, hm]⟩
  have : bv.getD b 0 ≠ v := fun e => hv (e ▸ getD_mem (r.bvlen ▸ hb))
  simp only [AEnv.set, if_neg this]; exact r.base b hb

theorem pc_toNat {pc : BitVec 64} {n a : Nat} (h : codeOK pc n) (ha : a ≤ n) :
    (pc + BitVec.ofNat 64 (4 * a)).toNat = pc.toNat + 4 * a := by
  obtain ⟨_, _, h3⟩ := h; simp [BitVec.toNat_add]; omega

/-- code outside the data regions survives -/
theorem codeAt_out {s s' : St} {pc ws} {R : List Region} (hc : codeAt s pc ws) (hok : codeOK pc ws.length)
    (hd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * ws.length⟩ r) (hu : unchangedOutside s s' R) : codeAt s' pc ws := by
  intro i hi
  refine instrAt_frame (hc i hi) fun j hj => hu _ fun r hr => ?_
  have := hd r hr; have e := pc_toNat hok (a := i) (by omega); unfold disjoint at this; dsimp only at this
  rw [e]; omega

theorem disj_sub {R : List Region} {p n p' n' : Nat} (hd : ∀ r ∈ R, disjoint ⟨p, n⟩ r) (h1 : p ≤ p')
    (h2 : p' + n' ≤ p + n) : ∀ r ∈ R, disjoint ⟨p', n'⟩ r := by
  intro r hr; have := hd r hr; unfold disjoint at *; dsimp only at *; omega

theorem mem_of_bytesAt {s : St} {a n : Nat} {l : List (BitVec 8)} (h : bytesAt s a n = l.map some) {i : Nat}
    (hi : i < l.length) : s.mem[a + i]? = some l[i] := by
  have hn : n = l.length := by simpa [bytesAt] using congrArg List.length h
  have := congrArg (·[i]?) h
  simp only [bytesAt, hn, List.getElem?_map, List.getElem?_range hi, List.getElem?_eq_getElem hi,
    Option.map_some] at this
  simpa using this

theorem addr_toNat {base len : Nat} {idx : BitVec 64} (hb : base + len ≤ 2 ^ 32) (hi : idx.toNat < len) :
    (BitVec.ofNat 64 base + idx).toNat = base + idx.toNat := by
  simp [BitVec.toNat_add]; omega

/-- the address of an in-bounds element: value, and RAM bounds -/
theorem addr_ok {bv R σ} {s : St} (r : Rel bv R σ s) (hR : RegOK R) {b : Nat} (hb : b < σ.heap.length)
    {i : AExp} (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
    ∃ hbR : b < R.length, ((addrE bv b i).denote σ.env).toNat = R[b].base + (i.denote σ.env).toNat ∧
      0x80000000 ≤ R[b].base + (i.denote σ.env).toNat ∧ R[b].base + (i.denote σ.env).toNat + 1 ≤ 0x100000000 := by
  have hbR : b < R.length := r.hlen ▸ hb
  have hl := r.blen b hbR; rw [hget _ hb] at hl
  have hram := hR.1 _ (List.getElem_mem hbR); unfold Region.inRAM at hram
  refine ⟨hbR, ?_, by omega, by omega⟩
  simp only [addrE, AExp.denote, Op.eval, r.base b hbR]
  exact addr_toNat (len := R[b].len) (by omega) (by omega)

/-! ## Correctness -/

theorem execA_ok (bv : List (Fin 8)) {R : List Region} (hR : RegOK R) :
    ∀ {p : AStmt} {σ σ' : AState}, AExec p σ σ' → p.wf bv → ∀ {s : St} {pc : BitVec 64}, Cfg s →
    s.regs.get? .PC = some pc → codeAt s pc (compileA bv p) → codeOK pc (compileA bv p).length →
    (∀ r ∈ R, disjoint ⟨pc.toNat, 4 * (compileA bv p).length⟩ r) → Rel bv R σ s →
    ∃ s', Reach s s' ∧ AF R s s' ∧ s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (compileA bv p).length)) ∧
      Rel bv R σ' s'
  | _, σ, _, .assign (v := v) (e := e), hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [compileA, AStmt.wf] at hp hc hok ⊢
    rw [codeAt_append] at hc
    rw [List.length_append] at hok ⊢
    obtain ⟨ok1, ok2⟩ := codeOK_append hok
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen8_ok σ.env e 0 (by omega) h hpc hc.1 ok1 hrel.env
    obtain ⟨s₂, hn⟩ := step_mv8 R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) v (codeAt_one (codeAt_mem R₁.mem hc.2))
    refine ⟨s₂, r₁.trans (Reach.next hn),
      (AF.ofRan7 R₁).trans (AF.ofNext hn (unchangedOutside_of_mem hn.mem) (.inr (.inl ⟨v, rfl⟩))),
      by rw [hn.pc, ← pc_add]; rfl, ?_⟩
    refine Rel.setVar hrel (by rw [hn.mem, R₁.mem]) hp.2 fun i => ?_
    rw [hn.x, R₁.keepA]
    by_cases hiv : i = v
    · subst hiv; simp [AEnv.set, A8_ne_0, ← v₁]; rfl
    · have : A8 i ≠ A8 v := fun e => hiv (A8_inj e)
      rw [if_neg (fun h => this h.1)]; simp only [AEnv.set, if_neg hiv]; exact hrel.env i
  | _, σ, _, .load (v := v) (b := b) (i := i) hb hi, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [compileA, AStmt.wf] at hp hc hok ⊢
    rw [codeAt_append] at hc
    rw [List.length_append] at hok ⊢
    obtain ⟨ok1, ok2⟩ := codeOK_append hok
    obtain ⟨hbR, ha, hram1, hram2⟩ := addr_ok hrel hR hb hi
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen8_ok σ.env (addrE bv b i) 0 (by simp [addrE, AExp.depth]; omega) h hpc hc.1 ok1
      hrel.env
    have hc2 := codeAt_mem R₁.mem hc.2
    have hbyte := mem_of_bytesAt (hrel.bytes b hbR) (i := (i.denote σ.env).toNat)
      (by rw [hget _ hb]; exact hi)
    simp only [hget _ hb] at hbyte
    have h5 : (getX s₁ 5).toNat = R[b].base + (i.denote σ.env).toNat := by
      rw [show (5 : Fin 32) = T 0 from rfl, v₁, ha]
    obtain ⟨s₂, hn₂⟩ := W8.lbuT R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) (by simpa [iLbuT] using hc2 0 (by simp))
      (by rw [h5]; omega) (b := σ.heap[b][(i.denote σ.env).toNat]) (by rw [h5, R₁.mem]; exact hbyte)
    have hpc₂ : s₂.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (gen8 (addrE bv b i) 0).length) +
        BitVec.ofNat 64 (4 * 1)) := hn₂.pc
    obtain ⟨s₃, hn₃⟩ := step_mv8 hn₂.cfg hpc₂ (codeOK_pcOK (codeOK_append (a := 1) (b := 1) ok2).2 (by simp)) v
      (by simpa using (codeAt_mem hn₂.mem hc2) 1 (by simp))
    refine ⟨s₃, (r₁.trans (Reach.next hn₂)).trans (Reach.next hn₃),
      ((AF.ofRan7 R₁).trans (AF.ofNext hn₂ (unchangedOutside_of_mem hn₂.mem) (.inr (.inr ⟨0, by omega, rfl⟩)))).trans
        (AF.ofNext hn₃ (unchangedOutside_of_mem hn₃.mem) (.inr (.inl ⟨v, rfl⟩))),
      by rw [hn₃.pc, pc_add, pc4]; exact congrArg some (pc_eq (by simp)), ?_⟩
    refine Rel.setVar hrel (by rw [hn₃.mem, hn₂.mem, R₁.mem]) hp.2.1 fun j => ?_
    have hx2 : getX s₂ (A8 j) = getX s₁ (A8 j) := by
      rw [hn₂.x (A8 j), if_neg (fun h => T_ne_A8' 0 (by omega) j h.1.symm)]
    rw [hn₃.x]
    by_cases hjv : j = v
    · subst hjv; simp only [true_and, A8_ne_0, ne_eq, not_false_eq_true, if_true, AEnv.set]
      rw [hn₂.x 5]; rfl
    · have : A8 j ≠ A8 v := fun e => hjv (A8_inj e)
      rw [if_neg (fun h => this h.1), hx2, R₁.keepA]; simp only [AEnv.set, if_neg hjv]; exact hrel.env j
  | _, σ, _, .store (b := b) (i := i) (e := e) hb hi, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [compileA, AStmt.wf] at hp hc hok hcd ⊢
    rw [codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append] at hok hcd ⊢
    obtain ⟨ok12, ok3⟩ := codeOK_append hok
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨hbR, ha, hram1, hram2⟩ := addr_ok hrel hR hb hi
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen8_ok σ.env (addrE bv b i) 0 (by simp [addrE, AExp.depth]; omega) h hpc hc.1.1 ok1
      hrel.env
    obtain ⟨s₂, r₂, R₂, v₂⟩ := gen8_ok σ.env e 1 (by omega) R₁.cfg R₁.pc (codeAt_mem R₁.mem hc.1.2) ok2
      (fun j => by rw [R₁.keepA, hrel.env])
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.zero_le _)
    have h5 : (getX s₂ 5).toNat = R[b].base + (i.denote σ.env).toNat := by
      rw [R₂.keep 5 (fun j hj hj7 he => by have := T_inj (i := 0) (j := j) (by omega) (by omega) he; omega)]
      rw [show (5 : Fin 32) = T 0 from rfl, v₁, ha]
    have hc3 := codeAt_mem R₁₂.mem hc.2
    rw [List.length_append] at hc3
    obtain ⟨s₃, hn₃⟩ := W8.sbT R₁₂.cfg R₁₂.pc (codeOK_pcOK ok3 (by simp)) (by simpa [iSbT] using hc3 0 (by simp))
      (by rw [h5]; omega)
    rw [h5, show (6 : Fin 32) = T 1 from rfl, v₂] at hn₃
    have hk : b < R.length := hbR
    have hil : (i.denote σ.env).toNat < R[b].len := by
      have := hrel.blen b hbR; rw [hget _ hb] at this; omega
    obtain ⟨st1, st2, st3⟩ := Next.store_region hR.1 hR.2 hk hil hn₃
    have hu : unchangedOutside s s₃ R := fun a ha' => by
      rw [st3 a (by simpa using ha' _ (List.getElem_mem hbR)), R₁₂.mem]
    refine ⟨s₃, ((r₁.trans r₂).trans (Reach.next hn₃)),
      (AF.ofRan7 R₁₂).trans (AF.ofNext hn₃ (fun a ha' => by
        rw [st3 a (by simpa using ha' _ (List.getElem_mem hbR))]) (.inl rfl)),
      by rw [hn₃.pc, pc4]; exact congrArg some (pc_eq (by simp)), ?_⟩
    have hx : ∀ j, getX s₃ (A8 j) = getX s (A8 j) := fun j => by
      rw [hn₃.x, if_neg (fun h => h.2 h.1), R₁₂.keepA]
    refine ⟨fun j => by rw [hx, hrel.env], by rw [List.length_set, hrel.hlen], hrel.bvlen, hrel.base,
      fun b' hb' => ?_, fun b' hb' => ?_⟩
    · by_cases hbb : b' = b
      · subst hbb
        have := hrel.blen b' hb'; rw [hget _ hb] at this
        simpa [List.getElem?_set, hb] using this
      · simp only [List.getElem?_set, Ne.symm hbb, if_false]; exact hrel.blen b' hb'
    · by_cases hbb : b' = b
      · subst hbb
        rw [st1]
        have e1 : bytesAt s₂ R[b'].base R[b'].len = bytesAt s R[b'].base R[b'].len := by
          simp only [bytesAt, R₁₂.mem]
        rw [e1, hrel.bytes b' hb', hget _ hb]
        simp [List.getElem?_set, hb, List.map_set]
      · rw [st2 b' hb' hbb]
        have e1 : bytesAt s₂ R[b'].base R[b'].len = bytesAt s R[b'].base R[b'].len := by
          simp only [bytesAt, R₁₂.mem]
        rw [e1, hrel.bytes b' hb']
        simp only [List.getElem?_set, Ne.symm hbb, if_false]
  | _, σ, _, .seq (p := a) (q := b) ha hb, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [compileA, AStmt.wf] at hp hc hok hcd ⊢
    rw [codeAt_append] at hc
    rw [List.length_append] at hok hcd ⊢
    obtain ⟨ok1, ok2⟩ := codeOK_append hok
    have e := pc_toNat hok (a := (compileA bv a).length) (by omega)
    obtain ⟨s₁, r₁, F₁, pc₁, v₁⟩ := execA_ok bv hR ha hp.1 h hpc hc.1 ok1
      (disj_sub hcd (Nat.le_refl _) (by omega)) hrel
    obtain ⟨s₂, r₂, F₂, pc₂, v₂⟩ := execA_ok bv hR hb hp.2 F₁.cfg pc₁
      (codeAt_out hc.2 ok2 (disj_sub hcd (by omega) (by omega)) F₁.out) ok2 (disj_sub hcd (by omega) (by omega)) v₁
    exact ⟨s₂, r₁.trans r₂, F₁.trans F₂, by rw [pc₂, pc_add], v₂⟩
  | _, σ, _, .loopF (c := c) (b := b) hc0, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    simp only [AStmt.wf] at hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    rw [compileA] at hc hok ⊢
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    simp only [List.length_append, List.length_singleton] at hok ⊢
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen8_ok σ.env c 0 (by omega) h hpc hc.1.1.1 ok1 hrel.env
    obtain ⟨s₂, hn⟩ := step_beq_5_0 R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) _
      (codeAt_one (codeAt_mem R₁.mem hc.1.1.2))
    have hcond : bcond 0 (getX s₁ 5) (getX s₁ 0) = true := by
      rw [show getX s₁ 0 = 0 from rfl, show getX s₁ 5 = c.denote σ.env from v₁, hc0]; rfl
    refine ⟨s₂, r₁.trans (Reach.next hn),
      (AF.ofRan7 R₁).trans (AF.ofNext hn (unchangedOutside_of_mem hn.mem) (.inl rfl)), ?_,
      hrel.regs (by rw [hn.mem, R₁.mem]) fun i => by rw [hn.keep0, R₁.keepA]⟩
    rw [hn.pc, if_pos hcond, boff_fwd ((compileA bv b).length + 2) (by omega), pc_add]
    congr 3; omega
  | _, σ, σ₂, .loopT (c := c) (b := b) (σ₁ := σ₁) hc0 hb hl, hp, s, pc, h, hpc, hc, hok, hcd, hrel => by
    have hp' := hp
    simp only [AStmt.wf] at hp'
    obtain ⟨hp1, hp2, hp3⟩ := hp'
    have hcode := hc
    have hok0 := hok
    have hcd0 := hcd
    rw [compileA] at hc hok hcd
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    simp only [List.length_append, List.length_singleton] at hok hcd
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen8_ok σ.env c 0 (by omega) h hpc hc.1.1.1 ok1 hrel.env
    obtain ⟨s₂, hn⟩ := step_beq_5_0 R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) _
      (codeAt_one (codeAt_mem R₁.mem hc.1.1.2))
    have hcond : bcond 0 (getX s₁ 5) (getX s₁ 0) = false := by
      rw [show getX s₁ 0 = 0 from rfl, show getX s₁ 5 = c.denote σ.env from v₁]; simpa [bcond] using hc0
    have F₂ : AF R s s₂ := (AF.ofRan7 R₁).trans (AF.ofNext hn (unchangedOutside_of_mem hn.mem) (.inl rfl))
    have hm₂ : s₂.mem = s.mem := by rw [hn.mem, R₁.mem]
    have hrel₂ : Rel bv R σ s₂ := hrel.regs hm₂ fun i => by rw [hn.keep0, R₁.keepA]
    have hpc₂ : s₂.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * ((gen8 c 0).length + 1))) := by
      rw [hn.pc, hcond]; simp only [Bool.false_eq_true, if_false]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4 * 1) from rfl, pc_add]
    have e1 := pc_toNat hok (a := (gen8 c 0).length + 1) (by omega)
    have hcd3 : ∀ r ∈ R, disjoint ⟨(pc + BitVec.ofNat 64 (4 * ((gen8 c 0).length + 1))).toNat,
        4 * (compileA bv b).length⟩ r := disj_sub hcd (by omega) (by omega)
    have hc3 : codeAt s₂ (pc + BitVec.ofNat 64 (4 * ((gen8 c 0).length + 1))) (compileA bv b) := by
      have := codeAt_mem hm₂ hc.1.2; rwa [List.length_append, List.length_singleton] at this
    obtain ⟨s₃, r₃, F₃, pc₃, v₃⟩ := execA_ok bv hR hb hp2 F₂.cfg hpc₂ hc3 ok3 hcd3 hrel₂
    rw [pc_add] at pc₃
    have e4 := pc_toNat hok (a := (gen8 c 0).length + 1 + (compileA bv b).length) (by omega)
    have hc4 : codeAt s₃ (pc + BitVec.ofNat 64 (4 * ((gen8 c 0).length + 1 + (compileA bv b).length)))
        [iJmp ((gen8 c 0).length + 1 + (compileA bv b).length)] := by
      have := codeAt_mem hm₂ hc.2
      rw [List.length_append, List.length_append, List.length_singleton] at this
      exact codeAt_out this ok4 (disj_sub hcd (by simp; omega) (by simp; omega)) F₃.out
    obtain ⟨s₄, hn₄⟩ := step_jal_0 F₃.cfg pc₃ (codeOK_pcOK ok4 (by simp)) _ (codeAt_one hc4)
    have F₄ := (F₂.trans F₃).trans (AF.ofNext hn₄ (unchangedOutside_of_mem hn₄.mem) (.inl rfl))
    have hpc₄ : s₄.regs.get? .PC = some pc := by
      rw [hn₄.pc, joff_back _ (by omega) (by omega), pc_jmp]
    have hrel₄ : Rel bv R σ₁ s₄ := v₃.regs hn₄.mem fun i => by rw [hn₄.keep0]
    obtain ⟨s₅, r₅, F₅, pc₅, v₅⟩ := execA_ok bv hR hl hp F₄.cfg hpc₄ (codeAt_out hcode hok0 hcd0 F₄.out) hok0
      hcd0 hrel₄
    exact ⟨s₅, (((r₁.trans (Reach.next hn)).trans r₃).trans (Reach.next hn₄)).trans r₅, F₄.trans F₅, pc₅, v₅⟩

end Proven

namespace Proven

theorem calleeSaved_of_AF {R} {s s' : St} (h : Cfg s) (f : AF R s s') : calleeSavedKept s s' := by
  have ne : ∀ j ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)),
      (∀ i, i < 7 → j ≠ T i) ∧ ∀ i : Fin 8, j ≠ A8 i := by decide
  have k : ∀ j ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)), getX s' j = getX s j :=
    fun j hj => f.keep j (ne j hj).1 (ne j hj).2
  have h₃ := f.cfg
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₃.x2, h.x2, k 2 (by decide)]
  · rw [h₃.x8, h.x8, k 8 (by decide)]
  · rw [h₃.x9, h.x9, k 9 (by decide)]
  · rw [h₃.x18, h.x18, k 18 (by decide)]
  · rw [h₃.x19, h.x19, k 19 (by decide)]
  · rw [h₃.x20, h.x20, k 20 (by decide)]
  · rw [h₃.x21, h.x21, k 21 (by decide)]
  · rw [h₃.x22, h.x22, k 22 (by decide)]
  · rw [h₃.x23, h.x23, k 23 (by decide)]
  · rw [h₃.x24, h.x24, k 24 (by decide)]
  · rw [h₃.x25, h.x25, k 25 (by decide)]
  · rw [h₃.x26, h.x26, k 26 (by decide)]
  · rw [h₃.x27, h.x27, k 27 (by decide)]

/-- **Correctness of `compileA`**: if the source program `p` terminates from `σ` in `σ'` (so every load
and store was in bounds) and the machine state represents `σ` (`Rel`: variables in `a0..a7`, block `b` in
region `R[b]`, its base in `a_(bv[b])`), with in-RAM pairwise disjoint data regions and code outside them,
the Sail model runs the code to its end with a state representing `σ'`, memory outside the data regions
unchanged, callee-saved registers and `Cfg` kept. -/
theorem compileA_ok (bv : List (Fin 8)) {p : AStmt} (hp : p.wf bv) {R : List Region} (hR : RegOK R)
    {σ σ' : AState} (hex : AExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileA bv p)) (hok : codeOK pc (compileA bv p).length)
    (hcd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * (compileA bv p).length⟩ r) (hrel : Rel bv R σ s) :
    runsTo s fun s' => s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (compileA bv p).length)) ∧
      Rel bv R σ' s' ∧ unchangedOutside s s' R ∧ Cfg s' ∧ calleeSavedKept s s' := by
  obtain ⟨s', r, F, hpc', v⟩ := execA_ok bv hR hex hp h hpc hc hok hcd hrel
  exact runsTo_of_reach r ⟨hpc', v, F.out, F.cfg, calleeSaved_of_AF h F⟩

/-- **Correctness of `compileAF`** (a called function): as `compileA_ok`, returning to `ra`. -/
theorem compileAF_ok (bv : List (Fin 8)) {p : AStmt} (hp : p.wf bv) {R : List Region} (hR : RegOK R)
    {σ σ' : AState} (hex : AExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileAF bv p)) (hok : codeOK pc (compileAF bv p).length)
    (hcd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * (compileAF bv p).length⟩ r) (hrel : Rel bv R σ s)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      Rel bv R σ' s' ∧ unchangedOutside s s' R ∧ Cfg s' ∧ calleeSavedKept s s' := by
  simp only [compileAF] at hc hok hcd
  rw [codeAt_append] at hc
  rw [List.length_append] at hok hcd
  obtain ⟨ok1, ok2⟩ := codeOK_append hok
  obtain ⟨s₁, r₁, F₁, pc₁, v₁⟩ := execA_ok bv hR hex hp h hpc hc.1 ok1 (disj_sub hcd (Nat.le_refl _) (by omega)) hrel
  have e := pc_toNat hok (a := (compileA bv p).length) (by omega)
  have hra₁ : getX s₁ 1 = getX s 1 := F₁.keep 1 (by decide) (by decide)
  obtain ⟨s₂, hn⟩ := step_ret F₁.cfg pc₁ (codeOK_pcOK ok2 (by simp))
    (codeAt_one (codeAt_out hc.2 ok2 (disj_sub hcd (by omega) (by omega)) F₁.out)) (by rw [hra₁]; exact hra)
  have F₂ := F₁.trans (AF.ofNext hn (unchangedOutside_of_mem hn.mem) (.inl rfl))
  exact runsTo_of_reach (r₁.trans (Reach.next hn)) ⟨by rw [hn.pc, hra₁],
    v₁.regs hn.mem (fun i => hn.keep0 _), F₂.out, F₂.cfg, calleeSaved_of_AF h F₂⟩

/-- loops via an invariant and a measure -/
theorem AExec.loop_inv {c : AExp} {b : AStmt} (I Q : AState → Prop) (μ : AState → Nat)
    (hstep : ∀ σ, I σ → c.denote σ.env ≠ 0 → ∃ σ₁, AExec b σ σ₁ ∧ I σ₁ ∧ μ σ₁ < μ σ)
    (hexit : ∀ σ, I σ → c.denote σ.env = 0 → Q σ) : ∀ σ, I σ → ∃ σ', AExec (.loop c b) σ σ' ∧ Q σ' := by
  intro σ
  induction h : μ σ using Nat.strongRecOn generalizing σ with
  | ind n ih =>
    intro hI
    by_cases hc : c.denote σ.env = 0
    · exact ⟨σ, .loopF hc, hexit σ hI hc⟩
    · obtain ⟨σ₁, hb, hI₁, hlt⟩ := hstep σ hI hc
      obtain ⟨σ', hl, hQ⟩ := ih _ (h ▸ hlt) σ₁ rfl hI₁
      exact ⟨σ', .loopT hc hb hl, hQ⟩

end Proven
