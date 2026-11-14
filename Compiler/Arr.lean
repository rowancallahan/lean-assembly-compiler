/- Middle layer, byte arrays: `AStmt` (`Proven/ArrCode.lean`: 8 variables, byte loads/stores into named
blocks, `while`) to abstract operations, and its correctness from the interface laws only.

Variables `v_i` live in `avar i` (`r11 .. r14`, `r7 .. r10`), expression temporaries are `r0 .. r6`;
block `b` is region `R[b]`, its base address held in variable `bv[b]` (never assigned). -/
import Compiler.Exp
import Compiler.Mem

namespace Proven.Mach

theorem varsOK7 : ∀ e : AExp, varsOK 7 e
  | .var i => avar_ge i
  | .const _ => trivial
  | .bin _ a b => ⟨varsOK7 a, varsOK7 b⟩
  | .ite c a b => ⟨varsOK7 c, varsOK7 a, varsOK7 b⟩

theorem movA (v : Fin 8) : MovOK (avar v) (rk 0) := by
  have := avar_ge v; unfold MovOK; rw [rk_val (by omega)]; omega

namespace Machine
variable (M : Machine)

def compA (bv : List (Fin 8)) : AStmt → List AOp
  | .assign v e => mgen8 e 0 ++ [.mov (avar v) (rk 0)]
  | .load v b i => mgen8 (addrE bv b i) 0 ++ [.lbu (rk 0) (rk 0), .mov (avar v) (rk 0)]
  | .store b i e => mgen8 (addrE bv b i) 0 ++ mgen8 e 1 ++ [.sb (rk 1) (rk 0)]
  | .seq p q => compA bv p ++ compA bv q
  | .loop c body => mgen8 c 0 ++ [.bz (rk 0) ((M.code (compA bv body)).length + M.lenBz + M.lenJmp)] ++
      compA bv body ++ [.jmp ((M.code (mgen8 c 0)).length + M.lenBz + (M.code (compA bv body)).length)]

def compAF (bv : List (Fin 8)) (p : AStmt) : List AOp := M.compA bv p ++ [.ret]

def wfA (bv : List (Fin 8)) : AStmt → Prop
  | .assign v e => e.depth < 7 ∧ v ∉ bv
  | .load v b i => i.depth < 6 ∧ v ∉ bv ∧ b < bv.length
  | .store b i e => i.depth < 6 ∧ e.depth < 6 ∧ b < bv.length
  | .seq p q => wfA bv p ∧ wfA bv q
  | .loop c body => c.depth < 7 ∧ wfA bv body ∧
      M.bzOK ((M.code (M.compA bv body)).length + M.lenBz + M.lenJmp) ∧
      M.jmpOK ((M.code (mgen8 c 0)).length + M.lenBz + (M.code (M.compA bv body)).length)

/-- data regions: in RAM, pairwise disjoint -/
def RegOK (R : List Region) : Prop := (∀ r ∈ R, M.inDat r.base r.len) ∧ R.Pairwise disjoint

/-- the machine state represents `σ` -/
structure Rel (bv : List (Fin 8)) (R : List Region) (σ : AState) (s : M.S) : Prop where
  env : ∀ i, M.get s (avar i) = σ.env i
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  bytes : ∀ b (hb : b < R.length), bytes (M.mem s) R[b].base R[b].len = (σ.heap[b]?.getD []).map some

theorem Rel.regs {bv R σ} {s s' : M.S} (r : M.Rel bv R σ s) (hm : M.mem s' = M.mem s)
    (he : ∀ i, M.get s' (avar i) = M.get s (avar i)) : M.Rel bv R σ s' :=
  ⟨fun i => by rw [he, r.env], r.hlen, r.bvlen, r.base, r.blen, fun b hb => by rw [hm]; exact r.bytes b hb⟩

theorem Rel.setVar {bv R σ} {s s' : M.S} (r : M.Rel bv R σ s) (hm : M.mem s' = M.mem s) {v : Fin 8} (hv : v ∉ bv)
    {x : BitVec 64} (he : ∀ i, M.get s' (avar i) = σ.env.set v x i) : M.Rel bv R ⟨σ.env.set v x, σ.heap⟩ s' := by
  refine ⟨he, r.hlen, r.bvlen, fun b hb => ?_, r.blen, fun b hb => by rw [hm]; exact r.bytes b hb⟩
  have : bv.getD b 0 ≠ v := fun e => hv (e ▸ getD_mem bv (r.bvlen ▸ hb))
  show (if bv.getD b 0 = v then x else σ.env (bv.getD b 0)) = _
  rw [ite_neg this]; exact r.base b hb

/-- code outside the data regions survives -/
theorem codeAt_out {s s' : M.S} {pc ws} {R : List Region} (hc : M.codeAt s pc ws) (hok : M.codeOK pc ws.length)
    (hd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * ws.length⟩ r) (hu : Out R (M.mem s) (M.mem s')) : M.codeAt s' pc ws := by
  intro i hi
  refine M.instrAt_frame (fun j hj => hu _ fun r hr => ?_) (hc i hi)
  have := hd r hr; have e := M.pc_toNat hok (a := i) (by omega)
  unfold disjoint at this; dsimp only at this
  show (next pc i).toNat + j < r.base ∨ r.base + r.len ≤ (next pc i).toNat + j
  rw [e]; omega

theorem disj_sub {R : List Region} {p n p' n' : Nat} (hd : ∀ r ∈ R, disjoint ⟨p, n⟩ r) (h1 : p ≤ p')
    (h2 : p' + n' ≤ p + n) : ∀ r ∈ R, disjoint ⟨p', n'⟩ r := by
  intro r hr; have := hd r hr; unfold disjoint at *; dsimp only at *; omega

/-- the address of an in-bounds element -/
theorem addr_ok {bv R σ} {s : M.S} (r : M.Rel bv R σ s) (hR : M.RegOK R) {b : Nat} (hb : b < σ.heap.length)
    {i : AExp} (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
    ∃ hbR : b < R.length, ((addrE bv b i).denote σ.env).toNat = R[b].base + (i.denote σ.env).toNat ∧
      M.inDat (R[b].base + (i.denote σ.env).toNat) 1 := by
  have hbR : b < R.length := r.hlen ▸ hb
  have hl := r.blen b hbR; rw [getD_get _ hb] at hl
  have hram := hR.1 _ (List.getElem_mem hbR)
  have hlt := M.datHi_lt
  obtain ⟨h1, h2⟩ := hram
  have h1' : M.datLo ≤ R[b].base := h1
  have h2' : R[b].base + R[b].len ≤ M.datHi := h2
  refine ⟨hbR, ?_, ⟨by omega, by omega⟩⟩
  show (σ.env (bv.getD b 0) + i.denote σ.env).toNat = _
  rw [r.base b hbR, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := R[b].base) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem code_two (a b : AOp) : M.code [a, b] = M.enc a ++ M.enc b := by
  show M.enc a ++ (M.enc b ++ []) = _; rw [List.append_nil]

theorem code_loopA (bv : List (Fin 8)) (c : AExp) (b : AStmt) : M.code (M.compA bv (.loop c b)) =
    M.code (mgen8 c 0) ++ M.enc (.bz (rk 0) ((M.code (M.compA bv b)).length + M.lenBz + M.lenJmp)) ++
    M.code (M.compA bv b) ++ M.enc (.jmp ((M.code (mgen8 c 0)).length + M.lenBz + (M.code (M.compA bv b)).length)) := by
  simp only [compA, code_append, code_one]

theorem len_loopA (bv : List (Fin 8)) (c : AExp) (b : AStmt) : (M.code (M.compA bv (.loop c b))).length =
    (M.code (mgen8 c 0)).length + M.lenBz + (M.code (M.compA bv b)).length + M.lenJmp := by
  rw [code_loopA]; simp only [List.length_append, M.len_bz, M.len_jmp]

theorem avar_ne_rk0 (j : Fin 8) : avar j ≠ rk 0 := fun e => by
  have := avar_ge j; rw [e, rk_val (by omega)] at this; omega

theorem execA_ok (bv : List (Fin 8)) {R : List Region} (hR : M.RegOK R) :
    ∀ {p : AStmt} {σ σ' : AState}, AExec p σ σ' → M.wfA bv p → ∀ {s : M.S} {pc : BitVec 64},
    M.At s pc (M.code (M.compA bv p)) → (∀ r ∈ R, disjoint ⟨pc.toNat, 4 * (M.code (M.compA bv p)).length⟩ r) →
    M.Rel bv R σ s →
    M.runsTo s fun s' => M.Done s s' (next pc (M.code (M.compA bv p)).length) ∧ Out R (M.mem s) (M.mem s') ∧
      M.Rel bv R σ' s'
  | _, σ, _, .assign (v := v) (e := e), hp, s, pc, hA, hcd, hrel => by
    simp only [compA, wfA, code_append, code_one, List.length_append] at hp hA hcd ⊢
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
    rw [← next_add]
    refine M.seq_run (M.gen_ok 7 (.inl rfl) σ.env e 0 (by omega) (varsOK7 e) hA1 fun i _ => hrel.env i)
      fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    refine M.runsTo_mono (M.law_mov (movA v) (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
      fun s₂ ⟨d₂, st, m₂⟩ => ⟨d₂, Out.of_eq (m₂.trans m₁), Rel.setVar M hrel (m₂.trans m₁) hp.2 fun i => ?_⟩
    rw [st (avar i)]
    by_cases hiv : i = v
    · subst hiv; rw [ite_pos rfl, v₁]; show _ = if i = i then _ else _; rw [ite_pos rfl]
    · rw [ite_neg (fun e => hiv (avar_inj e)), k₁ _ (.inr (avar_ge i)), hrel.env]
      show _ = if i = v then _ else _; rw [ite_neg hiv]
  | _, σ, _, .load (v := v) (b := b) (i := i) hb hi, hp, s, pc, hA, hcd, hrel => by
    simp only [compA, wfA, code_append, code_two, List.length_append] at hp hA hcd ⊢
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
    obtain ⟨hbR, ha, hram⟩ := M.addr_ok hrel hR hb hi
    have hB : bytes (M.mem s) R[b].base R[b].len = σ.heap[b].map some := by
      rw [← getD_get _ hb]; exact hrel.bytes b hbR
    have hbyte := get_of_bytes hB hi
    rw [← next_add, ← next_add]
    refine M.seq_run (M.gen_ok 7 (.inl rfl) σ.env (addrE bv b i) 0 (by simp only [addrE, AExp.depth]; omega)
      (varsOK7 _) hA1 fun j _ => hrel.env j) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    obtain ⟨hA2, hc3, ho3⟩ := Core.At.split _ (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2)
    refine M.seq_run (M.law_lbu (v := σ.heap[b][(i.denote σ.env).toNat]) (rk_val (by omega)) (rk_val (by omega)) hA2 (by rw [v₁, ha]; exact hram)
      (by rw [m₁, v₁, ha]; exact hbyte)) fun s₂ d₂ ⟨st₂, m₂⟩ => ?_
    refine M.runsTo_mono (M.law_mov (movA v) (Core.Done.at _ d₂ (M.codeAt_mem m₂ hc3) ho3))
      fun s₃ ⟨d₃, st₃, m₃⟩ => ⟨d₃, Out.of_eq (m₃.trans (m₂.trans m₁)),
        Rel.setVar M hrel (m₃.trans (m₂.trans m₁)) hp.2.1 fun j => ?_⟩
    rw [st₃ (avar j)]
    by_cases hjv : j = v
    · subst hjv; rw [ite_pos rfl, Core.Set1.same _ st₂]; show _ = if j = j then _ else _; rw [ite_pos rfl]
    · rw [ite_neg (fun e => hjv (avar_inj e)), Core.Set1.other _ st₂ (avar_ne_rk0 j), k₁ _ (.inr (avar_ge j)),
        hrel.env]
      show _ = if j = v then _ else _; rw [ite_neg hjv]
  | _, σ, _, .store (b := b) (i := i) (e := e) hb hi, hp, s, pc, hA, hcd, hrel => by
    simp only [compA, wfA, code_append, code_one, List.length_append] at hp hA hcd ⊢
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    obtain ⟨hbR, ha, hram⟩ := M.addr_ok hrel hR hb hi
    have hil : (i.denote σ.env).toNat < R[b].len := by
      have := hrel.blen b hbR; rw [getD_get _ hb] at this; omega
    rw [← next_add, ← next_add]
    refine M.runsTo_trans (M.gen_ok 7 (.inl rfl) σ.env (addrE bv b i) 0 (by simp only [addrE, AExp.depth]; omega)
      (varsOK7 _) hA1 fun j _ => hrel.env j) fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    refine M.runsTo_trans (M.gen_ok 7 (.inl rfl) σ.env e 1 (by omega) (varsOK7 e)
      (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) fun j _ => by rw [k₁ _ (.inr (avar_ge j)), hrel.env])
      fun s₂ ⟨d₂, m₂, v₂, k₂⟩ => ?_
    have a₂ : M.get s₂ (rk 0) = (addrE bv b i).denote σ.env := by
      rw [k₂ _ (.inl (by rw [rk_val (by omega)]; omega)), v₁]
    refine M.runsTo_mono (M.law_sb (rk_val (by omega)) (rk_val (by omega))
      (Core.Done.at _ d₂ (M.codeAt_mem (m₂.trans m₁) hc3) ho3) (by rw [a₂, ha]; exact hram))
      fun s₃ ⟨d₃, st₃, m₃⟩ => ⟨Core.Done.trans _ d₁ (Core.Done.trans _ d₂ d₃), ?_, ?_⟩
    · rw [a₂, ha, v₂, m₂, m₁] at m₃
      intro x hx
      rw [m₃]; unfold Mem.upd
      have := hx _ (List.getElem_mem hbR)
      rw [ite_neg (by omega)]
    · rw [a₂, ha, v₂, m₂, m₁] at m₃
      refine ⟨fun j => by rw [st₃ (avar j), k₂ _ (.inr (avar_ge j)), k₁ _ (.inr (avar_ge j)), hrel.env],
        by rw [List.length_set, hrel.hlen], hrel.bvlen, hrel.base, fun b' hb' => ?_, fun b' hb' => ?_⟩
      · by_cases hbb : b' = b
        · subst hbb
          rw [getD_set_self _ _ hb, List.length_set, ← getD_get _ hb]; exact hrel.blen b' hb'
        · rw [getD_set_ne _ _ hbb]; exact hrel.blen b' hb'
      · by_cases hbb : b' = b
        · subst hbb
          rw [m₃, bytes_upd_in hil, hrel.bytes b' hb', getD_set_self _ _ hb, map_set, getD_get _ hb]
        · have hd := pairwise_get hR.2 hb' hbR hbb
          have hil' : (i.denote σ.env).toNat < R[b].len := hil
          unfold disjoint at hd
          rw [m₃, bytes_upd_out (fun j hj => by omega), hrel.bytes b' hb', getD_set_ne _ _ hbb]
  | _, σ, _, .seq (p := p) (q := q) hpx hqx, hp, s, pc, hA, hcd, hrel => by
    simp only [compA, wfA, code_append, List.length_append] at hp hA hcd ⊢
    have e := M.pc_toNat hA.codeOK (a := (M.code (M.compA bv p)).length) (by rw [List.length_append]; omega)
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
    have hcd₂ := disj_sub (p' := (next pc (M.code (M.compA bv p)).length).toNat) (n' := 4 * (M.code (M.compA bv q)).length)
      hcd (by rw [e]; omega) (by rw [e]; omega)
    rw [← next_add]
    refine M.runsTo_trans (execA_ok bv hR hpx hp.1 hA1 (disj_sub hcd (Nat.le_refl _) (by omega)) hrel)
      fun s₁ ⟨d₁, o₁, r₁⟩ => ?_
    exact M.runsTo_mono (execA_ok bv hR hqx hp.2 (Core.Done.at _ d₁ (M.codeAt_out hc2 ho2 hcd₂ o₁) ho2) hcd₂ r₁)
      fun s₂ ⟨d₂, o₂, r₂⟩ => ⟨Core.Done.trans _ d₁ d₂, o₁.trans o₂, r₂⟩
  | _, σ, _, .loopF (c := c) (b := body) hc0, hp, s, pc, hA, hcd, hrel => by
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    rw [code_loopA] at hA
    rw [len_loopA]
    obtain ⟨hA123, -, -⟩ := Core.At.split _ hA
    obtain ⟨hA12, -, -⟩ := Core.At.split _ hA123
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    refine M.seq_run (M.gen_ok 7 (.inl rfl) σ.env c 0 (by omega) (varsOK7 c) hA1 fun j _ => hrel.env j)
      fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    refine M.runsTo_mono (M.law_bz (rk_val (by omega)) hp3 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
      fun s₂ ⟨d₂, st, m₂⟩ => ⟨?_, Out.of_eq (m₂.trans m₁),
        Rel.regs M hrel (m₂.trans m₁) fun j => by rw [st, k₁ _ (.inr (avar_ge j))]⟩
    rw [v₁, ite_pos hc0, next_add] at d₂
    rw [show (M.code (mgen8 c 0)).length + M.lenBz + (M.code (M.compA bv body)).length + M.lenJmp =
      (M.code (mgen8 c 0)).length + ((M.code (M.compA bv body)).length + M.lenBz + M.lenJmp) by omega]
    exact d₂
  | _, σ, σ₂, .loopT (c := c) (b := body) (σ₁ := σ₁) hc0 hb hl, hp, s, pc, hA, hcd, hrel => by
    have hp' := hp
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp'
    have hA0 := hA
    have hcd0 := hcd
    rw [code_loopA] at hA
    rw [len_loopA] at hcd
    have hok := hA0.codeOK
    rw [len_loopA] at hok
    obtain ⟨hA123, hc4, ho4⟩ := Core.At.split _ hA
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA123
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    simp only [List.length_append, M.len_bz] at hc3 ho3 hc4 ho4
    have e3 := M.pc_toNat hok (a := (M.code (mgen8 c 0)).length + M.lenBz) (by omega)
    have e4 := M.pc_toNat hok (a := (M.code (mgen8 c 0)).length + M.lenBz + (M.code (M.compA bv body)).length)
      (by omega)
    refine M.runsTo_trans (M.gen_ok 7 (.inl rfl) σ.env c 0 (by omega) (varsOK7 c) hA1 fun j _ => hrel.env j)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hp3 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_neg hc0, M.len_bz, next_add] at d₂
    have m₂₀ := m₂.trans m₁
    have hrel₂ : M.Rel bv R σ s₂ := Rel.regs M hrel m₂₀ fun j => by rw [st₂, k₁ _ (.inr (avar_ge j))]
    have hcd3 := disj_sub (p' := (next pc ((M.code (mgen8 c 0)).length + M.lenBz)).toNat)
      (n' := 4 * (M.code (M.compA bv body)).length) hcd (by rw [e3]; omega) (by rw [e3]; omega)
    refine M.runsTo_trans (execA_ok bv hR hb hp2 (Core.Done.at _ d₂ (M.codeAt_mem m₂₀ hc3) ho3) hcd3 hrel₂)
      fun s₃ ⟨d₃, o₃, r₃⟩ => ?_
    rw [next_add] at d₃
    have o₃' : Out R (M.mem s) (M.mem s₃) := (Out.of_eq m₂₀).trans o₃
    have hcd4 := disj_sub (p' := (next pc ((M.code (mgen8 c 0)).length + M.lenBz +
      (M.code (M.compA bv body)).length)).toNat) (n' := 4 * (M.enc (.jmp ((M.code (mgen8 c 0)).length + M.lenBz +
      (M.code (M.compA bv body)).length))).length) hcd (by rw [e4]; omega) (by rw [e4, M.len_jmp]; omega)
    refine M.runsTo_trans (M.law_jmp hp4 (Core.Done.at _ d₃ (M.codeAt_out hc4 ho4 hcd4 o₃') ho4))
      fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
    rw [next_jmp] at d₄
    have o₄ : Out R (M.mem s) (M.mem s₄) := o₃'.trans (Out.of_eq m₄)
    refine M.runsTo_mono (execA_ok bv hR hl hp (Core.Done.at _ d₄ (M.codeAt_out hA0.code hA0.codeOK hcd0 o₄)
      hA0.codeOK) hcd0 (Rel.regs M r₃ m₄ fun j => st₄ _)) fun s₅ ⟨d₅, o₅, r₅⟩ => ⟨?_, o₄.trans o₅, r₅⟩
    exact Core.Done.trans _ d₁ (Core.Done.trans _ d₂ (Core.Done.trans _ d₃ (Core.Done.trans _ d₄ d₅)))

/-- **`AStmt` compiler correctness from the interface laws** (as a function: return to `ra`). -/
theorem compAF_ok (bv : List (Fin 8)) {p : AStmt} (hp : M.wfA bv p) {R : List Region} (hR : M.RegOK R)
    {σ σ' : AState} (hex : AExec p σ σ') {s : M.S} {pc : BitVec 64} (hA : M.At s pc (M.code (M.compAF bv p)))
    (hcd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * (M.code (M.compAF bv p)).length⟩ r) (hrel : M.Rel bv R σ s)
    (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ M.Rel bv R σ' s' ∧ Out R (M.mem s) (M.mem s') ∧ M.ok s' ∧
      M.keep s s' := by
  simp only [compAF, code_append, code_one, List.length_append] at hA hcd
  have e := M.pc_toNat hA.codeOK (a := (M.code (M.compA bv p)).length) (by rw [List.length_append]; omega)
  obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
  have hcd₂ := disj_sub (p' := (next pc (M.code (M.compA bv p)).length).toNat) (n' := 4 * (M.enc .ret).length)
    hcd (by rw [e]; omega) (by rw [e]; omega)
  refine M.runsTo_trans (M.execA_ok bv hR hex hp hA1 (disj_sub hcd (Nat.le_refl _) (by omega)) hrel)
    fun s₁ ⟨d₁, o₁, r₁⟩ => ?_
  have e₁ : M.ra s₁ = M.ra s := M.keep_ra d₁.keep
  refine M.runsTo_mono (M.law_ret (by rw [e₁]; exact hra) (Core.Done.at _ d₁ (M.codeAt_out hc2 ho2 hcd₂ o₁) ho2))
    fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
  have d := Core.Done.trans _ d₁ d₂
  rw [e₁] at d
  exact ⟨d.hpc, Rel.regs M r₁ m₂ fun j => st₂ _, o₁.trans (Out.of_eq m₂), d.ok, d.keep⟩

end Machine
end Proven.Mach
