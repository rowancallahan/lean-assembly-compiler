/- `compileBF_ok` re-derived through the extended interface: the middle theorem `MachineF.compBF_ok`
instantiated with `rvF`; `Proven.BStmt` (`Riscv/Direct/Arr2Code.lean`) mapped into the model-free
`Mach.BStmt` (no word blocks); the abstract code encodes to exactly `compileBF`. -/
import Riscv.Back.Frame
import Compiler.BStmt

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

/-! ## The source language, mapped -/

def toMB : Proven.BExp → Mach.BExp
  | .var i => .var i
  | .const c => .const c
  | .bin op a b => .bin op (toMB a) (toMB b)
  | .ite c a b => .ite (toMB c) (toMB a) (toMB b)

def toMS : Proven.BStmt → Mach.BStmt
  | .assign v e => .assign v (toMB e)
  | .load v b i => .load v b (toMB i)
  | .store b i e => .store b (toMB i) (toMB e)
  | .seq p q => .seq (toMS p) (toMS q)
  | .loop c b => .loop (toMB c) (toMS b)

def toMSt (σ : Proven.BState) : Mach.BState := ⟨σ.env, σ.heap, []⟩

theorem denote_toMB (env : Nat → BitVec 64) : ∀ e : Proven.BExp, (toMB e).denote env = e.denote env
  | .var _ => rfl
  | .const _ => rfl
  | .bin op a b => by simp only [toMB, Mach.BExp.denote, Proven.BExp.denote, denote_toMB env a, denote_toMB env b]
  | .ite c a b => by
    simp only [toMB, Mach.BExp.denote, Proven.BExp.denote, denote_toMB env c, denote_toMB env a, denote_toMB env b]

theorem depth_toMB : ∀ e : Proven.BExp, (toMB e).depth = e.depth
  | .var _ => rfl
  | .const _ => rfl
  | .bin _ a b => by simp only [toMB, Mach.BExp.depth, Proven.BExp.depth, depth_toMB a, depth_toMB b]
  | .ite c a b => by simp only [toMB, Mach.BExp.depth, Proven.BExp.depth, depth_toMB c, depth_toMB a, depth_toMB b]

theorem vlt_toMB {m : Nat} : ∀ {e : Proven.BExp}, e.vlt m → (toMB e).vlt m
  | .var _, h => h
  | .const _, _ => trivial
  | .bin _ a b, h => ⟨vlt_toMB h.1, vlt_toMB h.2⟩
  | .ite c a b, h => ⟨vlt_toMB h.1, vlt_toMB h.2.1, vlt_toMB h.2.2⟩

theorem exec_toM {p : Proven.BStmt} {σ σ' : Proven.BState} (h : Proven.BExec p σ σ') :
    Mach.BExec (toMS p) (toMSt σ) (toMSt σ') := by
  induction h with
  | @assign v e σ =>
    have := Mach.BExec.assign (v := v) (e := toMB e) (σ := toMSt σ)
    rw [denote_toMB] at this; exact this
  | @load v b i σ hb hi =>
    have := Mach.BExec.load (v := v) (i := toMB i) (σ := toMSt σ) hb (by show _ < _; rw [denote_toMB]; exact hi)
    simp only [denote_toMB] at this; exact this
  | @store b i e σ hb hi =>
    have := Mach.BExec.store (e := toMB e) (i := toMB i) (σ := toMSt σ) hb (by show _ < _; rw [denote_toMB]; exact hi)
    simp only [denote_toMB] at this; exact this
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | loopF hc => exact .loopF (by show _ = _; rw [denote_toMB]; exact hc)
  | loopT hc _ _ ih1 ih2 => exact .loopT (by show _ ≠ _; rw [denote_toMB]; exact hc) ih1 ih2

/-! ## Same words -/

theorem code_genB : ∀ (e : Proven.BExp) (k : Nat), k + e.depth < 7 → rvF.codeF (mgenB (toMB e) k) = genB e k
  | .var i, k, hk => by
    simp only [Proven.BExp.depth] at hk
    by_cases hi : i < 8
    · simp only [toMB, mgenB, genB, dite_pos' hi, MachineF.codeF_one]
      show [encR 0 0 (phys (rk k)) 0 (phys (avar ⟨i, hi⟩))] = [iVar8 ⟨i, hi⟩ k]
      rw [phys_rk (by omega), phys_avar]; rfl
    · simp only [toMB, mgenB, genB, dite_neg' hi, MachineF.codeF_one]
      show [iLdS (i - 8) (rk k).val] = _
      rw [rk_val (by omega)]
  | .const c, k, hk => by
    simp only [toMB, mgenB, genB, MachineF.codeF_one]
    show genConst (rk k).val c.toNat = _
    rw [rk_val (by simp only [Proven.BExp.depth] at hk; omega)]
  | .bin op a b, k, hk => by
    simp only [Proven.BExp.depth] at hk
    simp only [toMB, mgenB, genB, MachineF.codeF_append, MachineF.codeF_one, code_genB a k (by omega),
      code_genB b (k + 1) (by omega)]
    show _ ++ opCode op (rk k).val = _
    rw [rk_val (by omega)]
  | .ite c a b, k, hk => by
    simp only [Proven.BExp.depth] at hk
    simp only [toMB, mgenB, genB, MachineF.codeF_append, MachineF.codeF_one, code_genB c k (by omega),
      code_genB a (k + 1) (by omega), code_genB b (k + 2) (by omega)]
    show _ ++ selCode (rk k).val = _
    rw [rk_val (by omega)]

theorem code_setV (v : Nat) : rvF.codeF (Mach.setV v) = [Proven.setV v] := by
  by_cases hv : v < 8
  · simp only [Mach.setV, Proven.setV, dite_pos' hv, MachineF.codeF_one]
    show [encR 0 0 (phys (avar ⟨v, hv⟩)) 0 (phys (rk 0))] = [iMv8 ⟨v, hv⟩]
    rw [phys_avar, show phys (rk 0) = 5 by decide]; rfl
  · simp only [Mach.setV, Proven.setV, dite_neg' hv, MachineF.codeF_one]; rfl

theorem code_compB (N : Nat) (bv : List Nat) : ∀ p : Proven.BStmt, p.wf N bv →
    rvF.codeF (rvF.compB bv [] (toMS p)) = compileB bv p ∧ rvF.wfB N bv [] (toMS p)
  | .assign v e, hp => by
    simp only [Proven.BStmt.wf] at hp
    refine ⟨?_, by rw [depth_toMB]; exact hp.1, vlt_toMB hp.2.1, hp.2.2.1, hp.2.2.2, List.not_mem_nil⟩
    simp only [toMS, MachineF.compB, compileB, MachineF.codeF_append, code_genB e 0 (by omega), code_setV]
  | .load v b i, hp => by
    simp only [Proven.BStmt.wf] at hp
    refine ⟨?_, by rw [depth_toMB]; exact hp.1, vlt_toMB hp.2.1, hp.2.2.1, hp.2.2.2.1, List.not_mem_nil, hp.2.2.2.2⟩
    simp only [toMS, MachineF.compB, compileB, MachineF.codeF_append, MachineF.codeF_one, code_setV]
    rw [show mgenB (Mach.addrB bv b (toMB i)) 0 = mgenB (toMB (Proven.addrB bv b i)) 0 from rfl,
      code_genB _ 0 (by simp only [Proven.addrB, Proven.BExp.depth]; omega), List.append_assoc]
    rfl
  | .store b i e, hp => by
    simp only [Proven.BStmt.wf] at hp
    refine ⟨?_, by rw [depth_toMB]; exact hp.1, by rw [depth_toMB]; exact hp.2.1, vlt_toMB hp.2.2.1,
      vlt_toMB hp.2.2.2.1, hp.2.2.2.2⟩
    simp only [toMS, MachineF.compB, compileB, MachineF.codeF_append, MachineF.codeF_one]
    rw [show mgenB (Mach.addrB bv b (toMB i)) 0 = mgenB (toMB (Proven.addrB bv b i)) 0 from rfl,
      code_genB _ 0 (by simp only [Proven.addrB, Proven.BExp.depth]; omega), code_genB e 1 (by omega)]
    rfl
  | .seq p q, hp => by
    obtain ⟨ea, wa⟩ := code_compB N bv p hp.1
    obtain ⟨eb, wb⟩ := code_compB N bv q hp.2
    exact ⟨by simp only [toMS, MachineF.compB, compileB, MachineF.codeF_append, ea, eb], wa, wb⟩
  | .loop c b, hp => by
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    obtain ⟨eb, wb⟩ := code_compB N bv b hp3
    have ec := code_genB c 0 (by omega)
    refine ⟨?_, by rw [depth_toMB]; exact hp1, vlt_toMB hp2, wb, ?_, ?_⟩
    · rw [toMS, MachineF.code_loopB, eb, ec]; rfl
    · show 2 * ((rvF.codeF (rvF.compB bv [] (toMS b))).length + 1 + 1) < 2048
      rw [eb]; omega
    · show 0 < (rvF.codeF (mgenB (toMB c) 0)).length + 1 + (rvF.codeF (rvF.compB bv [] (toMS b))).length ∧
        2 * ((rvF.codeF (mgenB (toMB c) 0)).length + 1 + (rvF.codeF (rvF.compB bv [] (toMS b))).length) ≤ 2 ^ 19
      rw [eb, ec]; omega

theorem code_compBF (N : Nat) (bv : List Nat) (p : Proven.BStmt) (hp : p.wf N bv) :
    rvF.codeF (rvF.compBF N bv [] (toMS p)) = compileBF N bv p := by
  rw [MachineF.compBF, MachineF.codeF_append, MachineF.codeF_append, (code_compB N bv p hp).1,
    MachineF.codeF_one, MachineF.codeF_two]; rfl

/-! ## The theorem -/

theorem keep_calleeSaved {s s' : St} (h : Cfg s) (h' : Cfg s') (k : rv.keep s s') : calleeSavedKept s s' :=
  calleeSaved_of_keepB h h' fun j h1 h2 _ => k j fun r e => by
    rcases phys_img7 r with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact h1 i.val i.2 (e.trans hi)
    · exact h2 i (e.trans hi)

theorem toR_mem {R : List Proven.Region} {r : Region} (h : r ∈ R.map toR) : ∃ r' ∈ R, r = toR r' := by
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 h; exact ⟨r', hr', rfl⟩

/-- **`compileBF_ok`, re-derived** through the extended interface (same statement as `Proven.compileBF_ok`). -/
theorem compileBF_ok' (N : Nat) (bv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N) {p : Proven.BStmt} (hp : p.wf N bv)
    {R : List Proven.Region} (hR : RegOK R) {σ σ' : Proven.BState} (hex : Proven.BExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileBF N bv p)) (hok : codeOK pc (compileBF N bv p).length)
    (hf : FrOK N (frameBase N (getX s 2))) (hfd : ∀ r ∈ R, Proven.disjoint ⟨frameBase N (getX s 2), 8 * (N + 1)⟩ r)
    (hcd : ∀ r ∈ (⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Proven.Region) :: R,
      Proven.disjoint ⟨pc.toNat, 4 * (compileBF N bv p).length⟩ r)
    (hreg : ∀ i : Fin 8, getX s (A8 i) = σ.env i.val) (hslot : ∀ j < N, σ.env (8 + j) = 0)
    (hheap : HeapRel bv R σ s) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 8, getX s' (A8 i) = σ'.env i.val) ∧
      HeapRel bv R σ' s' ∧ unchangedOutside s s' ((⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Proven.Region) :: R) ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 := by
  have ec := code_compBF N bv p hp
  rw [← ec] at hc hok hcd
  have hw := (code_compB N bv p hp).2
  have hL : rvF.Lay N (rvF.frameAt s N) (R.map toR) [] :=
    ⟨fun r hr => by obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact hR.1 r' hr', fun r hr => (nomatch hr),
      List.pairwise_map.2 (hR.2.imp id), List.Pairwise.nil, fun _ _ w hw => (nomatch hw),
      fun r hr => by obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact hfd r' hr', fun w hw => (nomatch hw),
      fun w hw => (nomatch hw)⟩
  have hcd' : ∀ r ∈ R.map toR ++ [] ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩],
      disjoint ⟨pc.toNat, 4 * (rvF.codeF (rvF.compBF N bv [] (toMS p))).length⟩ r := fun r hr => by
    rcases List.mem_append.1 hr with hr | hr
    · rw [List.append_nil] at hr
      obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact hcd r' (List.mem_cons_of_mem _ hr')
    · simp only [List.mem_singleton] at hr; subst hr; exact hcd _ (List.mem_cons_self ..)
  have hheap' : rvF.HeapB bv [] (R.map toR) [] (toMSt σ) s :=
    ⟨by simpa using hheap.hlen, by simpa using hheap.bvlen, fun b hb => by simpa [toR] using hheap.base b (by simpa using hb),
      fun b hb => by simpa [toR] using hheap.blen b (by simpa using hb),
      fun b hb => by
        have hb' : b < R.length := by simpa using hb
        rw [getR hb']; exact (bytes_eq s _ _).trans (hheap.bytes b hb'), rfl, rfl,
      fun b hb => (nomatch hb), fun b hb => (nomatch hb), fun b hb => (nomatch hb)⟩
  refine runsTo_mono (rvF.compBF_ok N bv [] hbv (fun x hx => (nomatch hx)) hw (exec_toM hex) ⟨h, hpc, hc, hok⟩
    hf hL hcd' (fun i => by show getX s (phys (avar i)) = _; rw [phys_avar]; exact hreg i) hslot hheap' hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  refine ⟨p1, fun i => by have := p2 i; rwa [show rvF.get s' (avar i) = getX s' (A8 i) by
      show getX s' (phys (avar i)) = _; rw [phys_avar]] at this, ⟨by simpa using p3.hlen, by simpa using p3.bvlen,
      fun b hb => by have := p3.base b (by simpa using hb); rw [getR hb] at this; exact this,
      fun b hb => by have := p3.blen b (by simpa using hb); rw [getR hb] at this; exact this,
      fun b hb => by
        have := p3.rbytes b (by simpa using hb); rw [getR hb] at this; exact (bytes_eq s' _ _).symm.trans this⟩,
    fun a ha => p4 a fun r hr => ?_, p5, keep_calleeSaved h p5 p6, p6 3 phys_ne3⟩
  rcases List.mem_append.1 hr with hr | hr
  · rw [List.append_nil] at hr
    obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact ha r' (List.mem_cons_of_mem _ hr')
  · simp only [List.mem_singleton] at hr; subst hr; exact ha _ (List.mem_cons_self ..)

example : type_of% @compileBF_ok' = type_of% @Proven.compileBF_ok := rfl

end Proven.Mach.Riscv
