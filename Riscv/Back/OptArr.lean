/- The optimising byte-array compiler on RISC-V (`compileOptA`, `compileOptA_ok`); separate from
`Riscv/Back/Opt.lean` because `Riscv.Back.Stmt` and `Riscv.Back.Arr` cannot be imported together. -/
import Riscv.Back.Wide
import Riscv.Back.Arr
import Compiler.Opt.Arr
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven
open Mach Mach.Riscv

def ofOptA : Option (List (BitVec 32)) → Except String (List (BitVec 32))
  | some ws => .ok ws
  | none => .error "compileOptA: out of temporaries, or a branch out of range, or a block variable assigned"

theorem ofOptA_ok {o : Option (List (BitVec 32))} {ws : List (BitVec 32)} (h : ofOptA o = .ok ws) : o = some ws := by
  cases o with
  | none => exact nomatch h
  | some w => cases h; rfl

/-- **The optimising byte-array compiler.** -/
def compileOptA (bv : List (Fin 8)) (p : AStmt) : Except String (List (BitVec 32)) :=
  ofOptA (rvw.optA bv p)

theorem bytesW (s : St) (a n : Nat) : bytes (rvw.mem s) a n = bytesAt s a n := Mach.Riscv.bytes_eq s a n

theorem relW_toR {bv R σ} {s : St} (h : Proven.Rel bv R σ s) : rvw.RelW bv (R.map toR) σ s :=
  ⟨fun i => by show getX s (phys (avar i)) = _; rw [phys_avar]; exact h.env i, by simpa using h.hlen,
    by simpa using h.bvlen, fun b hb => by simpa [toR] using h.base b (by simpa using hb),
    fun b hb => by simpa [toR] using h.blen b (by simpa using hb),
    fun b hb => by simpa [toR, bytesW] using h.bytes b (by simpa using hb)⟩

theorem relW_ofR {bv R σ} {s : St} (h : rvw.RelW bv (R.map toR) σ s) : Proven.Rel bv R σ s :=
  ⟨fun i => by have := h.env i; rwa [show rvw.get s (avar i) = getX s (A8 i) by
      show getX s (phys (avar i)) = _; rw [phys_avar]] at this, by simpa using h.hlen,
    by simpa using h.bvlen, fun b hb => by have := h.base b (by simpa using hb); rw [getR hb] at this; exact this,
    fun b hb => by have := h.blen b (by simpa using hb); rw [getR hb] at this; exact this,
    fun b hb => by have := h.bytes b (by simpa using hb); rw [getR hb, bytesW] at this; exact this⟩

/-- **`compileOptA` is correct** (the statement of `compileAF_ok` for the words it returns). -/
theorem compileOptA_ok (bv : List (Fin 8)) {p : AStmt} {ws : List (BitVec 32)} (hc : compileOptA bv p = .ok ws)
    {R : List Proven.Region} (hR : Proven.RegOK R) {σ σ' : AState} (hex : AExec p σ σ') {s : St} (h : Cfg s)
    {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hcode : codeAt s pc ws) (hok : codeOK pc ws.length)
    (hcd : ∀ r ∈ R, Proven.disjoint ⟨pc.toNat, 4 * ws.length⟩ r) (hrel : Proven.Rel bv R σ s)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      Proven.Rel bv R σ' s' ∧ unchangedOutside s s' R ∧ Cfg s' ∧ calleeSavedKept s s' := by
  have hcd' : ∀ r ∈ R.map toR, Mach.disjoint ⟨pc.toNat, 4 * ws.length⟩ r := fun r hr => by
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact hcd r' hr'
  have hR' : rvw.RegOK (R.map toR) := ⟨fun r hr => by
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact hR.1 r' hr', List.pairwise_map.2 (hR.2.imp id)⟩
  refine runsTo_mono (rvw.optA_ok bv (ofOptA_ok hc) hR' hex ⟨h, hpc, hcode, hok⟩ hcd' (relW_toR hrel) hra)
    fun s' ⟨p1, p2, p3, p4, p5⟩ => ⟨p1, relW_ofR p2, fun a ha => p3 a fun r hr => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact ha r' hr', p4, calleeSaved_of_AF h ⟨p4, fun a ha =>
        p3 a fun r hr => by obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact ha r' hr', fun j h1 h2 => p5 j fun r e => by
          rcases phys_img7 r with ⟨i, hi⟩ | ⟨i, hi⟩
          · exact h1 i.val i.2 (e.trans hi)
          · exact h2 i (e.trans hi)⟩⟩

/-- drop-in for `compileAF`: optimised words when the optimiser succeeds, the old words otherwise -/
def compileAFO (bv : List (Fin 8)) (p : AStmt) : List (BitVec 32) :=
  match compileOptA bv p with | .ok ws => ws | .error _ => compileAF bv p

/-- the statement of `compileAF_ok` for `compileAFO` -/
theorem compileAFO_ok (bv : List (Fin 8)) {p : AStmt} (hp : p.wf bv) {R : List Proven.Region} (hR : Proven.RegOK R)
    {σ σ' : AState} (hex : AExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileAFO bv p)) (hok : codeOK pc (compileAFO bv p).length)
    (hcd : ∀ r ∈ R, Proven.disjoint ⟨pc.toNat, 4 * (compileAFO bv p).length⟩ r) (hrel : Proven.Rel bv R σ s)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      Proven.Rel bv R σ' s' ∧ unchangedOutside s s' R ∧ Cfg s' ∧ calleeSavedKept s s' := by
  unfold compileAFO at hc hok hcd
  cases hx : compileOptA bv p with
  | ok ws => rw [hx] at hc hok hcd; exact compileOptA_ok bv hx hR hex h hpc hc hok hcd hrel hra
  | error _ => rw [hx] at hc hok hcd; exact compileAF_ok' bv hp hR hex h hpc hc hok hcd hrel hra

end Proven
