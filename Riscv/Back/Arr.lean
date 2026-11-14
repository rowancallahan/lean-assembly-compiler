/- `compileAF_ok`, `sortCode_ok`, `sortCode_implements` re-derived through the interface: the middle
theorem `Machine.compAF_ok` instantiated with `rv`; regions/relations converted to the model-free
`Mach.Region` / `Machine.Rel`; the abstract code encodes to exactly `compileAF`. -/
import Riscv.Back.Exp
import Compiler.Arr
import Riscv.Direct.SortMachine

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

theorem code_compA (bv : List (Fin 8)) : ∀ p : AStmt, p.wf bv →
    rv.code (rv.compA bv p) = compileA bv p ∧ rv.wfA bv p
  | .assign v e, hp => by
    refine ⟨?_, hp⟩
    simp only [AStmt.wf] at hp
    simp only [Machine.compA, compileA, Machine.code_append, Machine.code_one, code_gen8 e 0 (by omega)]
    show _ ++ [encR 0 0 (phys (avar v)) 0 (phys (rk 0))] = _
    rw [phys_avar, show phys (rk 0) = 5 by decide]; rfl
  | .load v b i, hp => by
    refine ⟨?_, hp⟩
    simp only [AStmt.wf] at hp
    simp only [Machine.compA, compileA, Machine.code_append, Machine.code_two,
      code_gen8 (addrE bv b i) 0 (by simp only [addrE, AExp.depth]; omega)]
    show _ ++ ([iLbuT] ++ [encR 0 0 (phys (avar v)) 0 (phys (rk 0))]) = _
    rw [phys_avar, show phys (rk 0) = 5 by decide]; rfl
  | .store b i e, hp => by
    refine ⟨?_, hp⟩
    simp only [AStmt.wf] at hp
    simp only [Machine.compA, compileA, Machine.code_append, Machine.code_one,
      code_gen8 (addrE bv b i) 0 (by simp only [addrE, AExp.depth]; omega), code_gen8 e 1 (by omega)]
    rfl
  | .seq p q, hp => by
    obtain ⟨ea, wa⟩ := code_compA bv p hp.1
    obtain ⟨eb, wb⟩ := code_compA bv q hp.2
    exact ⟨by simp only [Machine.compA, compileA, Machine.code_append, ea, eb], wa, wb⟩
  | .loop c b, hp => by
    obtain ⟨hp1, hp2, hp3⟩ := hp
    obtain ⟨eb, wb⟩ := code_compA bv b hp2
    have ec := code_gen8 c 0 (by omega)
    refine ⟨?_, hp1, wb, ?_, ?_⟩
    · rw [Machine.code_loopA, eb, ec]; rfl
    · show 2 * ((rv.code (rv.compA bv b)).length + 1 + 1) < 2048
      rw [eb]; omega
    · show 0 < (rv.code (mgen8 c 0)).length + 1 + (rv.code (rv.compA bv b)).length ∧
        2 * ((rv.code (mgen8 c 0)).length + 1 + (rv.code (rv.compA bv b)).length) ≤ 2 ^ 19
      rw [eb, ec]; omega

theorem code_compAF (bv : List (Fin 8)) (p : AStmt) (hp : p.wf bv) : rv.code (rv.compAF bv p) = compileAF bv p := by
  rw [Machine.compAF, Machine.code_append, (code_compA bv p hp).1]; rfl

def toR (r : Proven.Region) : Region := ⟨r.base, r.len⟩

theorem bytes_eq (s : St) : ∀ a n, bytes (rv.mem s) a n = bytesAt s a n
  | _, 0 => rfl
  | a, n + 1 => by
    show s.mem[a]? :: bytes (rv.mem s) (a + 1) n = _
    rw [bytes_eq s (a + 1) n]
    simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    congr 1; apply List.map_congr_left; intro j _; simp only [Function.comp]; rw [Nat.add_assoc, Nat.add_comm 1 j]

theorem regOK_toR {R : List Proven.Region} (h : Proven.RegOK R) : rv.RegOK (R.map toR) :=
  ⟨fun r hr => by
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact h.1 r' hr', List.pairwise_map.2 (h.2.imp id), fun r hr a h1 h2 _ _ => by
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    have := h.1 r' hr'; unfold Region.inRAM at this
    exact ⟨Nat.le_trans this.1 h1, Nat.le_trans h2 this.2⟩⟩

theorem rel_toR {bv R σ} {s : St} (h : Proven.Rel bv R σ s) : rv.Rel bv (R.map toR) σ s :=
  ⟨fun i => by show getX s (phys (avar i)) = _; rw [phys_avar]; exact h.env i, by simpa using h.hlen,
    by simpa using h.bvlen, fun b hb => by simpa [toR] using h.base b (by simpa using hb),
    fun b hb => by simpa [toR] using h.blen b (by simpa using hb),
    fun b hb => by simpa [toR, bytes_eq] using h.bytes b (by simpa using hb)⟩

theorem getR {R : List Proven.Region} {b : Nat} (hb : b < R.length) :
    (R.map toR)[b]'(by rw [List.length_map]; exact hb) = toR R[b] := List.getElem_map ..

theorem rel_ofR {bv R σ} {s : St} (h : rv.Rel bv (R.map toR) σ s) : Proven.Rel bv R σ s :=
  ⟨fun i => by have := h.env i; rwa [show rv.get s (avar i) = getX s (A8 i) by
      show getX s (phys (avar i)) = _; rw [phys_avar]] at this, by simpa using h.hlen,
    by simpa using h.bvlen, fun b hb => by have := h.base b (by simpa using hb); rw [getR hb] at this; exact this,
    fun b hb => by have := h.blen b (by simpa using hb); rw [getR hb] at this; exact this,
    fun b hb => by have := h.bytes b (by simpa using hb); rw [getR hb, bytes_eq] at this; exact this⟩

theorem phys_img7 : ∀ r : Reg, (∃ i : Fin 7, phys r = T i.val) ∨ ∃ i : Fin 8, phys r = A8 i := by decide

/-- **`compileAF_ok`, re-derived** through the interface (same statement as `Proven.compileAF_ok`). -/
theorem compileAF_ok' (bv : List (Fin 8)) {p : AStmt} (hp : p.wf bv) {R : List Proven.Region} (hR : Proven.RegOK R)
    {σ σ' : AState} (hex : AExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileAF bv p)) (hok : codeOK pc (compileAF bv p).length)
    (hcd : ∀ r ∈ R, Proven.disjoint ⟨pc.toNat, 4 * (compileAF bv p).length⟩ r) (hrel : Proven.Rel bv R σ s)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      Proven.Rel bv R σ' s' ∧ unchangedOutside s s' R ∧ Cfg s' ∧ calleeSavedKept s s' := by
  have ec := code_compAF bv p hp
  rw [← ec] at hc hok hcd
  have hcd' : ∀ r ∈ R.map toR, disjoint ⟨pc.toNat, 4 * (rv.code (rv.compAF bv p)).length⟩ r := fun r hr => by
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact hcd r' hr'
  refine runsTo_mono (rv.compAF_ok bv (code_compA bv p hp).2 (regOK_toR hR) hex ⟨h, hpc, hc, hok⟩ hcd'
    (rel_toR hrel) hra) fun s' ⟨p1, p2, p3, p4, p5⟩ => ⟨p1, rel_ofR p2, fun a ha => p3 a fun r hr => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact ha r' hr', p4, calleeSaved_of_AF h ⟨p4, fun a ha =>
        p3 a fun r hr => by obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact ha r' hr', fun j h1 h2 => p5 j fun r e => by
          rcases phys_img7 r with ⟨i, hi⟩ | ⟨i, hi⟩
          · exact h1 i.val i.2 (e.trans hi)
          · exact h2 i (e.trans hi)⟩⟩

end Proven.Mach.Riscv

/-! ## The sort, re-derived: the proofs of `sortCode_ok` / `sortCode_implements` (`Proven/SortMachine.lean`)
with `compileAF_ok` replaced by `Mach.Riscv.compileAF_ok'`. -/
namespace Proven

/-- **Insertion sort** (memory/region form): input `xs` at `a0` (length in `a1`), an output block of
`|xs|` bytes at `a3` (any contents): returns to `ra` with the output block holding
`xs.mergeSort` (computed by insertion sort), the input unchanged, all memory outside the output block
unchanged, callee-saved registers and `Cfg` kept. -/
theorem sortCode_ok_m {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc sortCode) (hok : codeOK pc sortCode.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs out : List (BitVec 8)} {inb outb : Nat} (hR : RegOK [⟨inb, xs.length⟩, ⟨outb, xs.length⟩])
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, xs.length⟩], disjoint ⟨pc.toNat, 4 * sortCode.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (ho : bytesAt s outb xs.length = out.map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb xs.length = (xs.mergeSort leB).map some ∧
      bytesAt s' inb xs.length = xs.map some ∧ unchangedOutside s s' [⟨outb, xs.length⟩] ∧
      Cfg s' ∧ calleeSavedKept s s' := by
  have hn : xs.length < 2 ^ 63 := by
    have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega
  have hout : out.length = xs.length := by simpa [bytesAt] using (congrArg List.length ho).symm
  obtain ⟨σ', hex, hh⟩ := sortProg_mergeSort xs out ⟨fun i => getX s (A8 i), [xs, out]⟩ rfl h1 hn hout
  have hrel : Rel [0, 3] [⟨inb, xs.length⟩, ⟨outb, xs.length⟩] ⟨fun i => getX s (A8 i), [xs, out]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl, fun b hb => by obtain _ | _ | b := b; exact h0; exact h3; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; rfl; exact hout; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; exact hx; exact ho; simp at hb; omega⟩
  refine runsTo_mono (Mach.Riscv.compileAF_ok' [0, 3] sortProg_wf hR hex h hpc hc hok hcd hrel hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5⟩
  have e0 := p2.bytes 0 (by simp); have e1 := p2.bytes 1 (by simp)
  simp only [hh] at e0 e1
  exact ⟨p1, by simpa using e1, by simpa using e0, unchanged_drop p3 (by simpa [hx] using e0), p4, p5⟩

/-- **Insertion sort implements `List.mergeSort`** in the sense of `ImplementsMapped`. -/
theorem sortCode_implements_m : ImplementsMapped sortCode (fun x => x.mergeSort leU) := by
  intro x s entry ra input scratch output stack codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hsl hol hstk hram hdis hmap
  simp only [List.length_mergeSort] at hol hmap ⊢
  have hin : ∀ r ∈ [input, scratch, output, stack, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14, d15⟩, ⟨d23, d24, d25⟩, ⟨d34, d35⟩, d45⟩ := hdis
  obtain ⟨ri, rs, ro, rst, rc⟩ := hin
  unfold Region.inRAM at ri ro rc
  unfold disjoint at d13 d15 d35
  simp only [codeR] at d15 d35
  have hxl : (x.map (·.toBitVec)).length = x.length := by simp
  have hol' : x.length ≤ output.len := hol
  have hil' : input.len = x.length := hil
  have hR : RegOK [⟨input.base, (x.map (·.toBitVec)).length⟩, ⟨output.base, (x.map (·.toBitVec)).length⟩] := by
    rw [hxl]
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Region.inRAM; dsimp only; (try simp only [List.length_map]); omega)
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold disjoint; dsimp only; (try simp only [List.length_map]); omega
  have hok : codeOK entry sortCode.length := ⟨hal, rc.1, rc.2⟩
  have hcd : ∀ r ∈ [(⟨input.base, (x.map (·.toBitVec)).length⟩ : Region), ⟨output.base, (x.map (·.toBitVec)).length⟩],
      disjoint ⟨entry.toNat, 4 * sortCode.length⟩ r := by
    rw [hxl]; intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold disjoint; dsimp only; (try simp only [List.length_map]); omega)
  -- the output's initial bytes
  have ho : bytesAt s output.base (x.map (·.toBitVec)).length =
      ((bytesAt s output.base (x.map (·.toBitVec)).length).map (·.getD 0)).map some := by
    rw [List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [bytesAt, List.getElem_map, List.getElem_range, Function.comp]
    have := hmap i (by simpa [bytesAt, hxl] using h1)
    cases e : s.mem[output.base + i]? with
    | none => rw [e] at this; simp at this
    | some b => rfl
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (sortCode_ok_m h hpc (codeAt_of_codeBytes hok hcode) hok
    (by rw [hra']; omega) hR hcd (getX_of (h.x10.symm.trans h10) rfl) (by rw [getX_of (h.x11.symm.trans h11) rfl, hxl])
    (getX_of (h.x13.symm.trans h13) rfl) (by simpa [List.map_map, Function.comp_def] using hx) ho) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  refine ⟨by rw [p1, hra'], ?_, ?_, p6, p5⟩
  · rw [← hxl, p2, ← mergeSort_toBitVec]; simp [List.map_map]
  · intro a ha
    apply p4 a
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    have := ha output (by simp)
    dsimp only; omega

end Proven

/-! Same statements as the originals (checked by the elaborator): -/
example : type_of% @Proven.Mach.Riscv.compileAF_ok' = type_of% @Proven.compileAF_ok := rfl
example : type_of% @Proven.sortCode_ok_m = type_of% @Proven.sortCode_ok := rfl
example : type_of% @Proven.sortCode_implements_m = type_of% @Proven.sortCode_implements := rfl
