/- The optimising back end in `Implements1` form.

* `compileAFO_okK`, `compileBFO_okK`: `compileAFO_ok` / `compileBFO_ok` with the full register frame
  `rv.keep` in the conclusion (as `compileAF_okK` / `compileBF_okK` of `Riscv/Back/Keep.lean`,
  `Riscv/Back/SortMerge.lean`), from `Wide.optA_ok` / `WideF.optB_ok`.
* `implements1_of_execO`: `implements1_of_exec` (same hypotheses) for the drop-in `compBFO N [0, 3] [2]`
  (`Riscv/Back/OptB.lean`; byte and word blocks). -/
import Riscv.Back.Implements1
import Riscv.Back.SortMerge
import Riscv.Back.OptB
import Riscv.Back.OptArr

set_option linter.unusedVariables false

namespace Proven
open Mach Mach.Riscv

/-- `compileAFO_ok` with the full frame `rv.keep` in the conclusion -/
theorem compileAFO_okK (bv : List (Fin 8)) {p : AStmt} (hp : p.wf bv) {R : List Proven.Region} (hR : Proven.RegOK R)
    {σ σ' : AState} (hex : AExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileAFO bv p)) (hok : codeOK pc (compileAFO bv p).length)
    (hcd : ∀ r ∈ R, Proven.disjoint ⟨pc.toNat, 4 * (compileAFO bv p).length⟩ r) (hrel : Proven.Rel bv R σ s)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      Proven.Rel bv R σ' s' ∧ unchangedOutside s s' R ∧ Cfg s' ∧ Mach.Riscv.rv.keep s s' := by
  unfold compileAFO at hc hok hcd
  cases hx : compileOptA bv p with
  | ok ws =>
    rw [hx] at hc hok hcd
    have hcd' : ∀ r ∈ R.map toR, Mach.disjoint ⟨pc.toNat, 4 * ws.length⟩ r := fun r hr => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact hcd r' hr'
    refine runsTo_mono (rvw.optA_ok bv (ofOptA_ok hx) (Mach.Riscv.regOK_toR hR) hex ⟨h, hpc, hc, hok⟩ hcd'
      (relW_toR hrel) hra) fun s' ⟨p1, p2, p3, p4, p5⟩ => ⟨p1, relW_ofR p2, fun a ha => p3 a fun r hr => by
        obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact ha r' hr', p4, p5⟩
  | error _ => rw [hx] at hc hok hcd; exact Mach.Riscv.compileAF_okK bv hp hR hex h hpc hc hok hcd hrel hra

/-- `compileBFO_ok` with the full frame `rv.keep` in the conclusion -/
theorem compileBFO_okK (N : Nat) (bv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N) {p : Proven.BStmt} (hp : p.wf N bv)
    {R : List Proven.Region} (hR : RegOK R) {σ σ' : Proven.BState} (hex : Proven.BExec p σ σ') {s : St} (h : Cfg s)
    {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileBFO N bv p))
    (hok : codeOK pc (compileBFO N bv p).length)
    (hf : FrOK N (frameBase N (getX s 2))) (hfd : ∀ r ∈ R, Proven.disjoint ⟨frameBase N (getX s 2), 8 * (N + 1)⟩ r)
    (hcd : ∀ r ∈ (⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Proven.Region) :: R,
      Proven.disjoint ⟨pc.toNat, 4 * (compileBFO N bv p).length⟩ r)
    (hreg : ∀ i : Fin 8, getX s (A8 i) = σ.env i.val) (hslot : ∀ j < N, σ.env (8 + j) = 0)
    (hheap : HeapRel bv R σ s) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 8, getX s' (A8 i) = σ'.env i.val) ∧
      HeapRel bv R σ' s' ∧ unchangedOutside s s' ((⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Proven.Region) :: R) ∧
      Cfg s' ∧ Mach.Riscv.rv.keep s s' := by
  unfold compileBFO at hc hok hcd
  cases hx : compileOptB N bv p with
  | error _ => rw [hx] at hc hok hcd; exact Mach.Riscv.compileBF_okK N bv hbv hp hR hex h hpc hc hok hf hfd hcd hreg hslot hheap hra
  | ok ws =>
  rw [hx] at hc hok hcd
  have hopt : ∃ g sp, rvwF.optB scB g sp N bv [] (toMS p) = some ws := by
    unfold compileOptB at hx
    cases hfb : pickB N bv [] (toMS p) with
    | none => rw [hfb] at hx; exact nomatch hx
    | some w => rw [hfb] at hx; cases hx; exact pickB_ok hfb
  obtain ⟨g, sp, hT⟩ := hopt
  have hcd' : ∀ r ∈ R.map toR ++ [] ++ [⟨rvwF.frameAt s N, 8 * (N + 1)⟩],
      Mach.disjoint ⟨pc.toNat, 4 * ws.length⟩ r := fun r hr => by
    rcases List.mem_append.1 hr with hr | hr
    · rw [List.append_nil] at hr
      obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact hcd r' (List.mem_cons_of_mem _ hr')
    · simp only [List.mem_singleton] at hr; subst hr; exact hcd _ (List.mem_cons_self ..)
  have hheap' : HeapI rvwF.toWide bv [] (R.map toR) [] (toMSt σ) s :=
    ⟨by simp; exact hheap.hlen, by simpa using hheap.bvlen, fun b hb => by simp [toR]; exact hheap.base b (by simpa using hb),
      fun b hb => by simp [toR]; exact hheap.blen b (by simpa using hb),
      fun b hb => by
        have hb' : b < R.length := by simpa using hb
        rw [getR hb']; exact (Mach.Riscv.bytes_eq s _ _).trans (hheap.bytes b hb'), rfl, rfl,
      fun b hb => (nomatch hb), fun b hb => (nomatch hb), fun b hb => (nomatch hb)⟩
  refine runsTo_mono (rvwF.optB_ok hT (exec_toM hex) ⟨h, hpc, hc, hok⟩ hf
    (fun r hr => by rw [List.append_nil] at hr; obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact hR.1 r' hr')
    (fun r hr => by rw [List.append_nil] at hr; exact (Mach.Riscv.regOK_toR hR).2.2 r hr)
    (List.pairwise_map.2 (hR.2.imp id)) List.Pairwise.nil (fun _ _ _ hw => (nomatch hw)) (fun _ hw => (nomatch hw))
    (fun r hr => by rw [List.append_nil] at hr; obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact hfd r' hr') hcd'
    (fun i => by show getX s (phys (avar i)) = _; rw [phys_avar]; exact hreg i) hslot hheap' hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  refine ⟨p1, fun i => by have := p2 i; rwa [show rvwF.get s' (avar i) = getX s' (A8 i) by
      show getX s' (phys (avar i)) = _; rw [phys_avar]] at this, ⟨by have h := p3.hlen; simp at h; exact h, by simpa using p3.bvlen,
      fun b hb => by have := p3.base b (by simpa using hb); rw [getR hb] at this; exact this,
      fun b hb => by have := p3.blen b (by simpa using hb); rw [getR hb] at this; exact this,
      fun b hb => by
        have := p3.rbytes b (by simpa using hb); rw [getR hb] at this; exact (Mach.Riscv.bytes_eq s' _ _).symm.trans this⟩,
    fun a ha => p4 a fun r hr => ?_, p5, p6⟩
  rcases List.mem_append.1 hr with hr | hr
  · rw [List.append_nil] at hr
    obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact ha r' (List.mem_cons_of_mem _ hr')
  · simp only [List.mem_singleton] at hr; subst hr; exact ha _ (List.mem_cons_self ..)

end Proven

namespace Proven.Mach.Riscv

/-- what `compBFO_ok'` says of the words `code` for `prog` (`Implements1` layout: blocks `[0, 3]`, words `[2]`) -/
def BSpec (N : Nat) (prog : Mach.BStmt) (code : List (BitVec 32)) : Prop :=
  ∀ {R W : List Region} {σ σ' : Mach.BState} {s : St} {pc : BitVec 64}, Mach.BExec prog σ σ' →
    rvF.At s pc code → rvF.enterOK s N → rvF.Lay N (rvF.frameAt s N) R W →
    (∀ r ∈ R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩], Mach.disjoint ⟨pc.toNat, 4 * code.length⟩ r) →
    (∀ i : Fin 8, rvF.get s (avar i) = σ.env i.val) → (∀ j, j < N → σ.env (8 + j) = 0) →
    rvF.HeapB [0, 3] [2] R W σ s → rvF.retOK (rvF.ra s) →
    rvF.runsTo s fun s' => rvF.pcIs s' (rvF.ra s) ∧ (∀ i : Fin 8, rvF.get s' (avar i) = σ'.env i.val) ∧
      rvF.HeapB [0, 3] [2] R W σ' s' ∧ Out (R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩]) (rvF.mem s) (rvF.mem s') ∧
      rvF.ok s' ∧ rvF.keep s s'

/-- `Implements1With` from a source-level run, for any words `code` with `BSpec` (up to `NS` slots) -/
theorem implements1_of_spec {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ NS) (prog : Mach.BStmt) (code : List (BitVec 32)) (hspec : BSpec N prog code) (wn : Nat → Nat)
    (space : Nat → Nat) (hsp : ∀ n, 8 * wn n + 8 * (N + 1) + 7 ≤ space n) (maxLen : Nat) (retLen : Bool)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv),
      env 1 = BitVec.ofNat 64 (encA a).length → (∀ j, 8 ≤ j → env j = 0) → (encA a).length ≤ maxLen →
      (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length → out.length < 2 ^ 32 →
      tbl.length = wn (encA a).length →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) :
    Implements1With encA encB code f space maxLen retLen := by
  intro a s entry ra input output work x y codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hws hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rw' rc
  unfold Proven.disjoint at d12 d13 d14 d23 d24 d34
  simp only [codeR] at d14 d24 d34 rc
  have hil' : input.len = x.length := hil
  have hol' : y.length ≤ output.len := hol
  have hws' := hsp x.length
  have hws'' : space x.length ≤ work.len := hws
  have hxl : (x.map (·.toBitVec)).length = x.length := by simp
  -- the frame
  have hsp2 : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp2]; exact toNat_ofNat' (by omega)
  have hfb : frameBase N (getX s 2) = (work.base + work.len) / 8 * 8 - 8 * (N + 1) := by
    unfold frameBase; rw [hspn]
  have hfb1 : work.base + 8 * wn x.length ≤ frameBase N (getX s 2) := by rw [hfb]; omega
  have hfb2 : frameBase N (getX s 2) + 8 * (N + 1) ≤ work.base + work.len := by rw [hfb]; omega
  have hf : FrOK N (frameBase N (getX s 2)) :=
    ⟨by rw [hfb]; omega, by omega, by omega, hN⟩
  -- the initial heap
  obtain ⟨out0, hout0l, ho⟩ : ∃ out0 : List (BitVec 8), out0.length = output.len ∧
      bytesAt s output.base output.len = out0.map some :=
    ⟨_, by simp [bytesAt], bytesAt_hosted fun i hi => hmapO i hi⟩
  obtain ⟨tbl0, htl, htb⟩ : ∃ tbl0 : List (BitVec 64), tbl0.length = wn x.length ∧
      bytesAt s work.base (8 * wn x.length) = (wbytes tbl0).map some := by
    obtain ⟨ws, hl, hw⟩ := exists_wbytes (wn x.length) ((bytesAt s work.base (8 * wn x.length)).map (·.getD 0))
      (by simp [bytesAt])
    exact ⟨ws, hl, by rw [hw]; exact bytesAt_hosted fun i hi => hmapW i (by omega)⟩
  obtain ⟨σ', out', hexec, hh, htk, hdr, hrl⟩ := hex a out0 tbl0 (envOf s)
    (by simp [envOf]; exact getX_of (h.x11.symm.trans h11) rfl) (fun j hj => by simp [envOf]; omega)
    hmax (by show x.length < 2 ^ 32; omega) (by show y.length ≤ out0.length; omega) (by omega) htl
  -- the layout
  let R : List Region := [⟨input.base, x.length⟩, ⟨output.base, output.len⟩]
  let W : List Region := [⟨work.base, 8 * wn x.length⟩]
  have hL : rvF.Lay N (rvF.frameAt s N) R W := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, List.pairwise_singleton _ _, fun r hr w hw => ?_, fun r hr => ?_,
      fun w hw => ?_, fun w hw => ?_, fun r hr q h1 h2 _ _ => ?_, fun w hw q h1 h2 _ _ => ?_⟩
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (show _ ∧ _; dsimp only; show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; omega)
    · simp only [W, List.mem_singleton] at hr; subst hr
      show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; dsimp only; omega
    · simp only [R, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold Mach.disjoint; dsimp only; omega
    · simp only [W, List.mem_singleton] at hw; subst hw
      simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      show Mach.disjoint ⟨frameBase N (getX s 2), _⟩ r
      rcases hr with rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [W, List.mem_singleton] at hw; subst hw
      show Mach.disjoint ⟨frameBase N (getX s 2), _⟩ _
      unfold Mach.disjoint; dsimp only; omega
    · simp only [W, List.mem_singleton] at hw; subst hw; exact hwal
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      show 0x80000000 ≤ q ∧ q + 1 ≤ 0x100000000
      rcases hr with rfl | rfl <;> (dsimp only at h1 h2; omega)
    · simp only [W, List.mem_singleton] at hw; subst hw
      show 0x80000000 ≤ q ∧ q + 1 ≤ 0x100000000; dsimp only at h1 h2; omega
  have hok : codeOK entry code.length := ⟨hal, rc.1, rc.2⟩
  have hcd : ∀ r ∈ R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩],
      Mach.disjoint ⟨entry.toNat, 4 * code.length⟩ r := by
    intro r hr
    simp only [R, W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [show rvF.frameAt s N = frameBase N (getX s 2) from rfl] at hr
    show Mach.disjoint _ r
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold Mach.disjoint; dsimp only)
    · omega
    · omega
    · omega
    · show _ ∨ frameBase N (getX s 2) + _ ≤ _; omega
  have hheap : rvF.HeapB [0, 3] [2] R W ⟨envOf s, [x.map (·.toBitVec), out0], [tbl0]⟩ s := by
    refine ⟨rfl, rfl, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, rfl, rfl, fun b hb => ?_, fun b hb => ?_,
      fun b hb => ?_⟩
    · obtain _ | _ | b := b
      · simp [envOf]; exact getX_of (h.x10.symm.trans h10) rfl
      · simp [envOf]; exact getX_of (h.x13.symm.trans h13) rfl
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | _ | b := b
      · simp [R]
      · simpa [R] using hout0l
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | _ | b := b
      · show bytes (rvF.mem s) input.base x.length = _
        exact (bytes_eq s _ _).trans (by simpa [List.map_map, Function.comp_def] using hx)
      · show bytes (rvF.mem s) output.base output.len = _
        exact (bytes_eq s _ _).trans (by simpa using ho)
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | b := b
      · simp [envOf]; exact getX_of (h.x12.symm.trans h12) rfl
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
    · obtain _ | b := b
      · show 8 * tbl0.length = 8 * wn x.length; rw [htl]
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
    · obtain _ | b := b
      · show bytes (rvF.mem s) work.base (8 * wn x.length) = _
        exact (bytes_eq s _ _).trans htb
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (hspec hexec ⟨h, hpc, codeAt_of_codeBytes hok hcode, hok⟩ hf hL hcd
    (fun i => by show getX s (phys (avar i)) = _; rw [phys_avar]; simp [envOf])
    (fun j hj => by simp only [envOf]; rw [dite_neg' (by omega)]) hheap (by show (getX s 1).toNat % 2 = 0; rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  have e0 := p3.rbytes 0 (by simp [R]); have e1 := p3.rbytes 1 (by simp [R])
  simp only [hh] at e0 e1
  have e0' : bytesAt s' input.base x.length = (x.map (·.toBitVec)).map some := by
    have := (bytes_eq s' _ _).symm.trans e0; simp at this ⊢; exact this
  have e1' : bytesAt s' output.base output.len = out'.map some := by
    have := (bytes_eq s' _ _).symm.trans e1; simp at this ⊢; exact this
  refine ⟨by rw [← hra']; exact p1, ?_, ?_, abi_of_keep h p5 p6, p5, fun hr => ?_⟩
  · rw [← bytesAt_take' s' output.base hol', e1', ← List.map_take, htk]; simp [List.map_map, y]
  · intro q hq
    have a2 := hq ⟨output.base, y.length⟩ (by simp); have a3 := hq work (by simp)
    dsimp only at a2
    by_cases hqi : input.base ≤ q ∧ q < input.base + input.len
    · have e0x : bytesAt s' input.base x.length = bytesAt s input.base x.length := by
        rw [e0', hx, List.map_map]; rfl
      have := congrArg (·[q - input.base]?) e0x
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - input.base < x.length by omega),
        Option.map_some, Option.some.injEq] at this
      rwa [Nat.add_sub_cancel' hqi.1] at this
    by_cases hqo : output.base ≤ q ∧ q < output.base + output.len
    · have e1x : (bytesAt s' output.base output.len)[q - output.base]? =
          (bytesAt s output.base output.len)[q - output.base]? := by
        rw [e1', ho, List.getElem?_map, List.getElem?_map]
        have := congrArg (·[q - output.base - y.length]?) hdr
        simp only [List.getElem?_drop] at this
        rw [show y.length + (q - output.base - y.length) = q - output.base by omega] at this
        rw [this]
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - output.base < output.len by omega),
        Option.map_some, Option.some.injEq] at e1x
      rwa [Nat.add_sub_cancel' hqo.1] at e1x
    · apply p4 q
      intro r hr
      simp only [R, W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only
      · omega
      · omega
      · omega
      · show q < frameBase N (getX s 2) ∨ frameBase N (getX s 2) + _ ≤ q; omega
  · have := p2 ⟨1, by decide⟩
    rw [show rvF.get s' (avar ⟨1, by decide⟩) = getX s' 11 from rfl, hrl hr] at this
    rw [p5.x11, this]

/-- `implements1_of_execO` for up to `NS` slots -/
theorem implements1_of_execOW {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ NS) (prog : Mach.BStmt) (hwf : rvF.wfB N [0, 3] [2] prog) (wn : Nat → Nat)
    (space : Nat → Nat) (hsp : ∀ n, 8 * wn n + 8 * (N + 1) + 7 ≤ space n) (maxLen : Nat) (retLen : Bool)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv),
      env 1 = BitVec.ofNat 64 (encA a).length → (∀ j, 8 ≤ j → env j = 0) → (encA a).length ≤ maxLen →
      (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length → out.length < 2 ^ 32 →
      tbl.length = wn (encA a).length →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) :
    Implements1With encA encB (compBFO N [0, 3] [2] prog) f space maxLen retLen :=
  implements1_of_spec encA encB f N hN prog _
    (fun hexec hA hen hL hcd hreg hslot hheap hra => compBFO_ok' N [0, 3] [2] (by intro x hx; simp at hx; omega)
      (by intro x hx; simp at hx; omega) hwf hexec hA hen hL hcd hreg hslot hheap hra) wn space hsp maxLen retLen hex

/-- **`implements1_of_execOW` for the checked words `compBFC`**: no `wfB`; `optB` accepts the choice instead -/
theorem implements1_of_execC {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ NS) (prog : Mach.BStmt) (t : List (Nat × Reg)) (spl : List Nat)
    (hc : (rvwF.optB scB (tblG t) (fun j => spl.contains j) N [0, 3] [2] prog).isSome = true) (wn : Nat → Nat)
    (space : Nat → Nat) (hsp : ∀ n, 8 * wn n + 8 * (N + 1) + 7 ≤ space n) (maxLen : Nat) (retLen : Bool)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv),
      env 1 = BitVec.ofNat 64 (encA a).length → (∀ j, 8 ≤ j → env j = 0) → (encA a).length ≤ maxLen →
      (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length → out.length < 2 ^ 32 →
      tbl.length = wn (encA a).length →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) :
    Implements1With encA encB (compBFC N [0, 3] [2] t spl prog) f space maxLen retLen :=
  implements1_of_spec encA encB f N hN prog _
    (fun hexec hA hen hL hcd hreg hslot hheap hra => compBFC_ok' N [0, 3] [2] hc hexec hA hen hL hcd hreg hslot
      hheap hra) wn space hsp maxLen retLen hex

/-- `implements1_of_exec` (same hypotheses) for the optimised words `compBFO N [0, 3] [2] prog` -/
theorem implements1_of_execO {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ 16) (prog : Mach.BStmt) (hwf : rvF.wfB N [0, 3] [2] prog) (wn : Nat → Nat)
    (space : Nat → Nat) (hsp : ∀ n, 8 * wn n + 8 * (N + 1) + 7 ≤ space n) (maxLen : Nat) (retLen : Bool)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv),
      env 1 = BitVec.ofNat 64 (encA a).length → (∀ j, 8 ≤ j → env j = 0) → (encA a).length ≤ maxLen →
      (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length → out.length < 2 ^ 32 →
      tbl.length = wn (encA a).length →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) :
    Implements1With encA encB (compBFO N [0, 3] [2] prog) f space maxLen retLen :=
  implements1_of_execOW encA encB f N (by unfold NS; omega) prog hwf wn space hsp maxLen retLen hex

end Proven.Mach.Riscv
