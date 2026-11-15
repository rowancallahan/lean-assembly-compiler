/- The optimising spill-slot compiler on RISC-V: `compileOptB` (byte blocks) with `compileOptB_ok` (the
statement of `compileBF_ok` for the words it returns) and the total drop-in `compileBFO`.

Which locals live in registers is chosen by an untrusted heuristic (`pickRegs`: most used first, loops
weighted); every choice is checked by the proved pipeline (`WideF.optB`), and the first that passes (cheapest candidate first) is used. -/
import Riscv.Back.Wide
import Riscv.Back.BStmt
import Compiler.Opt.BFn
import Compiler.Opt.Color
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

/-- **The Sail RV64 model is a `WideF` machine** (frame laws from `rvF`). -/
def rvwF : WideF where
  toWide := rvw
  encE n := encX (.enter n)
  encL := encX .leave
  keepF := rvF.keepF
  frameAt := rvF.frameAt
  enterOK := rvF.enterOK
  keepF_of_keep := rvF.keepF_of_keep
  keepF_trans := rvF.keepF_trans
  keep_of_keepF := rvF.keep_of_keepF
  keepF_ra := rvF.keepF_ra
  enterOK_frame := rvF.enterOK_frame
  f_enter := rvF.law_enter
  f_leave := rvF.law_leave

/-! ## The (untrusted) choice of registers -/

def cntE : Mach.BExp → Nat → Nat
  | .var i, x => if i = x then 1 else 0
  | .const _, _ => 0
  | .bin _ a b, x => cntE a x + cntE b x
  | .ite c a b, x => cntE c x + cntE a x + cntE b x

/-- weighted number of uses of variable `x` (a loop body counts 8 times) -/
def score : Mach.BStmt → Nat → Nat
  | .assign v e, x => (if v = x then 1 else 0) + cntE e x
  | .load v _ i, x => (if v = x then 1 else 0) + cntE i x
  | .store _ i e, x => cntE i x + cntE e x
  | .seq p q, x => score p x + score q x
  | .loop c b, x => 8 * (cntE c x + score b x)
  | .load64 v _ i, x => (if v = x then 1 else 0) + cntE i x
  | .store64 _ i e, x => cntE i x + cntE e x
  | .mop _ v a b, x => (if v = x then 1 else 0) + cntE a x + cntE b x

/-- the `k` most used locals (slot indices) -/
def pickRegs (p : Mach.BStmt) (N k : Nat) : List Nat :=
  ((List.range N).mergeSort fun a b => score p (8 + b) ≤ score p (8 + a)).take k

/-- scratch register -/
def scB : Reg := ⟨6, by decide⟩

/-- `T` temporaries in `r0 .. r(T-1)`, the locals `regs` in `rT ..`, scratch `r6` -/
def gB (T : Nat) (regs : List Nat) (x : Nat) : Reg :=
  if 32 ≤ x then (if x - 32 < T then rk (x - 32) else scB)
  else if regs.idxOf (x - 8) < regs.length ∧ T + regs.idxOf (x - 8) < 6 then rk (T + regs.idxOf (x - 8)) else scB

/-- all sublists of `l` with `k` elements -/
def choose : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: l => (choose k l).map (x :: ·) ++ choose (k + 1) l

/-- candidate assignments `(T, locals in registers)`: the locals are among the 8 most used; cheapest
(least weighted uses left in slots) first -/
def candidates (p : Mach.BStmt) (N : Nat) : List (Nat × List Nat) :=
  let top := pickRegs p N 8
  let cost := fun (c : Nat × List Nat) => ((List.range N).filter fun j => !c.2.contains j).foldl (fun a j => a + score p (8 + j)) 0
  ([1, 2, 3, 4, 5, 6].flatMap fun T => (choose (min (6 - T) top.length) top).map fun r => (T, r)).mergeSort
    fun a b => cost a ≤ cost b

def tryB (N : Nat) (bv : List Nat) (p : Mach.BStmt) (c : Nat × List Nat) (wv : List Nat := []) :
    Option (List (BitVec 32)) :=
  rvwF.optB scB (gB c.1 c.2) (fun j => !c.2.contains j) N bv wv p

/-! ### Liveness-based choice (untrusted colouring, checked by `allocOK` inside `WideF.optB`) -/

def firstB {α : Type} (f : α → Option (List (BitVec 32))) : List α → Option (List (BitVec 32))
  | [] => none
  | T :: l => match f T with | some ws => some ws | none => firstB f l

theorem firstB_ok {α : Type} {f : α → Option (List (BitVec 32))} {ws : List (BitVec 32)} :
    ∀ {l : List α}, firstB f l = some ws → ∃ T, f T = some ws
  | [], h => nomatch h
  | T :: l, h => by
    unfold firstB at h
    cases hf : f T with
    | some w => rw [hf] at h; exact ⟨T, hf.trans h⟩
    | none => rw [hf] at h; exact firstB_ok h

/-- the registers free for colouring: all but the scratch `r6`; the convention registers of the variables first (a short-lived register takes one where that variable is dead) -/
def colsB : List Reg := ((List.range 8).map (7 + ·) ++ List.range 6).map rk

/-- a colouring of the body `optB` builds, the locals `spl` in slots -/
def colorB (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) (spl : List Nat) (mode : Nat := 6) : Option (Nat → Reg) :=
  let sp := fun j => spl.contains j
  let c := IR.Code.seq (initL sp (List.range N)) (irB sp bv wv p)
  IR.color ((IR.cands [0, 1, 2, 3, 4, 5, 6, 7] c).getD mode c) [0, 1, 2, 3, 4, 5, 6, 7]
    (fun x => if h : x < 8 then some (avar ⟨x, h⟩) else none) colsB (fun _ => 0)

/-- a colouring of each candidate body (`IR.cands`), in the order `WideF.optB` tries them -/
def tryL (N : Nat) (bv : List Nat) (p : Mach.BStmt) (spl : List Nat) (wv : List Nat := []) :
    Option (List (BitVec 32)) :=
  firstB (fun mode => match colorB N bv wv p spl mode with
    | some g => rvwF.optB scB g (fun j => spl.contains j) N bv wv p
    | none => none) [0, 1, 2, 3, 4, 5, 6]

/-- spill sets to try: none, then one local, then two (cheapest by `score` first) -/
def spillSets (p : Mach.BStmt) (N : Nat) : List (List Nat) :=
  let cost := fun (l : List Nat) => l.foldl (fun a j => a + score p (8 + j)) 0
  [] :: (((List.range N).map fun j => [j]) ++ choose 2 (List.range N)).mergeSort fun a b => cost a ≤ cost b

/-- the locals the colouring of mode 0 leaves without a register, with `spl` spilled -/
def uncolB (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) (spl : List Nat) : List Nat :=
  let sp := fun j => spl.contains j
  let c := IR.Code.seq (initL sp (List.range N)) (irB sp bv wv p)
  ((IR.uncol ((IR.cands [0, 1, 2, 3, 4, 5, 6, 7] c).getD 0 c) [0, 1, 2, 3, 4, 5, 6, 7]
    (fun x => if h : x < 8 then some (avar ⟨x, h⟩) else none) colsB (fun _ => 0)).filterMap
    fun x => if 8 ≤ x ∧ x < 8 + N then some (x - 8) else none)

/-- spill sets grown one local at a time: the least used local the colouring leaves without a register (or the
least used one left) -/
def spillGrow (p : Mach.BStmt) (N : Nat) (bv wv : List Nat) (spl : List Nat) : Nat → List (List Nat)
  | 0 => []
  | k + 1 =>
    let by_ := fun (l : List Nat) => l.mergeSort fun a b => score p (8 + a) ≤ score p (8 + b)
    let u := by_ ((uncolB N bv wv p spl).filter fun j => !spl.contains j)
    let rest := by_ ((List.range N).filter fun j => !spl.contains j)
    match u ++ rest with
    | [] => [spl]
    | j :: _ => spl :: spillGrow p N bv wv (spl ++ [j]) k

/-- more than 16 locals: the locals `j ≥ 24` always spilled (`loB`); of the first set `spillGrow` finds and the
first of none, one, or the `k` least used others (cheapest first) that colour, the one with fewer words first -/
def spillSetsX (p : Mach.BStmt) (N : Nat) (bv wv : List Nat) : List (List Nat) :=
  if N ≤ 16 then spillSets p N else
  let cost := fun (l : List Nat) => l.foldl (fun a j => a + score p (8 + j)) 0
  let forced := (List.range N).filter (24 ≤ ·)
  let low := (List.range (min N 24)).mergeSort fun a b => score p (8 + a) ≤ score p (8 + b)
  let grow := spillGrow p N bv wv forced (low.length + 1)
  let greedy := (([] :: ((low.map fun j => [j]) ++ (List.range (low.length - 1)).map fun k => low.take (k + 2))).map
      (· ++ forced)).mergeSort fun a b => cost a ≤ cost b
  let first := fun (l : List (List Nat)) => l.findSome? fun spl => (tryL N bv p spl wv).map fun ws => (ws.length, spl)
  let best := match first grow, first greedy with
    | some (a, s), some (b, t) => if a ≤ b then [s] else [t]
    | some (_, s), none => [s]
    | none, some (_, t) => [t]
    | none, none => []
  best ++ grow ++ greedy

/-- the choice used by the compilers: liveness-checked colourings first (fewest weighted slot uses), then
the injective assignments -/
def pickB (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) : Option (List (BitVec 32)) :=
  match firstB (fun spl => tryL N bv p spl wv) (spillSetsX p N bv wv) with
  | some ws => some ws
  | none => firstB (fun c => tryB N bv p c wv) (candidates p N)

theorem pickB_ok {N : Nat} {bv wv : List Nat} {p : Mach.BStmt} {ws : List (BitVec 32)}
    (h : pickB N bv wv p = some ws) : ∃ g sp, rvwF.optB scB g sp N bv wv p = some ws := by
  unfold pickB at h
  cases hfl : firstB (fun spl => tryL N bv p spl wv) (spillSetsX p N bv wv) with
  | some w =>
    rw [hfl] at h; cases h
    obtain ⟨spl, h⟩ := firstB_ok hfl
    unfold tryL at h
    obtain ⟨u, h⟩ := firstB_ok h
    cases hg : colorB N bv wv p spl u with
    | none => rw [hg] at h; exact nomatch h
    | some g => rw [hg] at h; exact ⟨g, _, h⟩
  | none =>
    rw [hfl] at h; dsimp only at h
    obtain ⟨c, h⟩ := firstB_ok h
    exact ⟨_, _, h⟩

end Proven.Mach.Riscv

namespace Proven
open Mach Mach.Riscv

/-- **The optimising spill-slot compiler** (byte blocks). -/
def compileOptB (N : Nat) (bv : List Nat) (p : Proven.BStmt) : Except String (List (BitVec 32)) :=
  match pickB N bv [] (toMS p) with
  | some ws => .ok ws
  | none => .error "compileOptB: no register assignment passed the checks"

/-- **`compileOptB` is correct** (the statement of `compileBF_ok` for the words it returns). -/
theorem compileOptB_ok (N : Nat) (bv : List Nat) {p : Proven.BStmt} {ws : List (BitVec 32)}
    (hcmp : compileOptB N bv p = .ok ws)
    {R : List Proven.Region} (hR : RegOK R) {σ σ' : Proven.BState} (hex : Proven.BExec p σ σ') {s : St} (h : Cfg s)
    {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc ws) (hok : codeOK pc ws.length)
    (hf : FrOK N (frameBase N (getX s 2))) (hfd : ∀ r ∈ R, Proven.disjoint ⟨frameBase N (getX s 2), 8 * (N + 1)⟩ r)
    (hcd : ∀ r ∈ (⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Proven.Region) :: R,
      Proven.disjoint ⟨pc.toNat, 4 * ws.length⟩ r)
    (hreg : ∀ i : Fin 8, getX s (A8 i) = σ.env i.val) (hslot : ∀ j < N, σ.env (8 + j) = 0)
    (hheap : HeapRel bv R σ s) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 8, getX s' (A8 i) = σ'.env i.val) ∧
      HeapRel bv R σ' s' ∧ unchangedOutside s s' ((⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Proven.Region) :: R) ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 := by
  have hopt : ∃ g sp, rvwF.optB scB g sp N bv [] (toMS p) = some ws := by
    unfold compileOptB at hcmp
    cases hfb : pickB N bv [] (toMS p) with
    | none => rw [hfb] at hcmp; exact nomatch hcmp
    | some w => rw [hfb] at hcmp; cases hcmp; exact pickB_ok hfb
  obtain ⟨g, sp, hT⟩ := hopt
  have hcd' : ∀ r ∈ R.map toR ++ [] ++ [⟨rvwF.frameAt s N, 8 * (N + 1)⟩],
      Mach.disjoint ⟨pc.toNat, 4 * ws.length⟩ r := fun r hr => by
    rcases List.mem_append.1 hr with hr | hr
    · rw [List.append_nil] at hr
      obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact hcd r' (List.mem_cons_of_mem _ hr')
    · simp only [List.mem_singleton] at hr; subst hr; exact hcd _ (List.mem_cons_self ..)
  have hheap' : HeapI rvwF.toWide bv [] (R.map toR) [] (toMSt σ) s :=
    ⟨by simpa using hheap.hlen, by simpa using hheap.bvlen, fun b hb => by simpa [toR] using hheap.base b (by simpa using hb),
      fun b hb => by simpa [toR] using hheap.blen b (by simpa using hb),
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
      show getX s' (phys (avar i)) = _; rw [phys_avar]] at this, ⟨by simpa using p3.hlen, by simpa using p3.bvlen,
      fun b hb => by have := p3.base b (by simpa using hb); rw [getR hb] at this; exact this,
      fun b hb => by have := p3.blen b (by simpa using hb); rw [getR hb] at this; exact this,
      fun b hb => by
        have := p3.rbytes b (by simpa using hb); rw [getR hb] at this; exact (Mach.Riscv.bytes_eq s' _ _).symm.trans this⟩,
    fun a ha => p4 a fun r hr => ?_, p5, keep_calleeSaved h p5 p6, p6 3 phys_ne3⟩
  rcases List.mem_append.1 hr with hr | hr
  · rw [List.append_nil] at hr
    obtain ⟨r', hr', rfl⟩ := toR_mem hr; exact ha r' (List.mem_cons_of_mem _ hr')
  · simp only [List.mem_singleton] at hr; subst hr; exact ha _ (List.mem_cons_self ..)

/-- drop-in for `compileBF`: optimised words when the optimiser succeeds, the old words otherwise -/
def compileBFO (N : Nat) (bv : List Nat) (p : Proven.BStmt) : List (BitVec 32) :=
  match compileOptB N bv p with | .ok ws => ws | .error _ => compileBF N bv p

/-- the statement of `compileBF_ok` for `compileBFO` -/
theorem compileBFO_ok (N : Nat) (bv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N) {p : Proven.BStmt} (hp : p.wf N bv)
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
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 := by
  unfold compileBFO at hc hok hcd
  cases hx : compileOptB N bv p with
  | ok ws => rw [hx] at hc hok hcd; exact compileOptB_ok N bv hx hR hex h hpc hc hok hf hfd hcd hreg hslot hheap hra
  | error _ => rw [hx] at hc hok hcd; exact compileBF_ok' N bv hbv hp hR hex h hpc hc hok hf hfd hcd hreg hslot hheap hra

end Proven

namespace Proven.Mach.Riscv

/-! ## Drop-in for the middle compiler `rvF.compBF` (byte and word blocks) -/

/-- the optimised words for `rvF.compBF N bv wv p`, or the old words -/
def compBFO (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) : List (BitVec 32) :=
  match pickB N bv wv p with
  | some ws => ws
  | none => rvF.codeF (rvF.compBF N bv wv p)

/-- **the statement of `rvF.compBF_ok` for `compBFO`** -/
theorem compBFO_ok' (N : Nat) (bv wv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N) (hwv : ∀ x ∈ wv, x < 8 + N)
    {p : Mach.BStmt} (hp : rvF.wfB N bv wv p) {R W : List Region} {σ σ' : Mach.BState} (hex : Mach.BExec p σ σ')
    {s : St} {pc : BitVec 64} (hA : rvF.At s pc (compBFO N bv wv p)) (hen : rvF.enterOK s N)
    (hL : rvF.Lay N (rvF.frameAt s N) R W)
    (hcd : ∀ r ∈ R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩],
      Mach.disjoint ⟨pc.toNat, 4 * (compBFO N bv wv p).length⟩ r)
    (hreg : ∀ i : Fin 8, rvF.get s (avar i) = σ.env i.val) (hslot : ∀ j, j < N → σ.env (8 + j) = 0)
    (hheap : rvF.HeapB bv wv R W σ s) (hra : rvF.retOK (rvF.ra s)) :
    rvF.runsTo s fun s' => rvF.pcIs s' (rvF.ra s) ∧ (∀ i : Fin 8, rvF.get s' (avar i) = σ'.env i.val) ∧
      rvF.HeapB bv wv R W σ' s' ∧ Out (R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩]) (rvF.mem s) (rvF.mem s') ∧
      rvF.ok s' ∧ rvF.keep s s' := by
  unfold compBFO at hA hcd
  cases hx : pickB N bv wv p with
  | none => rw [hx] at hA hcd; exact rvF.compBF_ok N bv wv hbv hwv hp hex hA hen hL hcd hreg hslot hheap hra
  | some ws =>
    rw [hx] at hA hcd
    obtain ⟨g, sp, hc⟩ := pickB_ok hx
    have := rvwF.optB_ok hc hex hA hen
      (fun r hr => (List.mem_append.1 hr).elim (hL.ram r) (hL.wram r))
      (fun r hr a h1 h2 _ _ => by
        have h' : 0x80000000 ≤ r.base ∧ r.base + r.len ≤ 0x100000000 :=
          (List.mem_append.1 hr).elim (hL.ram r) (hL.wram r)
        show 0x80000000 ≤ a ∧ a + 1 ≤ 0x100000000; omega)
      hL.rp hL.wp hL.rw hL.wal
      (fun r hr => (List.mem_append.1 hr).elim (hL.fr r) (hL.fw r)) hcd hreg hslot
      ⟨hheap.hlen, hheap.bvlen, hheap.base, hheap.blen, hheap.rbytes, hheap.whlen, hheap.wvlen, hheap.wbase,
        hheap.wblen, hheap.wbyts⟩ hra
    exact runsTo_mono this fun s' ⟨p1, p2, p3, p4, p5, p6⟩ =>
      ⟨p1, p2, ⟨p3.hlen, p3.bvlen, p3.base, p3.blen, p3.rbytes, p3.whlen, p3.wvlen, p3.wbase, p3.wblen, p3.wbyts⟩,
        p4, p5, p6⟩

end Proven.Mach.Riscv

namespace Proven.Mach.Riscv

/-! ## Checked words without the fallback (`compBFC`)

`compBFO` falls back to the plain words, so its theorem needs `rvF.wfB` (loop bodies under 1024 plain words).
`compBFC` takes the choice `(t, spl)` found by `pickC` (a register table and the spilled locals) and keeps only the
optimised words; its theorem needs only that `optB` accepts the choice (`decide +kernel`). -/

/-- the register of `x` in table `t` (scratch for the rest) -/
def tblG (t : List (Nat × Reg)) (x : Nat) : Reg := (t.lookup x).getD scB

/-- the optimised words for the choice `(t, spl)` (`[]` if `optB` rejects it) -/
def compBFC (N : Nat) (bv wv : List Nat) (t : List (Nat × Reg)) (spl : List Nat) (p : Mach.BStmt) :
    List (BitVec 32) :=
  (rvwF.optB scB (tblG t) (fun j => spl.contains j) N bv wv p).getD []

/-- the table of `g` on `0 .. M - 1` (entries other than scratch) -/
def tabulate (g : Nat → Reg) (M : Nat) : List (Nat × Reg) :=
  (List.range M).filterMap fun x => if g x = scB then none else some (x, g x)

/-- (untrusted) a choice in the order of `pickB`, tabulated on the virtual registers below `M` -/
def pickC (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) (M : Nat := 4096) : Option (List (Nat × Reg) × List Nat) :=
  let ok := fun (t : List (Nat × Reg)) (spl : List Nat) =>
    (rvwF.optB scB (tblG t) (fun j => spl.contains j) N bv wv p).isSome
  let col := (spillSetsX p N bv wv).findSome? fun spl => [0, 1, 2, 3, 4, 5, 6].findSome? fun mode =>
    match colorB N bv wv p spl mode with
    | some g => let t := tabulate g M; if ok t spl then some (t, spl) else none
    | none => none
  match col with
  | some r => some r
  | none => (candidates p N).findSome? fun c =>
      let t := tabulate (gB c.1 c.2) M; let spl := (List.range N).filter fun j => !c.2.contains j
      if ok t spl then some (t, spl) else none

/-- **the statement of `compBFO_ok'` for `compBFC`**, with "`optB` accepts" in place of `wfB` -/
theorem compBFC_ok' (N : Nat) (bv wv : List Nat) {t : List (Nat × Reg)} {spl : List Nat} {p : Mach.BStmt}
    (hc : (rvwF.optB scB (tblG t) (fun j => spl.contains j) N bv wv p).isSome = true)
    {R W : List Region} {σ σ' : Mach.BState} (hex : Mach.BExec p σ σ')
    {s : St} {pc : BitVec 64} (hA : rvF.At s pc (compBFC N bv wv t spl p)) (hen : rvF.enterOK s N)
    (hL : rvF.Lay N (rvF.frameAt s N) R W)
    (hcd : ∀ r ∈ R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩],
      Mach.disjoint ⟨pc.toNat, 4 * (compBFC N bv wv t spl p).length⟩ r)
    (hreg : ∀ i : Fin 8, rvF.get s (avar i) = σ.env i.val) (hslot : ∀ j, j < N → σ.env (8 + j) = 0)
    (hheap : rvF.HeapB bv wv R W σ s) (hra : rvF.retOK (rvF.ra s)) :
    rvF.runsTo s fun s' => rvF.pcIs s' (rvF.ra s) ∧ (∀ i : Fin 8, rvF.get s' (avar i) = σ'.env i.val) ∧
      rvF.HeapB bv wv R W σ' s' ∧ Out (R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩]) (rvF.mem s) (rvF.mem s') ∧
      rvF.ok s' ∧ rvF.keep s s' := by
  unfold compBFC at hA hcd
  cases hx : rvwF.optB scB (tblG t) (fun j => spl.contains j) N bv wv p with
  | none => rw [hx] at hc; exact nomatch hc
  | some ws =>
    rw [hx] at hA hcd
    have := rvwF.optB_ok hx hex hA hen
      (fun r hr => (List.mem_append.1 hr).elim (hL.ram r) (hL.wram r))
      (fun r hr a h1 h2 _ _ => by
        have h' : 0x80000000 ≤ r.base ∧ r.base + r.len ≤ 0x100000000 :=
          (List.mem_append.1 hr).elim (hL.ram r) (hL.wram r)
        show 0x80000000 ≤ a ∧ a + 1 ≤ 0x100000000; omega)
      hL.rp hL.wp hL.rw hL.wal
      (fun r hr => (List.mem_append.1 hr).elim (hL.fr r) (hL.fw r)) hcd hreg hslot
      ⟨hheap.hlen, hheap.bvlen, hheap.base, hheap.blen, hheap.rbytes, hheap.whlen, hheap.wvlen, hheap.wbase,
        hheap.wblen, hheap.wbyts⟩ hra
    exact runsTo_mono this fun s' ⟨p1, p2, p3, p4, p5, p6⟩ =>
      ⟨p1, p2, ⟨p3.hlen, p3.bvlen, p3.base, p3.blen, p3.rbytes, p3.whlen, p3.wvlen, p3.wbase, p3.wblen, p3.wbyts⟩,
        p4, p5, p6⟩

end Proven.Mach.Riscv
