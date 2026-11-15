/- The optimising spill-slot compiler on DeepMind's AArch64 semantics: `compBFOA` = the words of
`WideF.optB` over `apcwF` with the register assignment found by the (untrusted) search of `Riscv/Back/OptB.lean`
(staged, `Apc/Src/Search.lean`), falling back to `MachineF.compBF`; `compBFOA_ok` (the shape of `compBF_ok`).
Clients: the branchy merge sort (`msortO_apc`) and CRC-32 (`crc_apc` unoptimised, `crcO_apc` optimised; source
proof `crcP_exec` of `Riscv/Examples/Crc.lean`, staged unchanged). -/
import Apc.Msort
import Apc.Src.Search
import Apc.Src.Crc
namespace Proven.Apc
open Proven Proven.Mach

/-! ## The words do not depend on the layout -/
theorem wcode_L (L L' : Lay) : ∀ l : List WOp, (apcwF L).toWide.wcode l = (apcwF L').toWide.wcode l
  | [] => rfl
  | o :: l => by
    show wencA o ++ (apcwF L).toWide.wcode l = wencA o ++ (apcwF L').toWide.wcode l; rw [wcode_L L L' l]
theorem lowIns_L (L L' : Lay) (sc : Reg) (i : IR.Ins Reg) :
    (apcwF L).toWide.lowIns sc i = (apcwF L').toWide.lowIns sc i := by
  cases i <;> rfl
theorem low_L (L L' : Lay) (sc : Reg) : ∀ c : IR.Code Reg, (apcwF L).toWide.low sc c = (apcwF L').toWide.low sc c := by
  intro c; induction c with
  | skip => rfl
  | ins i => exact lowIns_L L L' sc i
  | seq a b iha ihb => simp only [Wide.low, iha, ihb]
  | when t b ih => simp only [Wide.low, ih, wcode_L L L']; rfl
  | loop pre t b ihp ihb => simp only [Wide.low, ihp, ihb, wcode_L L L']; rfl
  | loop2 p₁ t₁ p₂ t₂ b ih₁ ih₂ ihb => simp only [Wide.low, ih₁, ih₂, ihb, wcode_L L L']; rfl
theorem wf_L (L L' : Lay) (sc : Reg) : ∀ c : IR.Code Reg, (apcwF L).toWide.wf sc c = (apcwF L').toWide.wf sc c := by
  intro c; induction c with
  | skip => rfl
  | ins i => cases i <;> rfl
  | seq a b iha ihb => simp only [Wide.wf, iha, ihb]
  | when t b ih => simp only [Wide.wf, ih, low_L L L', wcode_L L L']; rfl
  | loop pre t b ihp ihb => simp only [Wide.wf, ihp, ihb, low_L L L', wcode_L L L']; rfl
  | loop2 p₁ t₁ p₂ t₂ b ih₁ ih₂ ihb => simp only [Wide.wf, ih₁, ih₂, ihb, low_L L L', wcode_L L L']; rfl
theorem optB_L (L L' : Lay) (sc : Reg) (g : Nat → Reg) (sp : Nat → Bool) (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) :
    (apcwF L).optB sc g sp N bv wv p = (apcwF L').optB sc g sp N bv wv p := by
  simp only [WideF.optB, Wide.bodySR, Wide.body, Wide.W, wf_L L L', low_L L L', wcode_L L L']; rfl

/-- the optimised words when the search succeeds, the `compBF` words otherwise -/
def compBFOA (L : Lay) (N : Nat) (bv wv : List Nat) (p : Mach.BStmt) : List (BitVec 32) :=
  match ApcS.pickB N bv wv p with
  | some ws => ws
  | none => (apcF L).codeF ((apcF L).compBF N bv wv p)

/-- **The optimising compiler, correct on DeepMind's AArch64 semantics** (conclusion of `compBF_ok`). -/
theorem compBFOA_ok (L : Lay) (N : Nat) (bv wv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N) (hwv : ∀ x ∈ wv, x < 8 + N)
    {p : Mach.BStmt} (hp : (apcF L).wfB N bv wv p) {R W : List Region} {σ σ' : Mach.BState} (hex : Mach.BExec p σ σ')
    {s : Arm64.State} {pc : BitVec 64} (hA : (apcF L).At s pc (compBFOA L N bv wv p)) (hen : enterOK L s N)
    (hL : (apcF L).Lay N (frameAt s N) R W)
    (hcd : ∀ r ∈ R ++ W ++ [⟨frameAt s N, 8 * (N + 1)⟩], disjoint ⟨pc.toNat, 4 * (compBFOA L N bv wv p).length⟩ r)
    (hreg : ∀ i : Fin 8, (apcF L).get s (avar i) = σ.env i.val) (hslot : ∀ j, j < N → σ.env (8 + j) = 0)
    (hheap : (apcF L).HeapB bv wv R W σ s) :
    (apcF L).runsTo s fun s' => (apcF L).pcIs s' ((apcF L).ra s) ∧
      (∀ i : Fin 8, (apcF L).get s' (avar i) = σ'.env i.val) ∧ (apcF L).HeapB bv wv R W σ' s' ∧
      Out (R ++ W ++ [⟨frameAt s N, 8 * (N + 1)⟩]) ((apcF L).mem s) ((apcF L).mem s') ∧ (apcF L).ok s' ∧
      (apcF L).keep s s' := by
  unfold compBFOA at hA hcd
  cases hq : ApcS.pickB N bv wv p with
  | some ws =>
    rw [hq] at hA hcd
    obtain ⟨g, sp, hopt⟩ := ApcS.pickB_ok hq
    have hopt' : (apcwF L).optB ApcS.scB g sp N bv wv p = some ws := (optB_L L L0 _ _ _ _ _ _ _).trans hopt
    have hI : HeapI (apcwF L).toWide bv wv R W σ s :=
      ⟨hheap.hlen, hheap.bvlen, hheap.base, hheap.blen, hheap.rbytes, hheap.whlen, hheap.wvlen, hheap.wbase,
        hheap.wblen, hheap.wbyts⟩
    have := (apcwF L).optB_ok hopt' hex hA hen
      (fun r hr => by rcases List.mem_append.1 hr with h | h; exact hL.ram r h; exact hL.wram r h)
      (fun r hr => by rcases List.mem_append.1 hr with h | h; exact hL.wr r h; exact hL.wwr r h)
      hL.rp hL.wp hL.rw hL.wal
      (fun r hr => by rcases List.mem_append.1 hr with h | h; exact hL.fr r h; exact hL.fw r h)
      hcd hreg hslot hI trivial
    refine (core L).runsTo_mono this fun s' ⟨p1, p2, p3, p4, p5, p6⟩ => ⟨p1, p2, ?_, p4, p5, p6⟩
    exact ⟨p3.hlen, p3.bvlen, p3.base, p3.blen, p3.rbytes, p3.whlen, p3.wvlen, p3.wbase, p3.wblen, p3.wbyts⟩
  | none =>
    rw [hq] at hA hcd
    exact (apcF L).compBF_ok N bv wv hbv hwv hp hex hA hen hL hcd hreg hslot hheap trivial

/-! ## The branchy merge sort, optimised -/

/-- the optimised merge sort for this target -/
def msortCodeO : List (BitVec 32) := compBFOA L0 7 [0, 2, 3] [] msortB

/-- **Optimised merge sort on DeepMind's AArch64 semantics** (the statement of `msort_apc`, words `msortCodeO`). -/
theorem msortO_apc (L : Lay) {s : Arm64.State} {pc : BitVec 64} (hA : (apcF L).At s pc (compBFOA L 7 [0, 2, 3] [] msortB))
    (hen : enterOK L s 7) {xs scr out : List (BitVec 8)} {inb scb outb : Nat} (hn : xs.length < 2 ^ 32)
    (hi : L.dLo ≤ inb ∧ inb + xs.length ≤ L.dHi) (hs' : L.dLo ≤ scb ∧ scb + xs.length ≤ L.dHi)
    (ho' : L.dLo ≤ outb ∧ outb + xs.length ≤ L.dHi)
    (hdis : [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩].Pairwise disjoint)
    (hfd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩], disjoint ⟨frameAt s 7, 64⟩ r)
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩, ⟨frameAt s 7, 64⟩],
      disjoint ⟨pc.toNat, 4 * (compBFOA L 7 [0, 2, 3] [] msortB).length⟩ r)
    (h0 : s.regs.read 0#5 = BitVec.ofNat 64 inb) (h1 : s.regs.read 1#5 = BitVec.ofNat 64 xs.length)
    (h2 : s.regs.read 2#5 = BitVec.ofNat 64 scb) (h3 : s.regs.read 3#5 = BitVec.ofNat 64 outb)
    (hx : bytes (memV s) inb xs.length = xs.map some) (hs : bytes (memV s) scb xs.length = scr.map some)
    (ho : bytes (memV s) outb xs.length = out.map some) :
    ∃ s', Arm64.Steps P s s' ∧ s'.pc = s.regs.read 30#5 ∧
      bytes (memV s') outb xs.length = (xs.mergeSort leB).map some ∧ bytes (memV s') inb xs.length = xs.map some ∧
      Out [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩, ⟨frameAt s 7, 64⟩] (memV s) (memV s') ∧
      s'.status = .Running ∧ s'.sp = s.sp ∧ s'.regs.read 28#5 = s.regs.read 28#5 ∧
      ∀ x : BitVec 5, (∀ r, xr r ≠ x) → s'.regs.read x = s.regs.read x := by
  have hsl : scr.length = xs.length := by simpa [length_bytes] using (congrArg List.length hs).symm
  have hol : out.length = xs.length := by simpa [length_bytes] using (congrArg List.length ho).symm
  let env : BEnv := fun i => if h : i < 8 then (apcF L).get s (avar ⟨i, h⟩) else 0
  obtain ⟨σ', hex, scr', hh⟩ := msortProgB_mergeSort xs scr out ⟨env, [xs, scr, out]⟩ rfl
    (by simp only [env]; rw [dite_eq_left_of_eq_true (by decide)]; exact h1) hn hsl hol
  have R3 : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨scb, xs.length⟩, ⟨outb, xs.length⟩],
      L.dLo ≤ r.base ∧ r.base + r.len ≤ L.dHi := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  have hd := hen.2.2.2.2.2
  have hL : (apcF L).Lay 7 (frameAt s 7) [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩] [] :=
    { ram := fun r hr => ⟨Nat.zero_le _, by have := R3 r hr; show _ ≤ 2 ^ 64 - 1; omega⟩
      wram := fun r hr => by simp at hr
      rp := hdis
      wp := List.Pairwise.nil
      rw := fun r _ w hw => by simp at hw
      fr := hfd
      fw := fun w hw => by simp at hw
      wal := fun w hw => by simp at hw
      wr := fun r hr a h1 h2 _ _ => by have := R3 r hr; exact ⟨by omega, by omega⟩
      wwr := fun w hw => by simp at hw }
  have hheap : (apcF L).HeapB [0, 2, 3] [] [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩] []
      (Riscv.toMSt ⟨env, [xs, scr, out]⟩) s :=
    { hlen := rfl, bvlen := rfl,
      base := fun b hb => by
        obtain _ | _ | _ | b := b
        · exact h0
        · exact h2
        · exact h3
        · simp at hb; omega
      blen := fun b hb => by
        obtain _ | _ | _ | b := b
        · rfl
        · exact hsl
        · exact hol
        · simp at hb; omega
      rbytes := fun b hb => by
        obtain _ | _ | _ | b := b
        · exact hx
        · exact hs
        · exact ho
        · simp at hb; omega
      whlen := rfl, wvlen := rfl, wbase := fun b hb => by simp at hb, wblen := fun b hb => by simp at hb,
      wbyts := fun b hb => by simp at hb }
  obtain ⟨s', hst, p1, -, p3, p4, p5, p6⟩ := compBFOA_ok L 7 [0, 2, 3] [] (by decide) (by simp) (msortB_wf L)
    (Riscv.exec_toM hex) hA hen hL hcd (fun i => by simp [env, Riscv.toMSt])
    (fun j hj => by simp [env, Riscv.toMSt]; omega) hheap
  have e0 := p3.rbytes 0 (by simp); have e2 := p3.rbytes 2 (by simp)
  simp only [Riscv.toMSt, hh] at e0 e2
  have e2' : bytes ((apcF L).mem s') outb xs.length = (xs.mergeSort leB).map some := by simpa using e2
  have e0' : bytes ((apcF L).mem s') inb xs.length = xs.map some := by simpa using e0
  have p4' : Out [⟨inb, xs.length⟩, ⟨scb, xs.length⟩, ⟨outb, xs.length⟩, ⟨frameAt s 7, 64⟩]
      ((apcF L).mem s) ((apcF L).mem s') := by simpa using p4
  exact ⟨s', hst, p1, e2', e0', p4', p5.1, p6.2, (apcF L).keep_fr p6, fun x hx => p6.1 x hx id⟩

/-! ## CRC-32 -/
open Proven.Crc in
/-- what a compiled `crcP` (`N = 0`, byte blocks at v0 / v3, the word table at v2) does: the conclusion of
`compBF_ok` -/
def RunsCrc (L : Lay) (ws : List (BitVec 32)) : Prop :=
  ∀ {R W : List Region} {σ σ' : Mach.BState} {s : Arm64.State} {pc : BitVec 64}, Mach.BExec crcP σ σ' →
    (apcF L).At s pc ws → enterOK L s 0 → (apcF L).Lay 0 (frameAt s 0) R W →
    (∀ r ∈ R ++ W ++ [⟨frameAt s 0, 8 * (0 + 1)⟩], disjoint ⟨pc.toNat, 4 * ws.length⟩ r) →
    (∀ i : Fin 8, (apcF L).get s (avar i) = σ.env i.val) → (apcF L).HeapB [0, 3] [2] R W σ s →
    (apcF L).runsTo s fun s' => (apcF L).pcIs s' ((apcF L).ra s) ∧ (apcF L).HeapB [0, 3] [2] R W σ' s' ∧
      Out (R ++ W ++ [⟨frameAt s 0, 8 * (0 + 1)⟩]) ((apcF L).mem s) ((apcF L).mem s') ∧ (apcF L).ok s' ∧
      (apcF L).keep s s'

open Proven.Crc in
set_option maxRecDepth 100000 in
theorem crc_wf0 : (apcF L0).wfB 0 [0, 3] [2] crcP := by
  simp only [crcP, tableLoop, mainLoop, rep, stepE, Riscv.store8, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt]
  repeat' apply And.intro
  all_goals first | decide | (show _ < 1024; decide +kernel)

/-- the compiled CRC-32, unoptimised and optimised -/
def crcCode : List (BitVec 32) := (apcF L0).codeF ((apcF L0).compBF 0 [0, 3] [2] Crc.crcP)
def crcCodeO : List (BitVec 32) := compBFOA L0 0 [0, 3] [2] Crc.crcP
set_option maxRecDepth 100000 in
theorem crc_wf (L : Lay) : (apcF L).wfB 0 [0, 3] [2] Crc.crcP := crc_wf0

set_option maxRecDepth 100000 in
theorem runsCrc (L : Lay) : RunsCrc L ((apcF L).codeF ((apcF L).compBF 0 [0, 3] [2] Crc.crcP)) :=
  fun hex hA hen hL hcd hreg hheap => (core L).runsTo_mono
    ((apcF L).compBF_ok 0 [0, 3] [2] (by decide) (by decide) (crc_wf L) hex hA hen hL hcd hreg (fun j hj => absurd hj (by omega))
      hheap trivial) fun _ ⟨p1, _, p3, p4, p5, p6⟩ => ⟨p1, p3, p4, p5, p6⟩

theorem runsCrcO (L : Lay) : RunsCrc L (compBFOA L 0 [0, 3] [2] Crc.crcP) :=
  fun hex hA hen hL hcd hreg hheap => (core L).runsTo_mono
    (compBFOA_ok L 0 [0, 3] [2] (by decide) (by decide) (crc_wf L) hex hA hen hL hcd hreg (fun j hj => absurd hj (by omega))
      hheap) fun _ ⟨p1, _, p3, p4, p5, p6⟩ => ⟨p1, p3, p4, p5, p6⟩

open Proven.Crc in
/-- **CRC-32 on DeepMind's AArch64 semantics**, for any code `ws` that runs `crcP` (`RunsCrc`: the unoptimised and
the optimised words).  Input `xs` at x0 (length in x1), a 2048-byte 8-aligned table block at x2 (any 256 words),
a 4-byte output block at x3; all in the writable data range, pairwise disjoint, disjoint from the frame
`[sp - 8, sp)` and the code.  The run returns to x30 with the 4 little-endian bytes of `crc32 xs` in the output. -/
theorem crc_apc_of {L : Lay} {ws : List (BitVec 32)} (hrun : RunsCrc L ws) {s : Arm64.State} {pc : BitVec 64}
    (hA : (apcF L).At s pc ws) (hen : enterOK L s 0) {xs : List UInt8} {out : List (BitVec 8)} {tbl : List (BitVec 64)}
    {inb outb tb : Nat} (hn : xs.length < 2 ^ 32) (hol : out.length = 4) (htl : tbl.length = 256) (htal : tb % 8 = 0)
    (hi : L.dLo ≤ inb ∧ inb + xs.length ≤ L.dHi) (ho' : L.dLo ≤ outb ∧ outb + 4 ≤ L.dHi)
    (ht' : L.dLo ≤ tb ∧ tb + 2048 ≤ L.dHi)
    (hdis : [(⟨inb, xs.length⟩ : Region), ⟨outb, 4⟩, ⟨tb, 2048⟩].Pairwise disjoint)
    (hfd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, 4⟩, ⟨tb, 2048⟩], disjoint ⟨frameAt s 0, 8⟩ r)
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, 4⟩, ⟨tb, 2048⟩, ⟨frameAt s 0, 8⟩],
      disjoint ⟨pc.toNat, 4 * ws.length⟩ r)
    (h0 : s.regs.read 0#5 = BitVec.ofNat 64 inb) (h1 : s.regs.read 1#5 = BitVec.ofNat 64 xs.length)
    (h2 : s.regs.read 2#5 = BitVec.ofNat 64 tb) (h3 : s.regs.read 3#5 = BitVec.ofNat 64 outb)
    (hx : bytes (memV s) inb xs.length = xs.map (some ·.toBitVec)) (ho : bytes (memV s) outb 4 = out.map some)
    (ht : bytes (memV s) tb 2048 = (wbytes tbl).map some) :
    ∃ s', Arm64.Steps P s s' ∧ s'.pc = s.regs.read 30#5 ∧
      bytes (memV s') outb 4 = (enc32 (crc32 xs)).map (some ·.toBitVec) ∧
      bytes (memV s') inb xs.length = xs.map (some ·.toBitVec) ∧
      Out [⟨inb, xs.length⟩, ⟨outb, 4⟩, ⟨tb, 2048⟩, ⟨frameAt s 0, 8⟩] (memV s) (memV s') ∧
      s'.status = .Running ∧ s'.sp = s.sp ∧ ∀ x : BitVec 5, (∀ r, xr r ≠ x) → s'.regs.read x = s.regs.read x := by
  let env : BEnv := fun i => if h : i < 8 then (apcF L).get s (avar ⟨i, h⟩) else 0
  obtain ⟨σ', out', hex, hh, htk, -⟩ := crcP_exec ⟨env, [xs.map (·.toBitVec), out], [tbl]⟩ xs out tbl rfl rfl htl
    (by simp only [env]; rw [dite_eq_left_of_eq_true (by decide)]; exact h1) hn (by omega)
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13⟩, d23⟩ := hdis
  have hd := hen.2.2.2.2.2
  have hL : (apcF L).Lay 0 (frameAt s 0) [⟨inb, xs.length⟩, ⟨outb, 4⟩] [⟨tb, 2048⟩] :=
    { ram := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨Nat.zero_le _, by show _ ≤ 2 ^ 64 - 1; dsimp only; omega⟩
      wram := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨Nat.zero_le _, by show _ ≤ 2 ^ 64 - 1; dsimp only; omega⟩
      rp := List.pairwise_pair.2 d12
      wp := List.pairwise_singleton _ _
      rw := fun r hr w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hw; subst hw
        rcases hr with rfl | rfl; exact d13; exact d23.1
      fr := fun r hr => hfd r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
      fw := fun w hw => hfd w (by simp only [List.mem_singleton] at hw; subst hw; simp)
      wal := fun w hw => by simp only [List.mem_singleton] at hw; subst hw; exact htal
      wr := fun r hr a h1 h2 _ _ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> (dsimp only at h1 h2; exact ⟨by omega, by omega⟩)
      wwr := fun w hw a h1 h2 _ _ => by
        simp only [List.mem_singleton] at hw; subst hw; dsimp only at h1 h2; exact ⟨by omega, by omega⟩ }
  have hheap : (apcF L).HeapB [0, 3] [2] [⟨inb, xs.length⟩, ⟨outb, 4⟩] [⟨tb, 2048⟩]
      ⟨env, [xs.map (·.toBitVec), out], [tbl]⟩ s :=
    { hlen := rfl, bvlen := rfl,
      base := fun b hb => by
        obtain _ | _ | b := b
        · exact h0
        · exact h3
        · simp at hb; omega
      blen := fun b hb => by
        obtain _ | _ | b := b
        · simp
        · exact hol
        · simp at hb; omega
      rbytes := fun b hb => by
        obtain _ | _ | b := b
        · show bytes (memV s) inb xs.length = (xs.map (·.toBitVec)).map some; rw [hx, List.map_map]; rfl
        · exact ho
        · simp at hb; omega
      whlen := rfl, wvlen := rfl,
      wbase := fun b hb => by obtain _ | b := b; exact h2; simp at hb
      wblen := fun b hb => by obtain _ | b := b; show 8 * tbl.length = 2048; omega; simp at hb
      wbyts := fun b hb => by obtain _ | b := b; exact ht; simp at hb }
  obtain ⟨s', hst, p1, p3, p4, p5, p6⟩ := hrun hex hA hen hL (by simpa using hcd)
    (fun i => by simp [env]) hheap
  have e0 := p3.rbytes 0 (by simp); have e1 := p3.rbytes 1 (by simp); have l1 := p3.blen 1 (by simp)
  simp only [hh] at e0 e1 l1
  have hout' : out' = (enc32 (crc32 xs)).map (·.toBitVec) := by
    rw [← htk]; exact (List.take_of_length_le (by simp at l1; omega)).symm
  have e1' : bytes ((apcF L).mem s') outb 4 = (enc32 (crc32 xs)).map (some ·.toBitVec) := by
    have h := e1; simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some] at h
    rw [h, hout', List.map_map]; rfl
  have e0' : bytes ((apcF L).mem s') inb xs.length = xs.map (some ·.toBitVec) := by
    have h := e0; simp only [List.getElem_cons_zero, List.getElem?_cons_zero, Option.getD_some] at h
    rw [h, List.map_map]; rfl
  have p4' : Out [⟨inb, xs.length⟩, ⟨outb, 4⟩, ⟨tb, 2048⟩, ⟨frameAt s 0, 8⟩] ((apcF L).mem s) ((apcF L).mem s') := by
    simpa using p4
  exact ⟨s', hst, p1, e1', e0', p4', p5.1, p6.2, fun x hx => p6.1 x hx id⟩

/-- **CRC-32, unoptimised words** -/
theorem crc_apc (L : Lay) : RunsCrc L ((apcF L).codeF ((apcF L).compBF 0 [0, 3] [2] Crc.crcP)) := runsCrc L
/-- **CRC-32, optimised words** -/
theorem crcO_apc (L : Lay) : RunsCrc L (compBFOA L 0 [0, 3] [2] Crc.crcP) := runsCrcO L

end Proven.Apc
