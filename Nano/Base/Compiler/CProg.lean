/- Middle layer, whole programs with calls: layout of the function table, the entry stub, and the
top-level theorem `compP_ok` from the `MachineC` laws.

Layout: `stub ++ code of function 0 ++ code of function 1 ++ ..`.  The stub is an ordinary function in the
sense of `compBF` (called with the return address in the link register): `enter 0` (frame register from the
stack pointer, old frame register saved), `enterC 0` (return address saved), `res := main()`, `leaveC 0`,
`leave`, `ret`.  The stack of the run is the area `[lo, frameAt s 0)` below the stub's frame. -/
import Nano.Base.Compiler.CStmt

namespace Proven.Mach
open MachineF

theorem out_stk {R Wr : List Region} {a l lo top : Nat} {m m' : Mem} (h : Out [⟨a, l⟩] m m') (h1 : lo ≤ a)
    (h2 : a + l ≤ top) : Out (R ++ Wr ++ [⟨lo, top - lo⟩]) m m' :=
  Out.mono h fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact ⟨_, memLast, h1, by dsimp only; omega⟩

namespace MachineC
variable (M : MachineC) (P : Prog) (bv wv : List Nat)

/-- the word where function `f` of the table `Fs` (placed at `start`) begins -/
def offs (start : Nat) : List Fn → Nat → Nat
  | [], _ => start
  | _ :: _, 0 => start
  | F :: Fs, f + 1 => offs (start + M.lenF P bv wv F) Fs f

/-- the code of the table `Fs` placed at `pos` -/
def fnsC (off : Nat → Nat) : Nat → List Fn → List YOp
  | _, [] => []
  | pos, F :: Fs => M.fnC P bv wv off pos F ++ fnsC off (pos + M.lenF P bv wv F) Fs

theorem fns_sub (off : Nat → Nat) : ∀ (Fs : List Fn) (start : Nat) (pre : List (BitVec 32)), pre.length = start →
    ∀ f (hf : f < Fs.length), Sub (pre ++ M.codeC (M.fnsC P bv wv off start Fs)) (M.offs P bv wv start Fs f)
      (M.codeC (M.fnC P bv wv off (M.offs P bv wv start Fs f) Fs[f]))
  | F :: Fs, start, pre, hp, 0, _ =>
    ⟨pre, M.codeC (M.fnsC P bv wv off (start + M.lenF P bv wv F) Fs), by
      show pre ++ M.codeC (M.fnC P bv wv off start F ++ _) = pre ++ M.codeC (M.fnC P bv wv off start F) ++ _
      rw [codeC_append, List.append_assoc], hp⟩
  | F :: Fs, start, pre, hp, f + 1, hf => by
    have hf' : f < Fs.length := by simp only [List.length_cons] at hf; omega
    have := fns_sub off Fs (start + M.lenF P bv wv F) (pre ++ M.codeC (M.fnC P bv wv off start F))
      (by rw [List.length_append, len_fnC, hp]) f hf'
    show Sub (pre ++ M.codeC (M.fnC P bv wv off start F ++ M.fnsC P bv wv off (start + M.lenF P bv wv F) Fs))
      (M.offs P bv wv (start + M.lenF P bv wv F) Fs f)
      (M.codeC (M.fnC P bv wv off (M.offs P bv wv (start + M.lenF P bv wv F) Fs f) Fs[f]))
    rw [codeC_append, ← List.append_assoc]; exact this

/-- the word where the stub's call statement begins -/
def posS : Nat := (M.encX (.enter 0)).length + (M.encC (.enterC 0)).length

def lenStub (res main : Nat) : Nat :=
  M.posS + M.lenC P bv wv (.call res main []) +
    ((M.encC (.leaveC 0)).length + ((M.encX .leave).length + (M.enc .ret).length))

/-- the entry stub: `res := main()` in a frame without slots -/
def stubC (off : Nat → Nat) (res main : Nat) : List YOp :=
  [.x (.f (.enter 0))] ++ [.c (.enterC 0)] ++ M.compC P bv wv off M.posS (.call res main []) ++
    [.c (.leaveC 0)] ++ [.x (.f .leave)] ++ [.x (.a .ret)]

theorem len_stubC (off : Nat → Nat) (res main : Nat) :
    (M.codeC (M.stubC P bv wv off res main)).length = M.lenStub P bv wv res main := by
  simp only [stubC, lenStub, posS, codeC_append, codeC_one, encY, MachineF.encF, List.length_append, len_compC]
  omega

/-- the word where function `f` of the program begins -/
def progOff (res main : Nat) : Nat → Nat := M.offs P bv wv (M.lenStub P bv wv res main) P

/-- **the compiler**: a program with calls to abstract operations; entry = word 0 -/
def compP (res main : Nat) : List YOp :=
  M.stubC P bv wv (M.progOff P bv wv res main) res main ++
    M.fnsC P bv wv (M.progOff P bv wv res main) (M.lenStub P bv wv res main) P

/-- the layout of a run: `n` words of code at `cb`, byte blocks `R`, word blocks `Wr`, stack area
`[lo, top)`; all in RAM and pairwise disjoint -/
structure PLay (cb : BitVec 64) (n : Nat) (R Wr : List Region) (lo top : Nat) : Prop where
  ram : ∀ r ∈ R, M.inRAM r.base r.len
  wram : ∀ r ∈ Wr, M.inRAM r.base r.len
  rp : R.Pairwise disjoint
  wp : Wr.Pairwise disjoint
  rw : ∀ r ∈ R, ∀ w ∈ Wr, disjoint r w
  wal : ∀ w ∈ Wr, w.base % 8 = 0
  stk : M.inRAM lo (top - lo)
  sR : ∀ r ∈ R ++ Wr, disjoint ⟨lo, top - lo⟩ r
  cd : ∀ r ∈ R ++ Wr ++ [⟨lo, top - lo⟩], disjoint ⟨cb.toNat, 4 * n⟩ r
  /-- byte blocks may be stored to (`Base.writable`) -/
  wr : ∀ r ∈ R, ∀ a, r.base ≤ a → a < r.base + r.len → ∀ s, M.ok s → M.writable s a
  /-- word blocks and the stack area may be stored to -/
  wwr : ∀ r ∈ Wr, ∀ a, r.base ≤ a → a < r.base + r.len → ∀ s, M.ok s → M.writable s a
  stw : ∀ a, lo ≤ a → a < top → ∀ s, M.ok s → M.writable s a

variable {P bv wv}

/-- **Programs with calls: compiler correctness from the `MachineC` laws.**  If the source run
`res := main()` from `σ` to `σ'` needs `k` bytes of stack (`CExec P k`), and the stack area `[lo, top)`
below the stack pointer has room for it (`lo + k + 8 ≤ frameAt s 0`, where `top = frameAt s 0 + 8`: 16 bytes
for the stub's two cells), then the code of the program, entered at word 0 with the globals of `σ` in the
variable registers and the blocks of `σ` in memory, returns to the caller's return address with the
globals and blocks of `σ'`; it writes only the blocks and the stack area and keeps the full frame
(`keep`: frame register and link register restored). -/
theorem compP_ok {res main : Nat} {R Wr : List Region} {lo k : Nat} {σ σ' : BState} {s : M.S} {cb : BitVec 64}
    (hex : CExec P k (.call res main []) σ σ') (hA : M.At s cb (M.codeC (M.compP P bv wv res main)))
    (hwf : ∀ f (hf : f < P.length),
      M.wfF P bv wv (M.progOff P bv wv res main) (M.progOff P bv wv res main f) P[f])
    (hwfS : M.wfC P bv wv (M.progOff P bv wv res main) 0 M.posS (.call res main []))
    (hbv : ∀ x ∈ bv, x < 8) (hwv : ∀ x ∈ wv, x < 8) (hen : M.enterOK s 0) (hk : lo + k + 8 ≤ M.frameAt s 0)
    (hL : M.PLay cb (M.codeC (M.compP P bv wv res main)).length R Wr lo (M.frameAt s 0 + 8))
    (hreg : ∀ i : Fin 8, M.get s (avar i) = σ.env i.val) (hheap : M.HeapB bv wv R Wr σ s)
    (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ (∀ i : Fin 8, M.get s' (avar i) = σ'.env i.val) ∧
      M.HeapB bv wv R Wr σ' s' ∧ Out (R ++ Wr ++ [⟨lo, M.frameAt s 0 + 8 - lo⟩]) (M.mem s) (M.mem s') ∧
      M.ok s' ∧ M.keep s s' := by
  obtain ⟨hns, hram0, hal0, -⟩ := M.enterOK_frame hen
  have hsubS : Sub (M.codeC (M.compP P bv wv res main)) 0
      (M.codeC (M.stubC P bv wv (M.progOff P bv wv res main) res main)) :=
    ⟨[], M.codeC (M.fnsC P bv wv (M.progOff P bv wv res main) (M.lenStub P bv wv res main) P), by
      unfold compP; rw [codeC_append]; rfl, rfl⟩
  have hfns : ∀ f (hf : f < P.length), Sub (M.codeC (M.compP P bv wv res main)) (M.progOff P bv wv res main f)
      (M.codeC (M.fnC P bv wv (M.progOff P bv wv res main) (M.progOff P bv wv res main f) P[f])) := fun f hf => by
    unfold compP; rw [codeC_append]
    exact M.fns_sub P bv wv _ P _ _ (M.len_stubC P bv wv _ res main) f hf
  generalize M.codeC (M.compP P bv wv res main) = W at hA hL hsubS hfns
  generalize M.progOff P bv wv res main = off at hwf hwfS hsubS hfns
  generalize hfp : M.frameAt s 0 = fp₀ at *
  unfold Base.inRAM at hram0
  have hstk := hL.stk
  unfold Base.inRAM at hstk
  have hlt := M.ramHi_lt
  simp only [stubC, codeC_append, codeC_one, encY, MachineF.encF] at hsubS
  obtain ⟨q5, qret⟩ := hsubS.split
  obtain ⟨q4, qlv⟩ := q5.split
  obtain ⟨q3, qlc⟩ := q4.split
  obtain ⟨q2, qcall⟩ := q3.split
  obtain ⟨qen, qec⟩ := q2.split
  simp only [List.length_append, len_compC] at qret qlv qlc qcall
  have hc := hA.code
  have hok := hA.codeOK
  have hpc0 : M.pcIs s (next cb 0) := by rw [next_zero]; exact hA.hpc
  have hcd := hL.cd
  have hcdS := hcd _ memLast
  unfold disjoint at hcdS; dsimp only at hcdS
  -- 1. enter
  refine M.runsTo_trans (M.law_enter hen (M.at_sub hok hc qen hA.ok hpc0) (by
    rw [hfp, next_zero]; have := qen.le; unfold disjoint; dsimp only; omega))
    fun s₁ ⟨ok₁, kf₁, pc₁, fr₁, rg₁, o₁, sv₁, z₁⟩ => ?_
  rw [hfp] at fr₁ o₁ sv₁
  rw [next_add] at pc₁
  have oS₁ : Out [⟨lo, fp₀ + 8 - lo⟩] (M.mem s) (M.mem s₁) := out1 o₁ (by omega) (by omega)
  have hfr₁ : (M.fr s₁).toNat = fp₀ := by rw [fr₁, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hc₁ := M.codeAt_out hc hok hcd (out_stk (R := R) (Wr := Wr) oS₁ (Nat.le_refl _) (by omega))
  -- 2. save the return address
  refine M.runsTo_trans (M.law_enterC (n := 0) (Nat.zero_le _)
    (M.at_sub hok hc₁ qec ok₁ (M.pcIs_cast pc₁ (by omega))) (by rw [hfr₁]; omega)
    (by rw [hfr₁]; unfold Base.inRAM; omega) (by rw [hfr₁]; exact hal0)
    (fun i hi => by rw [hfr₁]; exact hL.stw _ (by omega) (by omega) _ ok₁))
    fun s₂ ⟨ok₂, kc₂, pc₂, fr₂, st₂, m₂⟩ => ?_
  rw [hfr₁] at fr₂ m₂
  rw [next_add] at pc₂
  have o₂ : Out [⟨fp₀ - 8 * (0 + 1), 8⟩] (M.mem s₁) (M.mem s₂) := by
    rw [m₂]; exact Out.wr (List.mem_singleton_self _) (Nat.le_refl _) (by rw [length_le8]; exact Nat.le_refl _)
  have oS₂ : Out [⟨lo, fp₀ + 8 - lo⟩] (M.mem s) (M.mem s₂) := oS₁.trans (out1 o₂ (by omega) (by omega))
  have oG₂ : Out (R ++ Wr ++ [⟨lo, fp₀ + 8 - lo⟩]) (M.mem s) (M.mem s₂) :=
    out_stk oS₂ (Nat.le_refl _) (by omega)
  have hc₂ := M.codeAt_out hc hok hcd oG₂
  have C : M.Ctx P bv wv off cb W R Wr lo fp₀ :=
    { codeOK := hok, fns := hfns, wf := hwf, bvlt := hbv, wvlt := hwv, ram := hL.ram, wram := hL.wram,
      rp := hL.rp, wp := hL.wp, rw := hL.rw, wal := hL.wal, wr := hL.wr, lohi := by omega,
      wwr := hL.wwr, stw := fun a h1 h2 => hL.stw a h1 (by omega),
      stk := by unfold Base.inRAM; omega,
      sR := fun r hr => by have := hL.sR r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega,
      cd := fun r hr => by
        rcases List.mem_append.1 hr with hr | hr
        · exact hcd r (List.mem_append_left _ hr)
        · rw [List.mem_singleton] at hr; subst hr; unfold disjoint; dsimp only; omega }
  have hF : M.Frm 0 (fp₀ - 8 * (0 + 1)) := ⟨by unfold Base.inRAM; omega, by omega, Nat.zero_le _,
    fun a h1 h2 => hL.stw a (by omega) (by omega)⟩
  have byR : ∀ r ∈ R ++ Wr, bytes (M.mem s₂) r.base r.len = bytes (M.mem s) r.base r.len := fun r hr =>
    bytes_out oS₂ fun r' hr' => by
      rw [List.mem_singleton] at hr'; subst hr'; exact disj_symm (hL.sR r hr)
  have hrel₂ : M.RelB 0 (fp₀ - 8 * (0 + 1)) bv wv R Wr σ s₂ :=
    ⟨⟨fun i => by rw [st₂, rg₁ _ (avar_ge i), hreg], fr₂, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
      hheap.hlen, hheap.bvlen, hheap.base, hheap.blen,
      fun b hb => by rw [byR _ (List.mem_append_left _ (List.getElem_mem hb))]; exact hheap.rbytes b hb,
      hheap.whlen, hheap.wvlen, hheap.wbase, hheap.wblen,
      fun b hb => by rw [byR _ (List.mem_append_right _ (List.getElem_mem hb))]; exact hheap.wbyts b hb⟩
  -- 3. the call of `main`
  refine M.runsTo_trans (M.execC_ok C hex hwfS (qcall.cast (by unfold posS; omega)) hF (by omega) (by omega) hc₂ ok₂
    (M.pcIs_cast pc₂ (by unfold posS; omega)) hrel₂) fun s₃ ⟨ok₃, kc₃, pc₃, o₃, r₃⟩ => ?_
  have oG₃ : Out (R ++ Wr ++ [⟨lo, fp₀ + 8 - lo⟩]) (M.mem s₂) (M.mem s₃) := wrt_G o₃ (by omega) (by omega)
  have hc₃ := M.codeAt_out hc₂ hok hcd oG₃
  -- 4. restore the return address
  have hfr₃ : (M.fr s₃).toNat = fp₀ - 8 * (0 + 1) := MachineF.Frm.fr M.toMachineF hF r₃.env.fr
  have hsv₃ : bytes (M.mem s₃) (fp₀ - 8 * (0 + 1)) 8 = (le8 (M.ra s₁)).map some := by
    rw [bytes_out o₃ (M.cell0 C (by omega) (by omega)), m₂]
    have := bytes_wr_self (m := M.mem s₁) (a := fp₀ - 8 * (0 + 1)) (l := le8 (M.ra s₁))
    rw [length_le8] at this; exact this
  refine M.runsTo_trans (M.law_leaveC (n := 0) (w := M.ra s₁) (Nat.zero_le _)
    (M.at_sub hok hc₃ qlc ok₃ (M.pcIs_cast pc₃ (by unfold posS; omega))) (by rw [hfr₃]; exact hF.ram)
    (by rw [hfr₃]; exact hF.al) (by rw [hfr₃]; exact hsv₃))
    fun s₄ ⟨ok₄, kc₄, pc₄, ra₄, fr₄, st₄, m₄⟩ => ?_
  rw [hfr₃, Nat.sub_add_cancel (by omega)] at fr₄
  rw [next_add] at pc₄
  -- 5. restore the frame register
  have hfr₄ : (M.fr s₄).toNat = fp₀ := by rw [fr₄, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hsv₄ : bytes (M.mem s₄) fp₀ 8 = (le8 (M.fr s)).map some := by
    rw [m₄, bytes_out o₃ (fun r hr => by
      unfold Wrt AllR at hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with ((hr | hr) | hr) | hr
      · have := hL.sR r (List.mem_append_left _ hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega
      · have := hL.sR r (List.mem_append_right _ hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega
      · obtain ⟨j, hj, -⟩ := mem_slots hr; exact absurd hj (Nat.not_lt_zero _)
      · subst hr; unfold disjoint; dsimp only; omega),
      bytes_out o₂ (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; unfold disjoint; dsimp only; omega)]
    exact sv₁
  refine M.runsTo_trans (M.law_leave (w := M.fr s)
    (M.at_sub hok (M.codeAt_mem m₄ hc₃) qlv ok₄ (M.pcIs_cast pc₄ (by omega)))
    (by rw [hfr₄]; unfold Base.inRAM; omega) (by rw [hfr₄]; exact hal0) (by rw [hfr₄]; exact hsv₄))
    fun s₅ ⟨ok₅, kf₅, pc₅, fr₅, st₅, m₅⟩ => ?_
  rw [next_add] at pc₅
  -- 6. return
  have era : M.ra s₅ = M.ra s := by rw [M.keepF_ra kf₅, ra₄, M.keepF_ra kf₁]
  refine M.runsTo_mono (M.law_ret (by rw [era]; exact hra)
    (M.at_sub hok (M.codeAt_mem m₅ (M.codeAt_mem m₄ hc₃)) qret ok₅ (M.pcIs_cast pc₅ (by omega))))
    fun s₆ ⟨d₆, st₆, m₆⟩ => ?_
  have m₆₃ : M.mem s₆ = M.mem s₃ := by rw [m₆, m₅, m₄]
  refine ⟨by rw [← era]; exact d₆.hpc, fun i => by rw [st₆, st₅, st₄, r₃.env.reg],
    ⟨r₃.hlen, r₃.bvlen, r₃.base, r₃.blen, fun b hb => by rw [m₆₃]; exact r₃.rbytes b hb, r₃.whlen, r₃.wvlen,
      r₃.wbase, r₃.wblen, fun b hb => by rw [m₆₃]; exact r₃.wbyts b hb⟩,
    by rw [m₆₃]; exact oG₂.trans oG₃, d₆.ok, ?_⟩
  have kc : M.keepC s s₆ := M.keepC_trans (M.keepC_of_keepF kf₁) (M.keepC_trans kc₂ (M.keepC_trans kc₃
    (M.keepC_trans kc₄ (M.keepC_trans (M.keepC_of_keepF kf₅) (M.kC d₆)))))
  exact M.keep_of_keepF (M.keepF_of_keepC kc (by rw [M.keep_ra d₆.keep, era])) (by rw [M.keep_fr d₆.keep, fr₅])

end MachineC
end Proven.Mach
