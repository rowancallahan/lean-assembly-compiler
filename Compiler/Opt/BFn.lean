/- The optimising spill-slot compiler (`BStmt`, byte blocks) over a `WideF` target (wide operations plus
`enter`/`leave` of a frame, as in `MachineF`), and its correctness `optB_ok`.

Code: `enter N; [locals in registers := 0]; body; leave; ret`.  Variables `0 .. 7` are in `avar i`; where a
variable `8 + j` lives (a register `g (8 + j)` or, if `sp j`, slot `j`) and where the temporaries go (`g`) is
the caller's untrusted choice, checked by `Wide.body` (`injOn`, `wf`). -/
import Compiler.Opt.Fn
import Compiler.Opt.BSel

namespace Proven.Mach
open IR Sel

/-- wide operations plus a frame (`enter`/`leave` as in `MachineF`) -/
structure WideF extends Wide where
  encE : Nat → List (BitVec 32)
  encL : List (BitVec 32)
  keepF : S → S → Prop
  frameAt : S → Nat → Nat
  enterOK : S → Nat → Prop
  keepF_of_keep : ∀ {s s' : S}, keep s s' → keepF s s'
  keepF_trans : ∀ {s₁ s₂ s₃ : S}, keepF s₁ s₂ → keepF s₂ s₃ → keepF s₁ s₃
  keep_of_keepF : ∀ {s s' : S}, keepF s s' → fr s' = fr s → keep s s'
  keepF_ra : ∀ {s s' : S}, keepF s s' → ra s' = ra s
  enterOK_frame : ∀ {s : S} {n : Nat}, enterOK s n →
    n ≤ maxSlots ∧ toBase.inRAM (frameAt s n) (8 * (n + 1)) ∧ frameAt s n % 8 = 0
  f_enter : ∀ {n : Nat} {s : S} {pc : BitVec 64}, enterOK s n → toBase.At s pc (encE n) →
    disjoint ⟨pc.toNat, 4 * (encE n).length⟩ ⟨frameAt s n, 8 * (n + 1)⟩ →
    runsTo s fun s' => ok s' ∧ keepF s s' ∧ pcIs s' (next pc (encE n).length) ∧
      fr s' = BitVec.ofNat 64 (frameAt s n) ∧ (∀ r : Reg, 7 ≤ r.val → get s' r = get s r) ∧
      Out [⟨frameAt s n, 8 * (n + 1)⟩] (mem s) (mem s') ∧
      bytes (mem s') (frameAt s n) 8 = (le8 (fr s)).map some ∧
      ∀ j, j < n → bytes (mem s') (frameAt s n + 8 * (j + 1)) 8 = (le8 0).map some
  f_leave : ∀ {s : S} {pc : BitVec 64} {w : BitVec 64}, toBase.At s pc encL →
    toBase.inRAM (fr s).toNat 8 → (fr s).toNat % 8 = 0 → bytes (mem s) (fr s).toNat 8 = (le8 w).map some →
    runsTo s fun s' => ok s' ∧ keepF s s' ∧ pcIs s' (next pc encL.length) ∧ fr s' = w ∧
      toBase.Same s s' ∧ mem s' = mem s

/-- `0` into the register-resident locals -/
def initL (sp : Nat → Bool) : List Nat → Code Nat
  | [] => .skip
  | j :: l => if sp j = true then initL sp l else .seq (.ins (.set (8 + j) (.i 0))) (initL sp l)

theorem initL_ok (sp : Nat → Bool) (ram : Nat → Prop) (fp : Nat) : ∀ (l : List Nat) (τ : St Nat),
    ∃ τ', Exec ram fp (initL sp l) τ τ' ∧ τ'.mem = τ.mem ∧ (∀ j, j ∈ l → sp j = false → τ'.reg (8 + j) = 0) ∧
      ∀ x, (∀ j, j ∈ l → x ≠ 8 + j) → τ'.reg x = τ.reg x
  | [], τ => ⟨τ, .skip, rfl, fun _ h => (nomatch h), fun _ _ => rfl⟩
  | j :: l, τ => by
    simp only [initL]
    by_cases hs : sp j = true
    · rw [if_pos hs]
      obtain ⟨τ', hx, hm, hz, hk⟩ := initL_ok sp ram fp l τ
      refine ⟨τ', hx, hm, fun i hi hsi => ?_, fun x hx' => hk x fun i hi => hx' i (List.mem_cons_of_mem _ hi)⟩
      rcases List.mem_cons.1 hi with e | hi'
      · rw [e, hs] at hsi; exact nomatch hsi
      · exact hz i hi' hsi
    · rw [if_neg hs]
      obtain ⟨τ', hx, hm, hz, hk⟩ := initL_ok sp ram fp l ⟨upd τ.reg (8 + j) 0, τ.mem⟩
      refine ⟨τ', .seq (.ins .set) hx, hm, fun i hi hsi => ?_, fun x hx' => ?_⟩
      · by_cases hil : i ∈ l
        · exact hz i hil hsi
        · have e : i = j := (List.mem_cons.1 hi).resolve_right hil
          subst e
          rw [hk (8 + i) fun k hk' e => hil (by have e' : i = k := (by omega); rw [e']; exact hk')]
          exact upd_same _ _ _
      · rw [hk x fun i hi => hx' i (List.mem_cons_of_mem _ hi)]
        exact upd_other _ _ (hx' j (List.mem_cons_self ..))

/-- the register assignment: variables `0 .. 7` by convention, the rest by `g` -/
def fB (g : Nat → Reg) (x : Nat) : Reg := if h : x < 8 then avar ⟨x, h⟩ else g x

/-- the blocks in machine memory -/
structure HeapI (M : Wide) (bv : List Nat) (R : List Region) (σ : BState) (s : M.S) : Prop where
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  rbytes : ∀ b (hb : b < R.length), bytes (M.mem s) R[b].base R[b].len = (σ.heap[b]?.getD []).map some

theorem Core.codeAt_out' (C : Core) {s s' : C.S} {pc ws} {A : List Region} (hc : C.codeAt s pc ws)
    (hok : C.codeOK pc ws.length) (hd : ∀ r ∈ A, disjoint ⟨pc.toNat, 4 * ws.length⟩ r)
    (hu : Out A (C.mem s) (C.mem s')) : C.codeAt s' pc ws := by
  intro i hi
  refine C.instrAt_frame (fun j hj => hu _ fun r hr => ?_) (hc i hi)
  have := hd r hr; have e := C.pc_toNat hok (a := i) (by omega)
  unfold disjoint at this; dsimp only at this
  show (next pc i).toNat + j < r.base ∨ r.base + r.len ≤ (next pc i).toNat + j
  rw [e]; omega

namespace WideF
variable (M : WideF) (sc : Reg) (g : Nat → Reg) (sp : Nat → Bool) (N : Nat)

/-- **The optimising spill-slot compiler** (byte blocks only) -/
def optB (bv : List Nat) (p : BStmt) : Option (List (BitVec 32)) :=
  if (okB N bv p && decide (N ≤ 16) && decide (∀ i : Fin 8, avar i ≠ sc)) = true then
    match M.body sc (fB g) [0, 1, 2, 3, 4, 5, 6, 7] (.seq (initL sp (List.range N)) (irB sp bv p)) with
    | some w => some (M.encE N ++ (w ++ (M.encL ++ M.wenc .ret)))
    | none => none
  else none

variable {M sc g sp N}

/-- **Correctness of the optimising spill-slot compiler** (the shape of `MachineF.compBF_ok`, byte blocks). -/
theorem optB_ok {bv : List Nat} {p : BStmt} {ws : List (BitVec 32)} (hc : M.optB sc g sp N bv p = some ws)
    {R : List Region} {σ σ' : BState} (hex : BExec p σ σ') {s : M.S} {pc : BitVec 64} (hA : M.At s pc ws)
    (hen : M.enterOK s N) (hRram : ∀ r ∈ R, M.inRAM r.base r.len) (hRp : R.Pairwise disjoint)
    (hRf : ∀ r ∈ R, disjoint ⟨M.frameAt s N, 8 * (N + 1)⟩ r)
    (hcd : ∀ r ∈ R ++ [⟨M.frameAt s N, 8 * (N + 1)⟩], disjoint ⟨pc.toNat, 4 * ws.length⟩ r)
    (hreg : ∀ i : Fin 8, M.get s (avar i) = σ.env i.val) (hslot : ∀ j, j < N → σ.env (8 + j) = 0)
    (hheap : HeapI M.toWide bv R σ s) (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ (∀ i : Fin 8, M.get s' (avar i) = σ'.env i.val) ∧
      HeapI M.toWide bv R σ' s' ∧ Out (R ++ [⟨M.frameAt s N, 8 * (N + 1)⟩]) (M.mem s) (M.mem s') ∧
      M.ok s' ∧ M.keep s s' := by
  unfold optB at hc
  have hchk : (okB N bv p && decide (N ≤ 16) && decide (∀ i : Fin 8, avar i ≠ sc)) = true :=
    Decidable.byContradiction fun h => by rw [if_neg h] at hc; exact nomatch hc
  rw [if_pos hchk] at hc
  obtain ⟨hokB, hN16, hsc⟩ := Wide.and3 hchk
  replace hN16 : N ≤ 16 := of_decide_eq_true hN16
  replace hsc : ∀ i : Fin 8, avar i ≠ sc := of_decide_eq_true hsc
  cases hb : M.body sc (fB g) [0, 1, 2, 3, 4, 5, 6, 7] (.seq (initL sp (List.range N)) (irB sp bv p)) with
  | none => rw [hb] at hc; exact nomatch hc
  | some w =>
  rw [hb] at hc
  cases hc
  obtain ⟨hns, hfram, hal⟩ := M.enterOK_frame hen
  have hlt := M.ramHi_lt
  have hfram' : M.ramLo ≤ M.frameAt s N ∧ M.frameAt s N + 8 * (N + 1) ≤ M.ramHi := hfram
  have hok := hA.codeOK
  simp only [List.length_append] at hok hcd
  obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
  have hFm : (⟨M.frameAt s N, 8 * (N + 1)⟩ : Region) ∈ R ++ [⟨M.frameAt s N, 8 * (N + 1)⟩] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have e1 := M.pc_toNat hok (a := (M.encE N).length) (by omega)
  have hcdF := hcd _ hFm
  refine M.runsTo_trans (M.f_enter hen hA1 (by unfold disjoint at hcdF ⊢; dsimp only at hcdF ⊢; omega))
    fun s₁ ⟨ok₁, kF₁, pc₁, fr₁, reg₁, out₁, cell₁, sl₁⟩ => ?_
  generalize hfp : M.frameAt s N = fp at *
  have frn : (M.fr s₁).toNat = fp := by
    rw [fr₁, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have L : LayI N fp R := ⟨hal, fun r hr => by
    have : M.ramLo ≤ r.base ∧ r.base + r.len ≤ M.ramHi := hRram r hr
    omega, hRp, hRf, hN16⟩
  -- writable addresses are in RAM, outside the code, outside cell 0
  have hramF : ∀ a, ramB N fp R a → (∃ r ∈ R, r.base ≤ a ∧ a < r.base + r.len) ∨
      (fp + 8 ≤ a ∧ a < fp + 8 * (N + 1)) := fun a ⟨r, hr, h1, h2⟩ => by
    rcases List.mem_append.1 hr with hr | hr
    · exact .inl ⟨r, hr, h1, h2⟩
    · obtain ⟨j, hj, rfl⟩ := mem_slots hr
      refine .inr ⟨by show fp + 8 ≤ a; have : fp + 8 * (j + 1) ≤ a := h1; omega, ?_⟩
      have : a < fp + 8 * (j + 1) + 8 := h2
      have : 8 * (j + 1) + 8 ≤ 8 * (N + 1) := by omega
      omega
  have hram : ∀ a, ramB N fp R a → M.inRAM a 1 := fun a ha => by
    rcases hramF a ha with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
    · have : M.ramLo ≤ r.base ∧ r.base + r.len ≤ M.ramHi := hRram r hr
      exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hnc : ∀ a, ramB N fp R a → ¬(pc.toNat ≤ a ∧ a < pc.toNat + 4 * ((M.encE N).length +
      (w.length + (M.encL.length + (M.wenc .ret).length)))) := fun a ha h' => by
    rcases hramF a ha with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
    · have := hcd r (List.mem_append_left _ hr); unfold disjoint at this; dsimp only at this; omega
    · unfold disjoint at hcdF; dsimp only at hcdF; omega
  have c2 : M.codeAt s₁ (next pc (M.encE N).length) (w ++ (M.encL ++ M.wenc .ret)) :=
    Core.codeAt_out' _ hc2 ho2 (A := [⟨fp, 8 * (N + 1)⟩]) (fun r hr => by
      rw [List.mem_singleton.1 hr]
      unfold disjoint at hcdF ⊢; dsimp only at hcdF ⊢
      simp only [List.length_append]; rw [e1]; omega) out₁
  have fg : M.Frag (ramB N fp R) fp s₁ (next pc (M.encE N).length) (w ++ (M.encL ++ M.wenc .ret)) :=
    ⟨c2, ho2, fun a ha h' => hnc a ha (by
      simp only [List.length_append] at h'; rw [e1] at h'; omega), frn⟩
  -- the IR run
  obtain ⟨τ₂, xi, mi, zi, ki⟩ := initL_ok sp (ramB N fp R) fp (List.range N)
    ⟨fun x => M.get s₁ (fB g x), M.mem s₁⟩
  have hdisjR : ∀ b (hb : b < R.length), ∀ r ∈ [(⟨fp, 8 * (N + 1)⟩ : Region)],
      disjoint ⟨R[b].base, R[b].len⟩ r := fun b hb r hr => by
    rw [List.mem_singleton.1 hr]
    have := hRf _ (List.getElem_mem hb); unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  have r₂ : RelBI sp N fp bv R σ τ₂ := by
    refine ⟨fun i hi hs => ?_, fun j hj hs => ?_, hheap.hlen, hheap.bvlen, hheap.base, hheap.blen, fun b hb => ?_⟩
    · by_cases h8 : i < 8
      · rw [ki i fun j _ => by omega]
        show M.get s₁ (fB g i) = _
        unfold fB; rw [dif_pos h8, reg₁ _ (avar_ge _)]; exact hreg ⟨i, h8⟩
      · have hsj : sp (i - 8) = false := by
          unfold isS at hs; rw [decide_eq_true (by omega : 8 ≤ i), Bool.true_and] at hs; exact hs
        have := zi (i - 8) (List.mem_range.2 (by omega)) hsj
        rw [show 8 + (i - 8) = i by omega] at this
        rw [this, ← hslot (i - 8) (by omega), show 8 + (i - 8) = i by omega]
    · rw [mi, hslot j hj]; exact sl₁ j hj
    · rw [mi]; show bytes (M.mem s₁) _ _ = _
      rw [MachineF.bytes_out out₁ (hdisjR b hb)]; exact hheap.rbytes b hb
  obtain ⟨τ₃, xb, r₃⟩ := irB_ok bv L hex hokB τ₂ r₂
  refine M.runsTo_trans (Wide.body_ok hram hb ok₁ pc₁ fg.left (.seq xi xb)) fun s₂ ⟨d₂, m₂, v₂, e₂⟩ => ?_
  -- leave
  have fr₂ : M.fr s₂ = M.fr s₁ := m₂.2
  have cell₂ : bytes (M.mem s₂) (M.fr s₂).toNat 8 = (le8 (M.fr s)).map some := by
    rw [fr₂, frn, ← cell₁]
    refine bytes_congr fun j hj => m₂.1 _ fun ha => ?_
    rcases hramF _ ha with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
    · have := hRf r hr; unfold disjoint at this; dsimp only at this; omega
    · omega
  have fg₂ := fg.right.mf m₂
  refine M.runsTo_trans (M.f_leave (w := M.fr s) (fg₂.left.at d₂.ok d₂.hpc)
    (by rw [fr₂, frn]; exact ⟨by omega, by omega⟩) (by rw [fr₂, frn]; exact hal) cell₂)
    fun s₃ ⟨ok₃, kF₃, pc₃, fr₃, same₃, m₃⟩ => ?_
  -- ret
  have ra₃ : M.ra s₃ = M.ra s := by
    rw [M.keepF_ra kF₃, M.keep_ra d₂.keep, M.keepF_ra kF₁]
  have atR : M.At s₃ (next (next (next pc (M.encE N).length) w.length) M.encL.length) (M.wenc .ret) :=
    ⟨ok₃, pc₃, M.codeAt_mem m₃ fg₂.right.code, fg₂.right.ok⟩
  refine M.runsTo_mono (M.w_ret (by rw [ra₃]; exact hra) atR) fun s₄ ⟨d₄, same₄, m₄⟩ => ?_
  have hkeep : M.keep s s₄ := M.keep_of_keepF
    (M.keepF_trans kF₁ (M.keepF_trans (M.keepF_of_keep d₂.keep) (M.keepF_trans kF₃ (M.keepF_of_keep d₄.keep))))
    (by rw [M.keep_fr d₄.keep, fr₃])
  have hmem : M.mem s₄ = τ₃.mem := by rw [m₄, m₃, e₂]
  refine ⟨ra₃ ▸ d₄.hpc, fun i => ?_, ⟨r₃.hlen, r₃.bvlen, r₃.base, r₃.blen, fun b hb => by
    rw [hmem]; exact r₃.rbytes b hb⟩, fun a ha => ?_, d₄.ok, hkeep⟩
  · rw [same₄, same₃]
    have := v₂ i.val (by revert i; decide) (by unfold fB; rw [dif_pos i.2]; exact hsc i)
    unfold fB at this; rw [dif_pos i.2] at this
    rw [this]
    exact r₃.reg i.val (by omega) (by unfold isS; rw [decide_eq_false (by omega : ¬8 ≤ i.val)]; rfl)
  · rw [m₄, m₃]
    have hfa := ha _ hFm
    have hnr : ¬ramB N fp R a := fun hr => by
      rcases hramF a hr with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩
      · have := ha r (List.mem_append_left _ hr); omega
      · dsimp only at hfa; omega
    rw [m₂.1 a hnr]
    exact out₁ a fun r hr => by rw [List.mem_singleton.1 hr]; exact hfa

end WideF
end Proven.Mach
