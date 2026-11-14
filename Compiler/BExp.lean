/- Middle layer, expressions with spill slots: `BExp` (variables `0 .. 7` in registers, `8 ..` in frame
slots) to extended abstract operations, and its correctness from the `MachineF` laws only. -/
import Compiler.Frame
import Compiler.BLang

namespace Proven.Mach

/-- abstract code leaving the value of `e` in `r_k` (a slot variable is one `ldS`) -/
def mgenB : BExp → Nat → List XOp
  | .var i, k => if h : i < 8 then [.a (.mov (rk k) (avar ⟨i, h⟩))] else [.f (.ldS (rk k) (i - 8))]
  | .const c, k => [.a (.li (rk k) c)]
  | .bin op a b, k => mgenB a k ++ mgenB b (k + 1) ++ [.a (.bin op (rk k) (rk k) (rk (k + 1)))]
  | .ite c a b, k => mgenB c k ++ mgenB a (k + 1) ++ mgenB b (k + 2) ++
      [.a (.sel (rk k) (rk k) (rk (k + 1)) (rk (k + 2)))]

namespace MachineF
variable (M : MachineF)

/-- an open frame of `N` slots at `fp` -/
structure Frm (N fp : Nat) : Prop where
  ram : M.inRAM fp (8 * (N + 1))
  al : fp % 8 = 0
  ns : N ≤ M.maxSlots

/-- `s` holds `env`: variable `i < 8` in `avar i`, frame register `= fp`, variable `8 + j` in slot `j` -/
structure EnvB (N fp : Nat) (env : BEnv) (s : M.S) : Prop where
  reg : ∀ i : Fin 8, M.get s (avar i) = env i.val
  fr : M.fr s = BitVec.ofNat 64 fp
  slot : ∀ j, j < N → bytes (M.mem s) (fp + 8 * (j + 1)) 8 = (le8 (env (8 + j))).map some

theorem Frm.fr {N fp : Nat} {s : M.S} (hF : M.Frm N fp) (h : M.fr s = BitVec.ofNat 64 fp) :
    (M.fr s).toNat = fp := by
  have := M.ramHi_lt; have := hF.ram
  rw [h, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
  unfold Base.inRAM at this; omega

/-- slot `j` is addressable -/
theorem Frm.slot {N fp : Nat} (hF : M.Frm N fp) {j : Nat} (hj : j < N) :
    M.inRAM (fp + 8 * (j + 1)) 8 ∧ (fp + 8 * (j + 1)) % 8 = 0 ∧ j < M.maxSlots := by
  have h1 := hF.ram; have h2 := hF.al; have h3 := hF.ns
  unfold Base.inRAM at h1 ⊢; omega

theorem EnvB.of {N fp env} {s s' : M.S} (r : M.EnvB N fp env s) (hm : M.mem s' = M.mem s)
    (hk : M.keep s s') (he : ∀ i : Fin 8, M.get s' (avar i) = M.get s (avar i)) : M.EnvB N fp env s' :=
  ⟨fun i => by rw [he, r.reg], by rw [M.keep_fr hk, r.fr], fun j hj => by rw [hm]; exact r.slot j hj⟩

theorem genB_ok {N fp : Nat} (hF : M.Frm N fp) (env : BEnv) :
    ∀ (e : BExp) (k : Nat), k + e.depth < 7 → e.vlt (8 + N) → ∀ {s : M.S} {pc : BitVec 64},
    M.At s pc (M.codeF (mgenB e k)) → M.EnvB N fp env s →
    M.runsTo s fun s' => M.Done s s' (next pc (M.codeF (mgenB e k)).length) ∧
      M.EPost 7 k (e.denote env) s s'
  | .var i, k, hk, hv, s, pc, hA, henv => by
    simp only [mgenB, BExp.depth, BExp.vlt, BExp.denote] at hk hv hA ⊢
    have hrk := rk_val (k := k) (by omega)
    by_cases hi : i < 8
    · rw [dite_pos' hi] at hA ⊢
      rw [codeF_one] at hA ⊢
      have h1 := avar_ge ⟨i, hi⟩
      have hmov : MovOK (rk k) (avar ⟨i, hi⟩) := by unfold MovOK; rw [hrk]; omega
      refine M.runsTo_mono (M.law_mov hmov hA) fun s' ⟨d, st, m⟩ => ⟨d, m, ?_, fun r hr => Core.Set1.other _ st ?_⟩
      · rw [Core.Set1.same _ st, henv.reg ⟨i, hi⟩]
      · intro e; subst e; rw [hrk] at hr; omega
    · rw [dite_neg' hi] at hA ⊢
      rw [codeF_one] at hA ⊢
      have hj : i - 8 < N := by omega
      obtain ⟨hr, hal, hjm⟩ := Frm.slot M hF hj
      have hfr := Frm.fr M hF henv.fr
      have hb := henv.slot (i - 8) hj
      rw [show 8 + (i - 8) = i by omega] at hb
      refine M.runsTo_mono (M.law_ldS (d := rk k) (v := env i) (by rw [hrk]; omega) hjm hA
        (by rw [hfr]; exact hr) (by rw [hfr]; exact hal) (by rw [hfr]; exact hb))
        fun s' ⟨d, st, m⟩ => ⟨d, m, Core.Set1.same _ st, fun r hr => Core.Set1.other _ st ?_⟩
      intro e; subst e; rw [hrk] at hr; omega
  | .const c, k, hk, hv, s, pc, hA, henv => by
    simp only [mgenB, BExp.depth, BExp.denote, codeF_one] at hk hA ⊢
    have hrk := rk_val (k := k) (by omega)
    refine M.runsTo_mono (M.law_li (by rw [hrk]; omega) hA) fun s' ⟨d, st, m⟩ =>
      ⟨d, m, (Core.Set1.same _ st), fun r hr => Core.Set1.other _ st ?_⟩
    intro e; subst e; rw [hrk] at hr; omega
  | .bin op a b, k, hk, hv, s, pc, hA, henv => by
    simp only [mgenB, BExp.depth, BExp.vlt, BExp.denote, codeF_append, codeF_one, List.length_append]
      at hk hv hA ⊢
    have hka : k + a.depth < 7 := by omega
    have hkb : k + 1 + b.depth < 7 := by omega
    have hrk := rk_val (k := k) (by omega)
    have hrk1 := rk_val (k := k + 1) (by omega)
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    rw [← next_add, ← next_add]
    refine M.seq_run (genB_ok hF env a k hka hv.1 hA1 henv) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    have henv₁ : M.EnvB N fp env s₁ := EnvB.of M henv m₁ d₁.keep fun i => k₁ _ (.inr (avar_ge i))
    refine M.seq_run (genB_ok hF env b (k + 1) hkb hv.2 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) henv₁)
      fun s₂ d₂ ⟨m₂, v₂, k₂⟩ => ?_
    have hc3' := M.codeAt_mem (m₂.trans m₁) hc3
    refine M.runsTo_mono (M.law_bin (op := op) (by rw [hrk]; omega) rfl (by rw [hrk, hrk1])
      (Core.Done.at _ d₂ hc3' ho3)) fun s₃ ⟨d₃, st, m₃⟩ => ⟨d₃, by rw [m₃, m₂, m₁], ?_, fun r hr => ?_⟩
    · rw [(Core.Set1.same _ st), k₂ _ (.inl (by rw [hrk]; omega)), v₁, v₂]
    · rw [Core.Set1.other _ st (fun e => by subst e; rw [hrk] at hr; omega), k₂ _ (by omega), k₁ _ hr]
  | .ite c a b, k, hk, hv, s, pc, hA, henv => by
    simp only [mgenB, BExp.depth, BExp.vlt, BExp.denote, codeF_append, codeF_one, List.length_append]
      at hk hv hA ⊢
    have hrk := rk_val (k := k) (by omega)
    have hrk1 := rk_val (k := k + 1) (by omega)
    have hrk2 := rk_val (k := k + 2) (by omega)
    obtain ⟨hA123, hc4, ho4⟩ := Core.At.split _ hA
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA123
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    rw [List.length_append, List.length_append, ← next_add, ← next_add] at hc4 ho4
    rw [← next_add, ← next_add, ← next_add]
    refine M.seq_run (genB_ok hF env c k (by omega) hv.1 hA1 henv) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    have henv₁ : M.EnvB N fp env s₁ := EnvB.of M henv m₁ d₁.keep fun i => k₁ _ (.inr (avar_ge i))
    refine M.seq_run (genB_ok hF env a (k + 1) (by omega) hv.2.1 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2)
      henv₁) fun s₂ d₂ ⟨m₂, v₂, k₂⟩ => ?_
    have henv₂ : M.EnvB N fp env s₂ := EnvB.of M henv₁ m₂ d₂.keep fun i => k₂ _ (.inr (avar_ge i))
    have hc3' := M.codeAt_mem (m₂.trans m₁) hc3
    refine M.seq_run (genB_ok hF env b (k + 2) (by omega) hv.2.2 (Core.Done.at _ d₂ hc3' ho3) henv₂)
      fun s₃ d₃ ⟨m₃, v₃, k₃⟩ => ?_
    have hc4' := M.codeAt_mem (m₃.trans (m₂.trans m₁)) hc4
    refine M.runsTo_mono (M.law_sel (by rw [hrk]; omega) rfl (by rw [hrk, hrk1]) (by rw [hrk, hrk2])
      (Core.Done.at _ d₃ hc4' ho4)) fun s₄ ⟨d₄, vs, ks, m₄⟩ => ⟨d₄, by rw [m₄, m₃, m₂, m₁], ?_, fun r hr => ?_⟩
    · have ec : M.get s₃ (rk k) = c.denote env := by
        rw [k₃ _ (.inl (by rw [hrk]; omega)), k₂ _ (.inl (by rw [hrk]; omega)), v₁]
      have ea : M.get s₃ (rk (k + 1)) = a.denote env := by rw [k₃ _ (.inl (by rw [hrk1]; omega)), v₂]
      rw [vs, ec, ea, v₃]
    · rw [ks r (fun e => by subst e; rw [hrk] at hr; omega) (fun e => by subst e; rw [hrk1] at hr; omega),
        k₃ _ (by omega), k₂ _ (by omega), k₁ _ hr]

end MachineF
end Proven.Mach
