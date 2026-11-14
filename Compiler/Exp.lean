/- Middle layer, expressions: `AExp` (`Proven/ArrCode.lean`, 8 variables) and `Exp` (`Proven/Code.lean`, 4
variables) to abstract operations, and the correctness theorems, proved from the interface laws only.

`mgen8 e k` leaves the value of `e` in `r_k`, using `r_k ..` as a stack of temporaries (no spilling);
`Exp` is compiled through the embedding `toA` with the 11 temporaries `r0 .. r10`; the array compiler
uses `r0 .. r6` (its variables `v4 .. v7` live in `r7 .. r10`). -/
import Compiler.Logic
import Spec.ArrCode

namespace Proven.Mach

/-- temporary `k` (`k < 15`) -/
def rk (k : Nat) : Reg := if h : k < 15 then ⟨k, h⟩ else ⟨0, by decide⟩

theorem rk_val {k : Nat} (h : k < 15) : (rk k).val = k := by
  unfold rk; rw [dite_pos' h]

/-- variable `v_i`: `v0 .. v3` in `r11 .. r14`, `v4 .. v7` in `r7 .. r10` -/
def avar (i : Fin 8) : Reg := if h : i.val < 4 then ⟨11 + i.val, by omega⟩ else ⟨3 + i.val, by omega⟩

theorem avar_ge (i : Fin 8) : 7 ≤ (avar i).val := by revert i; decide
theorem avar_inj {i j : Fin 8} (h : avar i = avar j) : i = j := by revert i j; decide

/-- the `Exp` variable `v_i` (`i < 4`): `r(11 + i)` -/
def v4 (i : Fin 4) : Reg := avar ⟨i.val, by omega⟩

theorem v4_val (i : Fin 4) : (v4 i).val = 11 + i.val := by
  unfold v4 avar; rw [dite_pos' i.2]

/-- every variable of `e` lives at or above `r_K` -/
def varsOK (K : Nat) : AExp → Prop
  | .var i => K ≤ (avar i).val
  | .const _ => True
  | .bin _ a b => varsOK K a ∧ varsOK K b
  | .ite c a b => varsOK K c ∧ varsOK K a ∧ varsOK K b

/-- abstract code leaving the value of `e` in `r_k` -/
def mgen8 : AExp → Nat → List AOp
  | .var i, k => [.mov (rk k) (avar i)]
  | .const c, k => [.li (rk k) c]
  | .bin op a b, k => mgen8 a k ++ mgen8 b (k + 1) ++ [.bin op (rk k) (rk k) (rk (k + 1))]
  | .ite c a b, k => mgen8 c k ++ mgen8 a (k + 1) ++ mgen8 b (k + 2) ++ [.sel (rk k) (rk k) (rk (k + 1)) (rk (k + 2))]

namespace Machine
variable (M : Machine)

/-- the target words of an abstract program -/
def code : List AOp → List (BitVec 32)
  | [] => []
  | o :: os => M.enc o ++ code os

theorem code_append : ∀ (a b : List AOp), M.code (a ++ b) = M.code a ++ M.code b
  | [], _ => rfl
  | o :: os, b => by
    show M.enc o ++ M.code (os ++ b) = (M.enc o ++ M.code os) ++ M.code b
    rw [code_append os b, List.append_assoc]

theorem code_one (o : AOp) : M.code [o] = M.enc o := List.append_nil _

/-- the effect of an expression fragment: memory unchanged, `r_k` holds `v`, `r_j` kept for `j < k` and
`j ≥ K` -/
def EPost (K k : Nat) (v : BitVec 64) (s s' : M.S) : Prop :=
  M.mem s' = M.mem s ∧ M.get s' (rk k) = v ∧ ∀ r : Reg, (r.val < k ∨ K ≤ r.val) → M.get s' r = M.get s r

theorem gen_ok (K : Nat) (hK : K = 7 ∨ K = 11) (env : AEnv) :
    ∀ (e : AExp) (k : Nat), k + e.depth < K → varsOK K e → ∀ {s : M.S} {pc : BitVec 64},
    M.At s pc (M.code (mgen8 e k)) → (∀ i, K ≤ (avar i).val → M.get s (avar i) = env i) →
    M.runsTo s fun s' => M.Done s s' (next pc (M.code (mgen8 e k)).length) ∧ M.EPost K k (e.denote env) s s'
  | .var i, k, hk, hv, s, pc, hA, henv => by
    simp only [mgen8, AExp.depth, varsOK, AExp.denote, code_one] at hk hv hA ⊢
    have h1 := avar_ge i
    have hrk := rk_val (k := k) (by omega)
    have hmov : MovOK (rk k) (avar i) := by
      unfold MovOK; rw [hrk]; rcases hK with rfl | rfl <;> omega
    refine M.runsTo_mono (M.law_mov hmov hA) fun s' ⟨d, st, m⟩ => ⟨d, m, ?_, fun r hr => Core.Set1.other _ st ?_⟩
    · rw [(Core.Set1.same _ st), henv i hv]
    · intro e; subst e; rw [hrk] at hr; omega
  | .const c, k, hk, hv, s, pc, hA, henv => by
    simp only [mgen8, AExp.depth, AExp.denote, code_one] at hk hA ⊢
    have hrk := rk_val (k := k) (by omega)
    refine M.runsTo_mono (M.law_li (by rw [hrk]; omega) hA) fun s' ⟨d, st, m⟩ =>
      ⟨d, m, (Core.Set1.same _ st), fun r hr => Core.Set1.other _ st ?_⟩
    intro e; subst e; rw [hrk] at hr; omega
  | .bin op a b, k, hk, hv, s, pc, hA, henv => by
    simp only [mgen8, AExp.depth, varsOK, AExp.denote, code_append, code_one, List.length_append]
      at hk hv hA ⊢
    have hka : k + a.depth < K := by omega
    have hkb : k + 1 + b.depth < K := by omega
    have hrk := rk_val (k := k) (by omega)
    have hrk1 := rk_val (k := k + 1) (by omega)
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    rw [List.length_append, ← next_add] at hc3 ho3
    rw [← next_add, ← next_add]
    refine M.seq_run (gen_ok K hK env a k hka hv.1 hA1 henv) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    have henv₁ : ∀ i, K ≤ (avar i).val → M.get s₁ (avar i) = env i := fun i hi => by
      rw [k₁ _ (.inr hi), henv i hi]
    refine M.seq_run (gen_ok K hK env b (k + 1) hkb hv.2 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) henv₁)
      fun s₂ d₂ ⟨m₂, v₂, k₂⟩ => ?_
    have hc3' := M.codeAt_mem (m₂.trans m₁) hc3
    refine M.runsTo_mono (M.law_bin (op := op) (by rw [hrk]; omega) rfl (by rw [hrk, hrk1])
      (Core.Done.at _ d₂ hc3' ho3)) fun s₃ ⟨d₃, st, m₃⟩ => ⟨d₃, by rw [m₃, m₂, m₁], ?_, fun r hr => ?_⟩
    · rw [(Core.Set1.same _ st), k₂ _ (.inl (by rw [hrk]; omega)), v₁, v₂]
    · rw [Core.Set1.other _ st (fun e => by subst e; rw [hrk] at hr; omega), k₂ _ (by omega), k₁ _ hr]
  | .ite c a b, k, hk, hv, s, pc, hA, henv => by
    simp only [mgen8, AExp.depth, varsOK, AExp.denote, code_append, code_one, List.length_append]
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
    refine M.seq_run (gen_ok K hK env c k (by omega) hv.1 hA1 henv) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    have henv₁ : ∀ i, K ≤ (avar i).val → M.get s₁ (avar i) = env i := fun i hi => by
      rw [k₁ _ (.inr hi), henv i hi]
    refine M.seq_run (gen_ok K hK env a (k + 1) (by omega) hv.2.1 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2)
      henv₁) fun s₂ d₂ ⟨m₂, v₂, k₂⟩ => ?_
    have henv₂ : ∀ i, K ≤ (avar i).val → M.get s₂ (avar i) = env i := fun i hi => by
      rw [k₂ _ (.inr hi), henv₁ i hi]
    have hc3' := M.codeAt_mem (m₂.trans m₁) hc3
    refine M.seq_run (gen_ok K hK env b (k + 2) (by omega) hv.2.2 (Core.Done.at _ d₂ hc3' ho3) henv₂)
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

end Machine

/-! ## `Exp` through the embedding into `AExp` -/

def toA : Exp → AExp
  | .var i => .var ⟨i.val, by omega⟩
  | .const c => .const c
  | .bin op a b => .bin op (toA a) (toA b)
  | .ite c a b => .ite (toA c) (toA a) (toA b)

/-- an `Exp` environment as an `AEnv` (`v4 .. v7 = 0`) -/
def ext (env : Fin 4 → BitVec 64) : AEnv := fun j => if h : j.val < 4 then env ⟨j.val, h⟩ else 0

theorem toA_denote (env : Fin 4 → BitVec 64) : ∀ e : Exp, (toA e).denote (ext env) = e.denote env
  | .var i => by simp only [toA, AExp.denote, Exp.denote, ext]; rw [dite_pos' i.2]
  | .const _ => rfl
  | .bin op a b => by simp only [toA, AExp.denote, Exp.denote, toA_denote env a, toA_denote env b]
  | .ite c a b => by
    simp only [toA, AExp.denote, Exp.denote, toA_denote env c, toA_denote env a, toA_denote env b]

theorem toA_depth : ∀ e : Exp, (toA e).depth = e.depth
  | .var _ | .const _ => rfl
  | .bin _ a b => by simp only [toA, AExp.depth, Exp.depth, toA_depth a, toA_depth b]
  | .ite c a b => by simp only [toA, AExp.depth, Exp.depth, toA_depth c, toA_depth a, toA_depth b]

theorem toA_varsOK : ∀ e : Exp, varsOK 11 (toA e)
  | .var i => by
    show 11 ≤ (v4 i).val
    rw [v4_val]; omega
  | .const _ => trivial
  | .bin _ a b => ⟨toA_varsOK a, toA_varsOK b⟩
  | .ite c a b => ⟨toA_varsOK c, toA_varsOK a, toA_varsOK b⟩

/-- abstract code leaving the value of `e : Exp` in `r_k` -/
def mgenE (e : Exp) (k : Nat) : List AOp := mgen8 (toA e) k

/-- the compiled function: result in `v0 = r11`, then return -/
def mcompile (e : Exp) : List AOp := mgenE e 0 ++ [.mov (rk 11) (rk 0), .ret]

namespace Machine
variable (M : Machine)

theorem genE_ok (env : Fin 4 → BitVec 64) (e : Exp) (k : Nat) (hk : k + e.depth < 11) {s : M.S} {pc : BitVec 64}
    (hA : M.At s pc (M.code (mgenE e k))) (henv : ∀ i, M.get s (v4 i) = env i) :
    M.runsTo s fun s' => M.Done s s' (next pc (M.code (mgenE e k)).length) ∧ M.EPost 11 k (e.denote env) s s' := by
  have := M.gen_ok 11 (.inr rfl) (ext env) (toA e) k (by rw [toA_depth]; exact hk) (toA_varsOK e) hA
    (fun i hi => by
      have hi4 : i.val < 4 := by
        unfold avar at hi; by_cases h : i.val < 4
        · exact h
        · rw [dite_neg' h] at hi; dsimp only at hi; omega
      have := henv ⟨i.val, hi4⟩
      simp only [v4] at this
      rw [this]; unfold ext; rw [dite_pos' hi4])
  rwa [toA_denote] at this

/-- **`Exp` compiler correctness from the interface laws**: from `At` (code at `pc`) with a valid return
address, the machine runs to the return address with `r11 = e.denote (r11, r12, r13, r14)`, memory
unchanged, frame and control state kept. -/
theorem compile_ok (e : Exp) (he : e.depth < 11) {s : M.S} {pc : BitVec 64} (hA : M.At s pc (M.code (mcompile e)))
    (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ M.get s' (rk 11) = e.denote (fun i => M.get s (v4 i)) ∧
      M.ok s' ∧ M.mem s' = M.mem s ∧ M.keep s s' := by
  simp only [mcompile, code_append] at hA
  obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
  have hc2' : M.codeAt s (next pc (M.code (mgenE e 0)).length) (M.enc (.mov (rk 11) (rk 0)) ++ M.enc .ret) := by
    simpa only [code, List.append_nil] using hc2
  have ho2' : M.codeOK (next pc (M.code (mgenE e 0)).length) (M.enc (.mov (rk 11) (rk 0)) ++ M.enc .ret).length := by
    simpa only [code, List.append_nil] using ho2
  have h := M.seq_run (Q := fun s' => M.get s' (rk 11) = e.denote (fun i => M.get s (v4 i)) ∧ M.mem s' = M.mem s)
    (pc₂ := M.ra s) (M.genE_ok _ e 0 (by omega) hA1 fun _ => rfl) fun s₁ d₁ ⟨m₁, v₁, _⟩ => by
      have hA2 := Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2') ho2'
      obtain ⟨hA2, hc3, ho3⟩ := Core.At.split _ hA2
      refine M.seq_run (M.law_mov (by unfold MovOK; rw [rk_val (by omega), rk_val (by omega)]; omega) hA2)
        fun s₂ d₂ ⟨st₂, m₂⟩ => ?_
      have e₂ : M.ra s₂ = M.ra s₁ := M.keep_ra d₂.keep
      have e₁ : M.ra s₁ = M.ra s := M.keep_ra d₁.keep
      refine M.runsTo_mono (M.law_ret (by rw [e₂, e₁]; exact hra)
        (Core.Done.at _ d₂ (M.codeAt_mem m₂ hc3) ho3)) fun s₃ ⟨d₃, st₃, m₃⟩ => ⟨(e₂.trans e₁) ▸ d₃, ?_, ?_⟩
      · rw [st₃, (Core.Set1.same _ st₂), v₁]
      · rw [m₃, m₂, m₁]
  exact M.runsTo_mono h fun s' ⟨d, v, m⟩ => ⟨d.hpc, v, d.ok, m, d.keep⟩

end Machine
end Proven.Mach
