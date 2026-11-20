/- Non-tail recursion as a `CStmt` function with real calls (source level, model-free), once and for all.

Schema ("divide and combine"): `f a = if go a then comb a (f (c₀ a)) … (f (c_{m-1} a)) else comb a 0 … 0`, every
call on a smaller measure `μ`.  The function `recFn L fi GO ARG COMB` (index `fi` in the program):

  locals `0 .. p-1` = parameters, `p .. p+m-1` = call results `r_j`, `p+m .. 2p+m-1` = argument staging,
  variables `S ..` = scratch of the pieces;
  body = `GO; if v_S then (for j < m: (for k < p: ARG j k; a_k := v_S); r_j := fi(a_0 … a_{p-1})); COMB`,
  result `v_S`.

`GO`, `ARG j k`, `COMB` are call-free pieces (any `BStmt` with the stated effect on `v_S`, keeping every
variable below `S` and the heaps).  `rec_ok`: by strong induction on `μ`, a call of `fi` on `a` runs within
`frame * (μ a + 1)` bytes of stack and returns `res a`. -/
import Nano.Base.Compiler.CLang

namespace Proven.Mach

/-- the layout: `p` parameters, `m` calls, `N` locals, pieces from variable `S` -/
structure RecLay where
  p : Nat
  m : Nat
  N : Nat
  S : Nat

def RecLay.rv (L : RecLay) (j : Nat) : Nat := 8 + L.p + j
def RecLay.av (L : RecLay) (k : Nat) : Nat := 8 + L.p + L.m + k

def bskip (S : Nat) : BStmt := .assign S (.var S)

/-- the argument pieces of one call, each followed by `a_k := v_S` -/
def stage (L : RecLay) (A : Nat → BStmt) : Nat → BStmt
  | 0 => bskip L.S
  | k + 1 => .seq (stage L A k) (.seq (A k) (.assign (L.av k) (.var L.S)))

/-- calls `0 .. j-1` -/
def callsC (L : RecLay) (fi : Nat) (ARG : Nat → Nat → BStmt) : Nat → CStmt
  | 0 => .base (bskip L.S)
  | j + 1 => .seq (callsC L fi ARG j)
      (.seq (.base (stage L (ARG j) L.p)) (.call (L.rv j) fi ((List.range L.p).map fun k => .var (L.av k))))

def recBody (L : RecLay) (fi : Nat) (GO : BStmt) (ARG : Nat → Nat → BStmt) (COMB : BStmt) : CStmt :=
  .seq (.base GO) (.seq (.ite (.var L.S) (callsC L fi ARG L.m) (.base (bskip L.S))) (.base COMB))

def recFn (L : RecLay) (fi : Nat) (GO : BStmt) (ARG : Nat → Nat → BStmt) (COMB : BStmt) : Fn :=
  ⟨L.p, L.N, recBody L fi GO ARG COMB, .var L.S⟩

/-- the globals are `g`, the parameters are `vs` -/
def Hold (p : Nat) (g : BEnv) (E : BEnv) (vs : List (BitVec 64)) : Prop :=
  (∀ v, v < 8 → E v = g v) ∧ ∀ k, k < p → E (8 + k) = vs.getD k 0

theorem bskip_exec (S : Nat) (σ : BState) : BExec (bskip S) σ σ := by
  have := BExec.assign (v := S) (e := .var S) (σ := σ)
  have e : σ.env.set S ((BExp.var S).denote σ.env) = σ.env := by
    funext i; simp only [BEnv.set, BExp.denote]; split <;> simp_all
  rw [e] at this; exact this

theorem set_eq' (E : BEnv) (v : Nat) (x : BitVec 64) : E.set v x v = x := by simp [BEnv.set]
theorem set_ne' (E : BEnv) {v w : Nat} (x : BitVec 64) (h : w ≠ v) : E.set v x w = E w := by simp [BEnv.set, h]

section
variable {L : RecLay} {H : Heap} {W : WHeap} {E₀ : BEnv}

/-- the staging of one call: `a_k` holds the `k`-th argument; variables below `S` other than the `a`'s kept -/
theorem stage_exec (hS : 8 + 2 * L.p + L.m ≤ L.S) (A : Nat → BStmt) (val : Nat → BitVec 64)
    (hA : ∀ k, k < L.p → ∀ E, (∀ v, v < 8 + L.p + L.m → E v = E₀ v) →
      ∃ E', BExec (A k) ⟨E, H, W⟩ ⟨E', H, W⟩ ∧ E' L.S = val k ∧ ∀ v, v < L.S → E' v = E v) :
    ∀ n, n ≤ L.p → ∀ E, (∀ v, v < 8 + L.p + L.m → E v = E₀ v) →
      ∃ E', BExec (stage L A n) ⟨E, H, W⟩ ⟨E', H, W⟩ ∧ (∀ v, v < 8 + L.p + L.m → E' v = E v) ∧
        ∀ k, k < n → E' (L.av k) = val k
  | 0, _, E, _ => ⟨E, bskip_exec _ _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, E, hE => by
    obtain ⟨E₁, h1, k1, a1⟩ := stage_exec hS A val hA n (by omega) E hE
    obtain ⟨E₂, h2, v2, k2⟩ := hA n (by omega) E₁ fun v hv => (k1 v hv).trans (hE v hv)
    refine ⟨_, .seq h1 (.seq h2 .assign), fun v hv => ?_, fun k hk => ?_⟩
    · show BEnv.set _ _ _ v = _
      rw [set_ne' _ _ (by simp only [RecLay.av]; omega)]
      show E₂ v = E v
      rw [k2 v (by omega), k1 v hv]
    · show BEnv.set _ _ _ _ = _
      simp only [BExp.denote]
      by_cases e : k = n
      · subst e; rw [set_eq', v2]
      · rw [set_ne' _ _ (by simp only [RecLay.av]; omega), k2 _ (by simp only [RecLay.av]; omega), a1 k (by omega)]
end

theorem retEnv_same {E E' : BEnv} (h : ∀ v, v < 8 → E' v = E v) : retEnv E E' = E := by
  funext i; simp only [retEnv]; split
  · exact h i (by omega)
  · rfl

/-- **Non-tail recursion, once and for all.** -/
theorem rec_ok (P : Prog) (fi : Nat) (L : RecLay) (GO COMB : BStmt) (ARG : Nat → Nat → BStmt)
    (hf : fi < P.length) (hF : P[fi] = recFn L fi GO ARG COMB)
    (hS : 8 + 2 * L.p + L.m ≤ L.S) (H : Heap) (W : WHeap) (g : BEnv)
    {α : Type} (vals : α → List (BitVec 64)) (ok : α → Prop) (go : α → Bool) (cs : α → Nat → α) (μ : α → Nat)
    (res : α → BitVec 64) (hvl : ∀ a, (vals a).length = L.p)
    (hdec : ∀ a, ok a → go a = true → ∀ j, j < L.m → ok (cs a j) ∧ μ (cs a j) < μ a)
    (hGO : ∀ a E, ok a → Hold L.p g E (vals a) →
      ∃ E', BExec GO ⟨E, H, W⟩ ⟨E', H, W⟩ ∧ (E' L.S ≠ 0 ↔ go a = true) ∧ ∀ v, v < L.S → E' v = E v)
    (hARG : ∀ j k, j < L.m → k < L.p → ∀ a E, ok a → go a = true → Hold L.p g E (vals a) →
      ∃ E', BExec (ARG j k) ⟨E, H, W⟩ ⟨E', H, W⟩ ∧ E' L.S = (vals (cs a j)).getD k 0 ∧
        ∀ v, v < L.S → E' v = E v)
    (hCOMB : ∀ a E, ok a → Hold L.p g E (vals a) →
      (∀ j, j < L.m → E (L.rv j) = if go a then res (cs a j) else 0) →
      ∃ E', BExec COMB ⟨E, H, W⟩ ⟨E', H, W⟩ ∧ E' L.S = res a ∧ ∀ v, v < L.S → E' v = E v) :
    ∀ a, ok a → ∀ (σ : BState) (args : List BExp) (r : Nat), (∀ v, v < 8 → σ.env v = g v) → σ.heap = H →
      σ.wheap = W → args.map (·.denote σ.env) = vals a →
      CExec P ((recFn L fi GO ARG COMB).frame * (μ a + 1)) (.call r fi args) σ ⟨σ.env.set r (res a), H, W⟩ := by
  intro a
  generalize hn : μ a = n
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
  intro hok σ args r hg hH hW hargs
  subst hn
  let F := recFn L fi GO ARG COMB
  have hfr : F.frame * (μ a + 1) = F.frame + F.frame * μ a := by rw [Nat.mul_succ, Nat.add_comm]
  -- the callee's initial variables
  let E₀ := callEnv σ.env (args.map (·.denote σ.env))
  have hl : args.length = L.p := by rw [← List.length_map (f := (·.denote σ.env)), hargs, hvl]
  have h0 : Hold L.p g E₀ (vals a) := ⟨fun v hv => by simp only [E₀, callEnv, if_pos hv]; exact hg v hv,
    fun k hk => by simp only [E₀, callEnv, if_neg (show ¬(8 + k < 8) by omega), hargs, Nat.add_sub_cancel_left]⟩
  have hz : ∀ j, j < L.m → E₀ (L.rv j) = 0 := fun j hj => by
    simp only [E₀, callEnv, RecLay.rv, if_neg (show ¬(8 + L.p + j < 8) by omega), hargs]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hvl]; omega)]; rfl
  -- the body, from `E₀`, ends in `E₃` with the result in `v_S` and the globals kept
  suffices hb : ∃ E₃, CExec P (F.frame * μ a) F.body ⟨E₀, H, W⟩ ⟨E₃, H, W⟩ ∧ E₃ L.S = res a ∧
      ∀ v, v < 8 → E₃ v = g v by
    obtain ⟨E₃, hx, h3, hg3⟩ := hb
    have hc := CExec.call (P := P) (res := r) (args := args) (σ := σ) (k := F.frame * (μ a + 1))
      (k' := F.frame * μ a) hf (by rw [hF]; exact hl) (by rw [hF, hfr]; exact Nat.le_refl _) (by rw [hF]; rw [hH, hW] at *; exact hx)
    have e1 : retEnv σ.env E₃ = σ.env := retEnv_same fun v hv => (hg3 v hv).trans (hg v hv).symm
    simp only [hF] at hc
    rw [e1, show (recFn L fi GO ARG COMB).ret.denote E₃ = res a from h3] at hc
    exact hc
  obtain ⟨E₁, x1, g1, k1⟩ := hGO a E₀ hok h0
  have h1 : Hold L.p g E₁ (vals a) := ⟨fun v hv => (k1 v (by omega)).trans (h0.1 v hv),
    fun k hk => (k1 _ (by omega)).trans (h0.2 k hk)⟩
  -- the calls: `r_j` for `j < n`, the parameters and globals kept
  have hcalls : go a = true → ∀ i, i ≤ L.m → ∀ E, Hold L.p g E (vals a) →
      ∃ E', CExec P (F.frame * μ a) (callsC L fi ARG i) ⟨E, H, W⟩ ⟨E', H, W⟩ ∧ Hold L.p g E' (vals a) ∧
        (∀ j, j < i → E' (L.rv j) = res (cs a j)) ∧ ∀ v, i ≤ v - 8 - L.p → v < 8 + L.p + L.m → E' v = E v := by
    intro hgo i
    induction i with
    | zero => intro _ E hE; exact ⟨E, .base (bskip_exec _ _), hE, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ _ => rfl⟩
    | succ i ihi =>
      intro hi E hE
      obtain ⟨E₁, x1, hh1, r1, k1⟩ := ihi (by omega) E hE
      obtain ⟨okc, hlt⟩ := hdec a hok hgo i (by omega)
      obtain ⟨E₂, x2, k2, a2⟩ := stage_exec (H := H) (W := W) (E₀ := E₁) hS (ARG i) (fun k => (vals (cs a i)).getD k 0)
        (fun k hk E hE' => hARG i k (by omega) hk a E hok hgo
          ⟨fun v hv => (hE' v (by omega)).trans (hh1.1 v hv), fun k hk => (hE' _ (by omega)).trans (hh1.2 k hk)⟩)
        L.p (Nat.le_refl _) E₁ fun _ _ => rfl
      have hargs' : ((List.range L.p).map fun k => BExp.var (L.av k)).map (·.denote E₂) = vals (cs a i) := by
        apply List.ext_getElem (by simp [hvl]) fun k h1 h2 => ?_
        simp only [List.map_map, List.getElem_map, List.getElem_range, Function.comp_def, BExp.denote]
        rw [a2 k (by simpa using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
      have hc := ih (μ (cs a i)) (by omega) (cs a i) rfl okc ⟨E₂, H, W⟩ _ (L.rv i)
        (fun v hv => (k2 v (by omega)).trans (hh1.1 v hv)) rfl rfl hargs'
      refine ⟨E₂.set (L.rv i) (res (cs a i)), .seq x1 (.seq (.base x2)
        (hc.mono (by
          have : μ (cs a i) + 1 ≤ μ a := hlt
          exact Nat.mul_le_mul_left _ this))), ⟨fun v hv => ?_, fun k hk => ?_⟩, fun j hj => ?_, fun v h1 h2 => ?_⟩
      · rw [set_ne' _ _ (by simp only [RecLay.rv]; omega), k2 v (by omega)]; exact hh1.1 v hv
      · rw [set_ne' _ _ (by simp only [RecLay.rv]; omega), k2 _ (by omega)]; exact hh1.2 k hk
      · by_cases e : j = i
        · subst e; exact set_eq' _ _ _
        · rw [set_ne' _ _ (by simp only [RecLay.rv]; omega), k2 _ (by simp only [RecLay.rv]; omega)]
          exact r1 j (by omega)
      · rw [set_ne' _ _ (by simp only [RecLay.rv]; omega), k2 v h2]; exact k1 v (by omega) h2
  have hfin : ∃ E₂, CExec P (F.frame * μ a) (.ite (.var L.S) (callsC L fi ARG L.m) (.base (bskip L.S)))
      ⟨E₁, H, W⟩ ⟨E₂, H, W⟩ ∧ Hold L.p g E₂ (vals a) ∧
      ∀ j, j < L.m → E₂ (L.rv j) = if go a then res (cs a j) else 0 := by
    by_cases hgo : go a = true
    · obtain ⟨E₂, x2, hh2, r2, _⟩ := hcalls hgo L.m (Nat.le_refl _) E₁ h1
      exact ⟨E₂, .iteT (by simpa [BExp.denote] using g1.2 hgo) x2, hh2, fun j hj => by rw [if_pos hgo]; exact r2 j hj⟩
    · refine ⟨E₁, .iteF (by
        simp only [BExp.denote]; exact Classical.byContradiction fun h => hgo (g1.1 h)) (.base (bskip_exec _ _)),
        h1, fun j hj => ?_⟩
      rw [if_neg hgo, k1 _ (by simp only [RecLay.rv]; omega)]; exact hz j hj
  obtain ⟨E₂, x2, hh2, r2⟩ := hfin
  obtain ⟨E₃, x3, h3, k3⟩ := hCOMB a E₂ hok hh2 r2
  exact ⟨E₃, .seq (.base x1) (.seq x2 (.base x3)), h3, fun v hv => (k3 v (by omega)).trans (hh2.1 v hv)⟩

end Proven.Mach
