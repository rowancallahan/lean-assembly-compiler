/- The optimising `Stmt` compiler (assignments, sequencing, `while`) over any `Wide` target, and its
correctness (`optS_ok`, the statement of `Machine.compF_ok`).  An assignment writes its variable directly;
a loop condition becomes the loop's test (comparison fused into the branch). -/
import Compiler.Opt.Exp
import Compiler.Stmt

namespace Proven.Mach
open IR

/-- IR code (virtual registers) of a statement -/
def irS : Stmt → Code Nat
  | .assign v e => Sel.into (toA e) v.val 0
  | .seq a b => .seq (irS a) (irS b)
  | .loop c b => Sel.loopCode (toA c) (irS b)

/-- selection preserves the statement semantics -/
theorem irS_ok (ram : Nat → Prop) (fp : Nat) : ∀ {p : Stmt} {σe σe' : Env}, Exec p σe σe' → ∀ (σ : St Nat),
    (∀ i : Fin 4, σ.reg i.val = σe i) →
    ∃ σ', IR.Exec ram fp (irS p) σ σ' ∧ (∀ i : Fin 4, σ'.reg i.val = σe' i) ∧ σ'.mem = σ.mem := by
  intro p σe σe' h
  induction h with
  | @assign v e σe =>
    intro σ hσ
    obtain ⟨σ', hx, hv, hm, hf⟩ := Sel.into_ok (ram := ram) (toA e) v.val 0 σ (agree_toA e hσ)
    rw [toA_denote] at hv
    refine ⟨σ', hx, fun i => ?_, hm⟩
    unfold Env.set
    by_cases hi : i = v
    · rw [ite_pos hi, hi, hv]
    · rw [ite_neg hi, hf i.val (fun e => hi (Fin.ext e)) (by omega), hσ]
  | seq _ _ iha ihb =>
    intro σ hσ
    obtain ⟨σ₁, x₁, v₁, m₁⟩ := iha σ hσ
    obtain ⟨σ₂, x₂, v₂, m₂⟩ := ihb σ₁ v₁
    exact ⟨σ₂, .seq x₁ x₂, v₂, m₂.trans m₁⟩
  | @loopF c b σe hc =>
    intro σ hσ
    obtain ⟨σ₁, x₁, f₁⟩ := Sel.loopCode_exit (ram := ram) (body := irS b) (agree_toA c hσ)
      (by rw [toA_denote]; exact hc)
    exact ⟨σ₁, x₁, fun i => (f₁.2 i.val (by omega)).trans (hσ i), f₁.1⟩
  | @loopT c b σe _ _ hc _ _ ihb ihl =>
    intro σ hσ
    obtain ⟨σ₁, f₁, hx⟩ := Sel.loopCode_iter (ram := ram) (body := irS b) (agree_toA c hσ)
      (by rw [toA_denote]; exact hc)
    obtain ⟨σ₂, x₂, v₂, m₂⟩ := ihb σ₁ fun i => (f₁.2 i.val (by omega)).trans (hσ i)
    obtain ⟨σ₃, x₃, v₃, m₃⟩ := ihl σ₂ v₂
    exact ⟨σ₃, hx σ₂ σ₃ x₂ x₃, v₃, m₃.trans (m₂.trans f₁.1)⟩

namespace Wide
variable (M : Wide)

/-- **The optimising `Stmt` compiler** (as a function: run the statement, then return) -/
def optS (p : Stmt) : Option (List (BitVec 32)) := M.fn scE fE [0, 1, 2, 3] (irS p)

/-- **Correctness of the optimising `Stmt` compiler from the wide laws**; same conclusion as
`Machine.compF_ok`. -/
theorem optS_ok {p : Stmt} {ws : List (BitVec 32)} (hc : M.optS p = some ws) {σ' : Env} {s : M.S}
    (hex : Exec p (fun i => M.get s (v4 i)) σ') {pc : BitVec 64} (hA : M.At s pc ws) (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ (∀ i, M.get s' (v4 i) = σ' i) ∧ M.ok s' ∧ M.mem s' = M.mem s ∧
      M.keep s s' := by
  obtain ⟨τ', hx, hv, hm⟩ := irS_ok (fun _ => False) (M.fr s).toNat hex ⟨fun x => M.get s (fE x), M.mem s⟩
    fun i => congrArg _ (fE_v4 i)
  refine M.runsTo_mono (fn_ok (fun _ h => h.elim) hc hA.ok hA.hpc ⟨hA.code, hA.codeOK, fun _ h => h.elim, rfl⟩ hra hx)
    fun s' ⟨p, v, o, m, k⟩ => ⟨p, fun i => ?_, o, m.trans hm, k⟩
  rw [← hv, ← fE_v4]
  exact v i.val (by revert i; decide) (by revert i; decide)

end Wide
end Proven.Mach
