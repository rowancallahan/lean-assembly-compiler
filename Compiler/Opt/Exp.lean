/- The optimising `Exp` compiler over any `Wide` target, and its correctness (`optE_ok`, the statement of
`Machine.compile_ok`):  selection (`Sel.into`) → register assignment (`fE`, checked injective) → lowering
(`Wide.low`, checked `wf`) → words.

Registers: variable `i` in `r(11+i)` (as before), temporary `k` in `r k` (`k < 10`), scratch `r10`. -/
import Compiler.Opt.Fn
import Compiler.Opt.Sel
import Compiler.Exp

namespace Proven.Mach
open IR

/-- scratch register of the `Exp` / `Stmt` pipelines -/
def scE : Reg := ⟨10, by decide⟩

/-- register assignment: variables `0..3 ↦ r11..r14`, temporary `k` (virtual `32 + k`) `↦ r k`; anything else
goes to the scratch register (and is then rejected by `wf`) -/
def fE (x : Nat) : Reg :=
  if h : x < 4 then ⟨11 + x, by omega⟩ else if h : 32 ≤ x ∧ x < 42 then ⟨x - 32, by omega⟩ else scE

theorem fE_v4 (i : Fin 4) : fE i.val = v4 i := by revert i; decide

theorem uses_toA : ∀ (e : Exp) (x : Nat), Sel.uses (Sel.ofA (toA e)) x = true → x < 4
  | .var i, x, h => by have e : i.val = x := of_decide_eq_true h; omega
  | .const _, _, h => nomatch h
  | .bin _ a b, x, h => by
    simp only [toA, Sel.ofA, Sel.uses, Bool.or_eq_true] at h
    exact h.elim (uses_toA a x) (uses_toA b x)
  | .ite c a b, x, h => by
    simp only [toA, Sel.ofA, Sel.uses, Bool.or_eq_true] at h
    exact h.elim (fun h => h.elim (uses_toA c x) (uses_toA a x)) (uses_toA b x)

/-- an IR state whose variables hold `env` agrees with `toA e` -/
theorem agree_toA {ram : Nat → Prop} {fp : Nat} {sv : Nat → BitVec 64} (e : Exp) {env : Fin 4 → BitVec 64}
    {σ : St Nat} (h : ∀ i : Fin 4, σ.reg i.val = env i) :
    Sel.Agree ram fp (Sel.envA (ext env)) sv (Sel.ofA (toA e)) σ := Sel.agreeA (toA e) fun i hi => by
  have h4 := uses_toA e i.val hi
  unfold ext; rw [dite_pos' h4]; exact h ⟨i.val, h4⟩

namespace Wide
variable (M : Wide)

/-- IR code (virtual registers) for `v0 := e` -/
def irE (e : Exp) : Code Nat := Sel.into (Sel.ofA (toA e)) 0 0

/-- **The optimising `Exp` compiler** (abstract level): `none` if the expression needs more than the 10
temporaries. -/
def optE (e : Exp) : Option (List (BitVec 32)) := M.fn scE fE [0] (irE e)

/-- **Correctness of the optimising `Exp` compiler from the wide laws**; same conclusion as
`Machine.compile_ok`. -/
theorem optE_ok (e : Exp) {ws : List (BitVec 32)} (hc : M.optE e = some ws) {s : M.S} {pc : BitVec 64}
    (hA : M.At s pc ws) (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ M.get s' (rk 11) = e.denote (fun i => M.get s (v4 i)) ∧
      M.ok s' ∧ M.mem s' = M.mem s ∧ M.keep s s' := by
  obtain ⟨σ', hx, hv, hm, -⟩ := Sel.into_ok (ram := fun _ => False) (fp := (M.fr s).toNat) (sv := fun _ => 0) (Sel.ofA (toA e)) 0 0 ⟨fun x => M.get s (fE x), M.mem s⟩
    (agree_toA e (env := fun i => M.get s (v4 i)) fun i => congrArg _ (fE_v4 i))
  rw [Sel.ofA_denote, toA_denote] at hv
  refine M.runsTo_mono (fn_ok (fun _ h => h.elim) hc hA.ok hA.hpc ⟨hA.code, hA.codeOK, fun _ h => h.elim, rfl⟩ hra hx)
    fun s' ⟨p, v, o, m, k⟩ => ⟨p, ?_, o, m.trans hm, k⟩
  rw [← hv]; exact v 0 (List.mem_cons_self ..) (by decide)

end Wide
end Proven.Mach
