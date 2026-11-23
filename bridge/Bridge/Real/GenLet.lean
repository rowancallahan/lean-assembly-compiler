/- Bridge.Real.GenLet: the `let` step of the general theorem (`Ev.lt`, DENOTES_GENERAL §2).

nano's `let x := v; b` is `tr`-ed to the redex `(λ x : T. b) v` (binder data `.never`).  `conv_let`: if `v`
converts to a value `w` and the body with `w` substituted converts to `y`, the redex converts to `y`
(congruence into the argument, then `Conv.beta`).  `substD_comp`: substituting `w` into the body after the
environment `es` equals substituting `w :: es` at once — the shape the invariant `R` uses for the extended env. -/
import Bridge.Real.TySubst
import Bridge.Real.Conv

namespace Bridge.Real.GenLet
open ConLeche Bridge Bridge.Real Bridge.Real.Engine Bridge.Real.EngineLam Bridge.Real.TySubst

/-- composing substitutions: `w` at depth `d` after closed `es` at depth `d + 1` is `w :: es` at depth `d` -/
theorem substD_comp {w : Expr} {es : List Expr} (hw : wfk 0 w = true) (hes : ∀ e ∈ es, wfk 0 e = true) :
    ∀ {d : Nat} {e : Expr}, wfk (d + 1 + es.length) e = true →
      substD [w] d (substD es (d + 1) e) = substD (w :: es) d e
  | d, .bvar j, h => by
    simp only [wfk, decide_eq_true_eq] at h
    by_cases h1 : j < d
    · simp [substD, h1, show j < d + 1 by omega]
    · by_cases h2 : j = d
      · subst h2; simp [substD]
      · have hj : j - (d + 1) < es.length := by omega
        have hget : es[j - (d + 1)]? = some (es[j - (d + 1)]'hj) := List.getElem?_eq_getElem hj
        have hcl := hes _ (List.getElem_mem hj)
        simp only [substD, show ¬ j < d + 1 by omega, h1, if_false, List.getD_eq_getElem?_getD, hget,
          Option.getD_some]
        rw [substD_closed hcl (Nat.zero_le _)]
        have : j - d = (j - (d + 1)) + 1 := by omega
        rw [this, List.getElem?_cons_succ, hget]; rfl
  | _, .sort _, _ | _, .const _ _, _ | _, .lit (.natVal _), _ => rfl
  | d, .app f a, h => by
    simp only [wfk, Bool.and_eq_true] at h
    simp only [substD, substD_comp hw hes h.1, substD_comp hw hes h.2]
  | d, .lam t b m, h => by
    simp only [wfk, Bool.and_eq_true] at h
    have h2 : wfk (d + 1 + 1 + es.length) b = true := by rw [Nat.add_right_comm (d + 1)]; exact h.2
    simp only [substD, substD_comp hw hes h.1, substD_comp (d := d + 1) hw hes h2]
  | d, .forallE t b m, h => by
    simp only [wfk, Bool.and_eq_true] at h
    have h2 : wfk (d + 1 + 1 + es.length) b = true := by rw [Nat.add_right_comm (d + 1)]; exact h.2
    simp only [substD, substD_comp hw hes h.1, substD_comp (d := d + 1) hw hes h2]
  | d, .proj s i e, h => by
    simp only [wfk] at h
    simp only [substD, substD_comp hw hes h]
  | _, .lit (.strVal _), h | _, .fvar _ _, h | _, .letE _ _ _, h => by simp [wfk] at h

/-- **the `let` step**: the redex converts to what the body does at the argument's value -/
theorem conv_let {tab : Tab} {eqs : List (Expr × Expr)} {thms : List Thm} {T b v w y S : Expr} {u : Level}
    (hT : HasTy tab eqs [] T (.sort u)) (hTc : wfk 0 T = true) (hSc : wfk 0 S = true)
    (hb : HasTy tab eqs [T] b S) (hb1 : wfk 1 b = true)
    (hv : HasTy tab eqs [] v T) (hw : HasTy tab eqs [] w T) (hw0 : wfk 0 w = true)
    (cv : Conv tab eqs thms [] v w T) (cb : Conv tab eqs thms [] (substD [w] 0 b) y S) :
    Conv tab eqs thms [] (.app (.lam T b ⟨.never⟩) v) y S := by
  have hlam : HasTy tab eqs [] (.lam T b ⟨.never⟩) (.forallE T S ⟨.never⟩) :=
    .lam hT hTc hSc (fun _ h => by simp at h) hb
  have c1 : Conv tab eqs thms [] (apps (.lam T b ⟨.never⟩) [v]) (apps (.lam T b ⟨.never⟩) [w]) S :=
    .cong (.app hlam hv hSc) (.cons cv .nil)
  have c2 : Conv tab eqs thms [] (.app (.lam T b ⟨.never⟩) w) (substD [w] 0 b) S :=
    .beta (.refl (.app hlam hw hSc)) hw hb1 hw0
  exact .trans c1 (.trans c2 cb)

end Bridge.Real.GenLet
