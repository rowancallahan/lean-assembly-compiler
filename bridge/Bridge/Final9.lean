/- Bridge.Final9: `Final8` plus the Nat-`==` ite (IteNat).  `Open9` = what remains open: ite on Nat `<` and on
`dropHead`-affected UInt64 `<` (0 occurrences of either in C's emitted Expr).

STATUS: proved, no sorry. -/
import Bridge.IteNat

namespace Bridge.Final9
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm Bridge.Final Bridge.Final3
  Bridge.Final7 Bridge.Final8 Bridge.IteNat

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def doneIte9 (n : Bool) (cmp : Nat) (a b : X) : Prop := doneIte n cmp a b ∨ (n = true ∧ cmp = 1)

structure Env9 (env : List Const) (sig : Sig) (P : Prog) : Prop extends Env8 env sig P where
  natEq : NatEqEnv env

structure Open9 (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
  iteTy : ∀ {ρ r n cmp a b c d H X Y}, ¬ doneIte9 n cmp a b → condX n cmp a b = (c, d) → (cmp = 1 ∨ cmp = 2) →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  ite : ∀ {env r n cmp a b c d va vb H Xt Xe}, ¬ doneIte9 n cmp a b → condX n cmp a b = (c, d) →
    (cmp = 1 ∨ cmp = 2) → VSh (if n then .nt else .uw) va → VSh (if n then .nt else .uw) vb →
    (∀ A, D O M.cval (ρE (encM M) junk env) (trM a) A → A = encM M va) →
    (∀ B, D O M.cval (ρE (encM M) junk env) (trM b) B → B = encM M vb) →
    D O M.cval (ρE (encM M) junk env) (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem Xt (tyS M r) → O.mem Xe (tyS M r) →
    O.app (O.app H Xt) Xe = if cmpV cmp va vb then Xt else Xe

variable (L : SetLaws O)
include L

theorem open8_of (E : Env9 env sig P) (Op : Open9 M sig P junk) : Open8 M sig P junk where
  iteTy := fun {ρ r n cmp a b c d H X Y} h1 hcd hcmp ha hb hH hX hY => by
    by_cases h : n = true ∧ cmp = 1
    · obtain ⟨rfl, rfl⟩ := h
      exact iteEqN_ty L E.toEnv2 E.natEq hcd (by simpa using ha) (by simpa using hb) hH hX hY
    · exact Op.iteTy (fun hd => hd.elim h1 h) hcd hcmp ha hb hH hX hY
  ite := fun {env r n cmp a b c d va vb H Xt Xe} h1 hcd hcmp hva hvb iha ihb hH hXt hXe => by
    by_cases h : n = true ∧ cmp = 1
    · obtain ⟨rfl, rfl⟩ := h
      exact iteEqN_field L E.toEnv2 E.natEq hcd hva hvb iha ihb hH hXt hXe
    · exact Op.ite (fun hd => hd.elim h1 h) hcd hcmp hva hvb iha ihb hH hXt hXe

theorem ev_denotes_final9 (E : Env9 env sig P) (Op : Open9 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy)
    (hP : PWf sig P) {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  ev_denotes_final8 L E.toEnv8 (open8_of L E Op) hbl hP h hw he

end Bridge.Final9
