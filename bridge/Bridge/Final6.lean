/- Bridge.Final6: `Final5` plus `-` and `*` (Arith).  `Open6` = what remains open: `.bin` for &,|,<<,>> (value and
head typing) and `ite` on Nat operands / `dropHead`-affected `<` (3 resp. 0 occurrences in C).

STATUS: proved, no sorry. -/
import Bridge.Arith

namespace Bridge.Final6
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm Bridge.Final Bridge.Final3 Bridge.Final5
  Bridge.Arith Bridge.Add

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

structure Env6 (env : List Const) (sig : Sig) (P : Prog) : Prop extends Env5 env sig P where
  sub : SubEnv env
  mul : MulEnv env

structure Open6 (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
  binTy : ∀ {ρ op n i H X Y}, 4 ≤ op → binHead op = (n, i) → n ∈ binList →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.mem X (tyS M .uw) → O.mem Y (tyS M .uw) → O.mem (O.app (O.app H X) Y) (tyS M .uw)
  iteTy : ∀ {ρ r n cmp a b c d H X Y}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) → (cmp = 1 ∨ cmp = 2) →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  bin : ∀ {ρ op n i H x y z}, 4 ≤ op → binHead op = (n, i) → 1 ≤ op → op ≤ 7 → binV n x y = some z →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.app (O.app H (encM M (.w x))) (encM M (.w y)) = encM M (.w z)
  ite : ∀ {env r n cmp a b c d va vb H Xt Xe}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) →
    (cmp = 1 ∨ cmp = 2) → VSh (if n then .nt else .uw) va → VSh (if n then .nt else .uw) vb →
    (∀ A, D O M.cval (ρE (encM M) junk env) (trM a) A → A = encM M va) →
    (∀ B, D O M.cval (ρE (encM M) junk env) (trM b) B → B = encM M vb) →
    D O M.cval (ρE (encM M) junk env) (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem Xt (tyS M r) → O.mem Xe (tyS M r) →
    O.app (O.app H Xt) Xe = if cmpV cmp va vb then Xt else Xe

variable (L : SetLaws O)
include L

omit L in
theorem headD_inv {ρ : Nat → S} {f hi I : String} {Hv : S}
    (hD : D O M.cval ρ (trM (apps (.c f [0, 0, 0]) [U, U, U, apps (.c hi [0]) [U, .c I []]])) Hv) :
    Hv = opS M f hi (M.cval "UInt64" []) I := by
  obtain ⟨H3, Iv, hH3, hIv, rfl⟩ := app_inv hD
  obtain ⟨H2, U3, hH2, hU3, rfl⟩ := app_inv hH3
  obtain ⟨H1, U2, hH1, hU2, rfl⟩ := app_inv hH2
  obtain ⟨H0, U1, hH0, hU1, rfl⟩ := app_inv hH1
  obtain ⟨J, Ia, hJ, hIa, rfl⟩ := app_inv hIv
  obtain ⟨J0, U4, hJ0, hU4, rfl⟩ := app_inv hJ
  cases hH0; cases hU1; cases hU2; cases hU3; cases hJ0; cases hU4; cases hIa; rfl

theorem open5_of (E : Env6 env sig P) (Op : Open6 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy) :
    Open5 M sig P junk where
  binTy := fun {ρ op n i H X Y} hop hb hn hD hX hY => by
    by_cases h2 : op = 2
    · subst h2; simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      rw [headD_inv hD]
      exact op_mem L E.add E.sub.op (ρ := ρ) (univ1 (M := M) (L := L) E.enc E.enc.u64 ρ)
        (mem_ty M L E.sub.op.kU64 (ρ := ρ) (.app .const .const)) hX hY
    by_cases h3 : op = 3
    · subst h3; simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      rw [headD_inv hD]
      exact op_mem L E.add E.mul.op (ρ := ρ) (univ1 (M := M) (L := L) E.enc E.enc.u64 ρ)
        (mem_ty M L E.mul.op.kU64 (ρ := ρ) (.app .const .const)) hX hY
    by_cases h0 : op = 0
    · subst h0
      exact Op.binTy (op := 7) (by decide) (by rw [← hb]; rfl) hn hD hX hY
    exact Op.binTy (by omega) hb hn hD hX hY
  iteTy := Op.iteTy
  bin := fun {ρ op n i H x y z} hop hb h1 h7 hz hD => by
    by_cases h2 : op = 2
    · subst h2; simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      simp only [binV, Option.some.injEq] at hz; subst hz
      rw [headD_inv hD]; exact sub_field L E.toEnv5 E.sub hbl ρ x y
    by_cases h3 : op = 3
    · subst h3; simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      simp only [binV, Option.some.injEq] at hz; subst hz
      rw [headD_inv hD]; exact mul_field L E.toEnv5 E.mul hbl ρ x y
    exact Op.bin (by omega) hb h1 h7 hz hD
  ite := Op.ite

theorem ev_denotes_final6 (E : Env6 env sig P) (Op : Open6 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy)
    (hP : PWf sig P) {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  ev_denotes_final5 L E.toEnv5 (open5_of L E Op hbl) hbl hP h hw he

end Bridge.Final6
