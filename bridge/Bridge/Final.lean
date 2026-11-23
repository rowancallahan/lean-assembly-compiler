/- Bridge.Final: the assembly with the discharged `+` (Add.lean) and UInt64 `==` ite (Ite.lean) plugged in.
`Open2` is what remains open: `.bin` for ops 2..7 (−,×,&,|,<<,>>) with their head typing, `ite` on `<` and on Nat
operands (value and head typing), and the 9 prelude ops.  `ev_denotes_final`: Ev ⇒ Denotes under `Env2` + `Open2`.

STATUS: proved, no sorry. -/
import Bridge.Ite

namespace Bridge.Final
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota2 Bridge.Asm Bridge.Add
  Bridge.Cmp Bridge.Ite

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def brLitNTy : E := piN [(tNat, false)] (eqE 1 tNat
  (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0))) (.bvar 0))

structure Env2 (env : List Const) (sig : Sig) (P : Prog) : Prop extends Env env sig P where
  add : AddEnv env
  cmp : CmpEnv env
  beqE : BeqEnv env
  iteE : IteEnv env

structure Open2 (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
  binTy : ∀ {ρ op n i H X Y}, op ≠ 1 → binHead op = (n, i) → n ∈ binList →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.mem X (tyS M .uw) → O.mem Y (tyS M .uw) → O.mem (O.app (O.app H X) Y) (tyS M .uw)
  iteTy : ∀ {ρ r n cmp a b c d H X Y}, ¬(n = false ∧ cmp = 1) → condX n cmp a b = (c, d) → (cmp = 1 ∨ cmp = 2) →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  bin : ∀ {ρ op n i H x y z}, op ≠ 1 → binHead op = (n, i) → 1 ≤ op → op ≤ 7 → binV n x y = some z →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.app (O.app H (encM M (.w x))) (encM M (.w y)) = encM M (.w z)
  ite : ∀ {env r n cmp a b c d va vb H Xt Xe}, ¬(n = false ∧ cmp = 1) → condX n cmp a b = (c, d) →
    (cmp = 1 ∨ cmp = 2) → VSh (if n then .nt else .uw) va → VSh (if n then .nt else .uw) vb →
    (∀ A, D O M.cval (ρE (encM M) junk env) (trM a) A → A = encM M va) →
    (∀ B, D O M.cval (ρE (encM M) junk env) (trM b) B → B = encM M vb) →
    D O M.cval (ρE (encM M) junk env) (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem Xt (tyS M r) → O.mem Xe (tyS M r) →
    O.app (O.app H Xt) Xe = if cmpV cmp va vb then Xt else Xe
  prim : PrimFactsM O M.cval (encM M)

variable (L : SetLaws O)
include L

omit L in
theorem binHead1 : binHead 1 = ("HAdd.hAdd", apps (.c "instHAdd" [0]) [U, .c "instAddUInt64" []]) := rfl

/-- typing of the UInt64-`==` ite head -/
theorem iteEqU_ty (E : Env2 env sig P) {ρ : Nat → S} {r : Sh} {a b c d : X} {Hv X Y : S}
    (hcd : condX false 1 a b = (c, d))
    (ha : ∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M .uw)) (hb : ∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M .uw))
    (hH : D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) Hv)
    (hX : O.mem X (tyS M r)) (hY : O.mem Y (tyS M r)) : O.mem (O.app (O.app Hv X) Y) (tyS M r) := by
  simp only [condX, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq] at hcd
  obtain ⟨rfl, rfl⟩ := hcd
  obtain ⟨H2, Dv, hH2, hD, rfl⟩ := app_inv hH
  obtain ⟨H1, Cv, hH1, hC, rfl⟩ := app_inv hH2
  obtain ⟨H0, Rv, hH0, hRv, rfl⟩ := app_inv hH1
  cases hH0
  rw [D_functional L hRv (shTy_tyS M r)]
  obtain ⟨C2, Tv, hC2, hT, rfl⟩ := app_inv hC
  obtain ⟨C1, Qv, hC1, hQ, rfl⟩ := app_inv hC2
  obtain ⟨C0, Bv, hC0, hBv, rfl⟩ := app_inv hC1
  cases hC0; cases hBv; cases hT
  obtain ⟨D1, Q', hD1, hQ', rfl⟩ := app_inv hD
  obtain ⟨D0, Q'', hD0, hQ'', rfl⟩ := app_inv hD1
  cases hD0; cases hQ'
  obtain rfl := D_functional L hQ'' hQ
  obtain ⟨Q2, Bb, hQ2, hBb, rfl⟩ := app_inv hQ
  obtain ⟨Q1, Aa, hQ1, hAa, rfl⟩ := app_inv hQ2
  obtain ⟨Q0, Iv, hQ0, hIv, rfl⟩ := app_inv hQ1
  obtain ⟨Qh, Uv, hQh, hUv, rfl⟩ := app_inv hQ0
  cases hQh; cases hUv
  obtain ⟨I1, Dq, hI1, hDq, rfl⟩ := app_inv hIv
  obtain ⟨I0, Uw, hI0, hUw, rfl⟩ := app_inv hI1
  cases hI0; cases hUw; cases hDq
  have hTb := mem_ty M L E.cmp.btrue (ρ := ρ) .const
  have hQm := beqU_mem L E.enc E.cmp E.beqE (ρ := ρ) (ha _ hAa) (hb _ hBb)
  exact ite_mem L E.iteE (ρ := ρ) (tyS_univ (M := M) L E.enc ρ r) (eqB_mem L E.cmp E.iteE (ρ := ρ) hQm hTb)
    (decB_mem L E.cmp E.beqE E.iteE (ρ := ρ) hQm hTb) hX hY

theorem open_of (E : Env2 env sig P) (Op : Open2 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy) :
    Open M sig P junk where
  binTy := fun {ρ op n i H X Y} hb hn hD hX hY => by
    by_cases hop : op = 1
    · subst hop; rw [binHead1] at hb; simp only [Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      exact add_ty L E.enc E.add hD hX hY
    · exact Op.binTy hop hb hn hD hX hY
  iteTy := fun {ρ r n cmp a b c d H X Y} hcd hcmp ha hb hH hX hY => by
    by_cases h : n = false ∧ cmp = 1
    · obtain ⟨rfl, rfl⟩ := h
      exact iteEqU_ty L E hcd (by simpa using ha) (by simpa using hb) hH hX hY
    · exact Op.iteTy h hcd hcmp ha hb hH hX hY
  bin := fun {ρ op n i H x y z} hb h1 h7 hz hD => by
    by_cases hop : op = 1
    · subst hop; rw [binHead1] at hb; simp only [Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      simp only [binV, Option.some.injEq] at hz; subst hz
      exact add_field L E.enc E.lit E.instN hbl E.add hD x y
    · exact Op.bin hop hb h1 h7 hz hD
  ite := fun {env r n cmp a b c d va vb H Xt Xe} hcd hcmp hva hvb iha ihb hH hXt hXe => by
    by_cases h : n = false ∧ cmp = 1
    · obtain ⟨rfl, rfl⟩ := h
      exact iteEqU_field L E.enc E.lit E.instN E.cmp E.beqE E.iteE hbl hcd hva hvb iha ihb hH hXt hXe
    · exact Op.ite h hcd hcmp hva hvb iha ihb hH hXt hXe
  prim := Op.prim

/-- **Ev ⇒ Denotes** (trimmed model), with `+` and UInt64 `==` discharged -/
theorem ev_denotes_final (E : Env2 env sig P) (Op : Open2 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy)
    (hP : PWf sig P) {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  ev_denotes_assembled L E.toEnv (open_of L E Op hbl) hP h hw he

end Bridge.Final
