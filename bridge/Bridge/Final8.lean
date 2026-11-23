/- Bridge.Final8: `Final7` plus `&&&` and `|||` (Bits).  All seven `.bin` ops are now discharged.  `Open8` = what
remains open: `ite` on Nat operands / `dropHead`-affected `<` (3 resp. 0 occurrences in C).

STATUS: proved, no sorry. -/
import Bridge.Bits

namespace Bridge.Final8
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm Bridge.Final Bridge.Final3 Bridge.Final6
  Bridge.Final7 Bridge.Arith Bridge.Add Bridge.Shift Bridge.Bits

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

structure Env8 (env : List Const) (sig : Sig) (P : Prog) : Prop extends Env7 env sig P where
  bits : BitsEnv env

structure Open8 (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
  iteTy : ∀ {ρ r n cmp a b c d H X Y}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) → iteOk n cmp a b →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  ite : ∀ {env r n cmp a b c d va vb H Xt Xe}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) →
    iteOk n cmp a b → VSh (if n then .nt else .uw) va → VSh (if n then .nt else .uw) vb →
    (∀ A, D O M.cval (ρE (encM M) junk env) (trM a) A → A = encM M va) →
    (∀ B, D O M.cval (ρE (encM M) junk env) (trM b) B → B = encM M vb) →
    D O M.cval (ρE (encM M) junk env) (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem Xt (tyS M r) → O.mem Xe (tyS M r) →
    O.app (O.app H Xt) Xe = if cmpV cmp va vb then Xt else Xe

variable (L : SetLaws O)
include L

theorem open7_of (E : Env8 env sig P) (Op : Open8 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy) :
    Open7 M sig P junk where
  binTy := fun {ρ op n i H X Y} hop hb hn hD hX hY => by
    have hUu := univ1 (M := M) (L := L) E.enc E.enc.u64 ρ
    rcases hop with rfl | rfl
    · simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      rw [headD_inv hD]
      exact core_mem L E.add E.bits.andC (ρ := ρ) hUu (mem_ty M L E.bits.andI (ρ := ρ) (.app .const .const)) hX hY
    · simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      rw [headD_inv hD]
      exact core_mem L E.add E.bits.orC (ρ := ρ) hUu (mem_ty M L E.bits.orI (ρ := ρ) (.app .const .const)) hX hY
  iteTy := Op.iteTy
  bin := fun {ρ op n i H x y z} hop hb hz hD => by
    rcases hop with rfl | rfl
    · simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      simp only [binV, Option.some.injEq] at hz; subst hz
      rw [headD_inv hD]; exact and_field L E.toEnv7 E.bits hbl ρ x y
    · simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      simp only [binV, Option.some.injEq] at hz; subst hz
      rw [headD_inv hD]; exact or_field L E.toEnv7 E.bits hbl ρ x y
  ite := Op.ite

theorem ev_denotes_final8 (E : Env8 env sig P) (Op : Open8 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy)
    (hP : PWf sig P) {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  ev_denotes_final7 L E.toEnv7 (open7_of L E Op hbl) hbl hP h hw he

end Bridge.Final8
