/- Bridge.Final7: `Final6` plus `<<<` and `>>>` (Shift).  `Open7` = what remains open: `.bin` for `&&&`, `|||` (value
and head typing) and `ite` on Nat operands / `dropHead`-affected `<` (3 resp. 0 occurrences in C).

STATUS: proved, no sorry. -/
import Bridge.Shift

namespace Bridge.Final7
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm Bridge.Final Bridge.Final3 Bridge.Final6
  Bridge.Arith Bridge.Add Bridge.Shift

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

structure Env7 (env : List Const) (sig : Sig) (P : Prog) : Prop extends Env6 env sig P where
  shift : ShiftEnv env

structure Open7 (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
  binTy : ∀ {ρ op n i H X Y}, (op = 4 ∨ op = 5) → binHead op = (n, i) → n ∈ binList →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.mem X (tyS M .uw) → O.mem Y (tyS M .uw) → O.mem (O.app (O.app H X) Y) (tyS M .uw)
  iteTy : ∀ {ρ r n cmp a b c d H X Y}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) → iteOk n cmp a b →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  bin : ∀ {ρ op n i H x y z}, (op = 4 ∨ op = 5) → binHead op = (n, i) → binV n x y = some z →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.app (O.app H (encM M (.w x))) (encM M (.w y)) = encM M (.w z)
  ite : ∀ {env r n cmp a b c d va vb H Xt Xe}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) →
    iteOk n cmp a b → VSh (if n then .nt else .uw) va → VSh (if n then .nt else .uw) vb →
    (∀ A, D O M.cval (ρE (encM M) junk env) (trM a) A → A = encM M va) →
    (∀ B, D O M.cval (ρE (encM M) junk env) (trM b) B → B = encM M vb) →
    D O M.cval (ρE (encM M) junk env) (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem Xt (tyS M r) → O.mem Xe (tyS M r) →
    O.app (O.app H Xt) Xe = if cmpV cmp va vb then Xt else Xe

variable (L : SetLaws O)
include L

theorem open6_of (E : Env7 env sig P) (Op : Open7 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy) :
    Open6 M sig P junk where
  binTy := fun {ρ op n i H X Y} hop hb hn hD hX hY => by
    have hUu := univ1 (M := M) (L := L) E.enc E.enc.u64 ρ
    by_cases h45 : op = 4 ∨ op = 5
    · exact Op.binTy h45 hb hn hD hX hY
    by_cases h6 : op = 6
    · subst h6; simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      rw [headD_inv hD]
      exact core_mem L E.add E.shift.shlC (ρ := ρ) hUu (mem_ty M L E.shift.shlI (ρ := ρ) (.app .const .const)) hX hY
    -- every other op ≥ 4 is `>>>` (binHead's default)
    have hb7 : binHead op = binHead 7 := by
      unfold binHead; rcases op with _ | _ | _ | _ | _ | _ | _ | op <;> first | omega | rfl
    rw [hb7] at hb; simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
    rw [headD_inv hD]
    exact core_mem L E.add E.shift.shrC (ρ := ρ) hUu (mem_ty M L E.shift.shrI (ρ := ρ) (.app .const .const)) hX hY
  iteTy := Op.iteTy
  bin := fun {ρ op n i H x y z} hop hb h1 h7 hz hD => by
    by_cases h45 : op = 4 ∨ op = 5
    · exact Op.bin h45 hb hz hD
    by_cases h6 : op = 6
    · subst h6; simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
      simp only [binV, Option.some.injEq] at hz; subst hz
      rw [headD_inv hD]; exact shl_field L E.toEnv6 E.shift hbl ρ x y
    have h7' : op = 7 := by omega
    subst h7'; simp only [binHead, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
    simp only [binV, Option.some.injEq] at hz; subst hz
    rw [headD_inv hD]; exact shr_field L E.toEnv6 E.shift hbl ρ x y
  ite := Op.ite

theorem ev_denotes_final7 (E : Env7 env sig P) (Op : Open7 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy)
    (hP : PWf sig P) {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  ev_denotes_final6 L E.toEnv6 (open6_of L E Op hbl) hbl hP h hw he

end Bridge.Final7
