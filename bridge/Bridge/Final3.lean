/- Bridge.Final3: `Final` plus UInt64 `<` (IteLt).  `Open3` is what remains open: `.bin` for ops 2..7 and their head
typing, `ite` on Nat operands or with `dropHead`-affected `<` operands (none in C's `<`-ites), and the 9 prelude
ops.

STATUS: proved, no sorry. -/
import Bridge.IteLt

namespace Bridge.Final3
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm Bridge.Final Bridge.IteLt

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

/-- the ite cases discharged so far -/
def doneIte (n : Bool) (cmp : Nat) (a b : X) : Prop :=
  (n = false ∧ cmp = 1) ∨ (n = false ∧ cmp = 2 ∧ a.dropHead = a ∧ b.dropHead = b)

structure Env3 (env : List Const) (sig : Sig) (P : Prog) : Prop extends Env2 env sig P where
  lt : LtEnv env

structure Open3 (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
  binTy : ∀ {ρ op n i H X Y}, op ≠ 1 → binHead op = (n, i) → n ∈ binList →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.mem X (tyS M .uw) → O.mem Y (tyS M .uw) → O.mem (O.app (O.app H X) Y) (tyS M .uw)
  iteTy : ∀ {ρ r n cmp a b c d H X Y}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) → (cmp = 1 ∨ cmp = 2) →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  bin : ∀ {ρ op n i H x y z}, op ≠ 1 → binHead op = (n, i) → 1 ≤ op → op ≤ 7 → binV n x y = some z →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.app (O.app H (encM M (.w x))) (encM M (.w y)) = encM M (.w z)
  ite : ∀ {env r n cmp a b c d va vb H Xt Xe}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) →
    (cmp = 1 ∨ cmp = 2) → VSh (if n then .nt else .uw) va → VSh (if n then .nt else .uw) vb →
    (∀ A, D O M.cval (ρE (encM M) junk env) (trM a) A → A = encM M va) →
    (∀ B, D O M.cval (ρE (encM M) junk env) (trM b) B → B = encM M vb) →
    D O M.cval (ρE (encM M) junk env) (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem Xt (tyS M r) → O.mem Xe (tyS M r) →
    O.app (O.app H Xt) Xe = if cmpV cmp va vb then Xt else Xe
  prim : PrimFactsM O M.cval (encM M)

variable (L : SetLaws O)
include L

theorem open2_of (E : Env3 env sig P) (Op : Open3 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy) :
    Open2 M sig P junk where
  binTy := Op.binTy
  iteTy := fun {ρ r n cmp a b c d H X Y} h1 hcd hcmp ha hb hH hX hY => by
    by_cases h : n = false ∧ cmp = 2 ∧ a.dropHead = a ∧ b.dropHead = b
    · obtain ⟨rfl, rfl, ha0, hb0⟩ := h
      exact iteLtU_ty L E.toEnv2 E.lt hcd ha0 hb0 (by simpa using ha) (by simpa using hb) hH hX hY
    · exact Op.iteTy (fun hd => hd.elim h1 h) hcd hcmp ha hb hH hX hY
  bin := Op.bin
  ite := fun {env r n cmp a b c d va vb H Xt Xe} h1 hcd hcmp hva hvb iha ihb hH hXt hXe => by
    by_cases h : n = false ∧ cmp = 2 ∧ a.dropHead = a ∧ b.dropHead = b
    · obtain ⟨rfl, rfl, ha0, hb0⟩ := h
      exact iteLtU_field L E.toEnv2 E.lt hbl hcd ha0 hb0 hva hvb iha ihb hH hXt hXe
    · exact Op.ite (fun hd => hd.elim h1 h) hcd hcmp hva hvb iha ihb hH hXt hXe
  prim := Op.prim

theorem ev_denotes_final3 (E : Env3 env sig P) (Op : Open3 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy)
    (hP : PWf sig P) {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  ev_denotes_final L E.toEnv2 (open2_of L E Op hbl) hbl hP h hw he

end Bridge.Final3
