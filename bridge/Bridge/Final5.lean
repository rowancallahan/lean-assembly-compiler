/- Bridge.Final5: all nine prelude ops discharged (Len, Push, Index, Bytes).  `Open5` = what remains open:
`.bin` for −,×,&,|,<<,>> (value and head typing) and `ite` on Nat operands / `dropHead`-affected `<` (3 resp. 0
occurrences in C).

STATUS: proved, no sorry. -/
import Bridge.Bytes

namespace Bridge.Final5
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm Bridge.Final Bridge.Final3 Bridge.Final4
  Bridge.Index Bridge.Bytes

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

structure Env5 (env : List Const) (sig : Sig) (P : Prog) : Prop extends Env4 env sig P where
  idx : IdxEnv env
  bytes : ByteEnv env

structure Open5 (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
  binTy : ∀ {ρ op n i H X Y}, op ≠ 1 → binHead op = (n, i) → n ∈ binList →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.mem X (tyS M .uw) → O.mem Y (tyS M .uw) → O.mem (O.app (O.app H X) Y) (tyS M .uw)
  iteTy : ∀ {ρ r n cmp a b c d H X Y}, ¬ doneIte n cmp a b → condX n cmp a b = (c, d) → iteOk n cmp a b →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  bin : ∀ {ρ op n i H x y z}, op ≠ 1 → binHead op = (n, i) → 1 ≤ op → op ≤ 7 → binV n x y = some z →
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

theorem open4_of (E : Env5 env sig P) (Op : Open5 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy) :
    Open4 M sig P junk where
  binTy := Op.binTy
  iteTy := Op.iteTy
  bin := Op.bin
  ite := Op.ite
  rd := fun x i => rd_field L E.toEnv4 E.idx E.bytes hbl (fun _ => M.cval "Nat" []) x i
  put := fun o v => put_field L E.toEnv4 E.bytes hbl (fun _ => M.cval "Nat" []) o v
  bget := fun b i => bget_field L E.toEnv4 E.idx hbl (fun _ => M.cval "Nat" []) b i
  bset := fun b i v => bset_field L E.toEnv4 E.idx hbl (fun _ => M.cval "Nat" []) b i v

theorem ev_denotes_final5 (E : Env5 env sig P) (Op : Open5 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy)
    (hP : PWf sig P) {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  ev_denotes_final4 L E.toEnv4 (open4_of L E Op hbl) hbl hP h hw he

end Bridge.Final5
