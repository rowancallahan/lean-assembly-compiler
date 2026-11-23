/- Bridge.Final4: `Final3` plus the prelude ops `len'`, `len`, `bsize`, `bnew`, `bpush` (Len, Push).  `Open4` is what
remains open: `.bin` for −,×,&,|,<<,>> (and head typing), `ite` on Nat operands / `dropHead`-affected `<`, and the
prelude ops `rd`, `put`, `bget`, `bset`.

STATUS: proved, no sorry. -/
import Bridge.Push

namespace Bridge.Final4
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.Asm Bridge.Add Bridge.Final Bridge.Final3
  Bridge.Len Bridge.Push

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

structure Env4 (env : List Const) (sig : Sig) (P : Prog) : Prop extends Env3 env sig P where
  len : LenEnv env
  push : PushEnv env

structure Open4 (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
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
  rd : ∀ x i, O.app (O.app (M.cval "rd" []) (encM M (.l x))) (encM M (.w i)) = encM M (.w (x.getD i.toNat 0).toUInt64)
  put : ∀ o v, O.app (O.app (M.cval "put" []) (encM M (.l o))) (encM M (.w v)) = encM M (.l (o ++ [v.toUInt8]))
  bget : ∀ b i, O.app (O.app (M.cval "bget" []) (encM M (.b b))) (encM M (.w i)) = encM M (.w (b.getD i.toNat 0))
  bset : ∀ b i v, O.app (O.app (O.app (M.cval "bset" []) (encM M (.b b))) (encM M (.w i))) (encM M (.w v)) =
    encM M (.b (b.set i.toNat v))

variable (L : SetLaws O)
include L

theorem open3_of (E : Env4 env sig P) (Op : Open4 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy) :
    Open3 M sig P junk where
  binTy := Op.binTy
  iteTy := Op.iteTy
  bin := Op.bin
  ite := Op.ite
  prim :=
    { rd := Op.rd
      len := fun x => len_field L E.toEnv E.len E.add hbl (fun _ => M.cval "Nat" []) x
      len' := fun x => len'_field L E.toEnv E.len (fun _ => M.cval "Nat" []) x
      put := Op.put
      bnew := bnew_field L E.toEnv E.push (fun _ => M.cval "Nat" [])
      bsize := fun b => bsize_field L E.toEnv E.len E.add hbl (fun _ => M.cval "Nat" []) b
      bget := Op.bget
      bset := Op.bset
      bpush := fun b v => bpush_field L E.toEnv E.push (fun _ => M.cval "Nat" []) b v }

theorem ev_denotes_final4 (E : Env4 env sig P) (Op : Open4 M sig P junk) (hbl : HasTy env "br_litN" [] brLitNTy)
    (hP : PWf sig P) {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  ev_denotes_final3 L E.toEnv3 (open3_of L E Op hbl) hbl hP h hw he

end Bridge.Final4
