/- Bridge.Assembly: everything plugged together in the trimmed model.  `ev_denotes_assembled`: for every
well-formed term (and well-formed program), Ev's value is what the term denotes, in EVERY model of an env that
holds the listed constants and theorems (`Env`), given ONLY the still-open facts `Open`
(`.bin` arithmetic, `ite` conditions, the 9 prelude ops, and the typing of the `bin`/`ite` heads).

STATUS: proved, no sorry. -/
import Bridge.Call

namespace Bridge.Asm
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota Bridge.Iota2 Bridge.Call

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

/-- the prims' Lean types (monomorphic arrows) -/
def PrimTyEnv (env : List Const) : Prop :=
  ∀ {p n ps r}, primInfo p = (n, ps, r) → p ≠ 5 → p ≠ 0 → p ≤ 9 → HasTy env n [] (piPs (ps.map psSh) r)

/-- what the env must hold (all discharged above): constructors and their types, literal and iota theorems,
`Buf = List UInt64`, `bnew : Buf`, the prims' types, the program's defs with their `f = value` theorems -/
structure Env (env : List Const) (sig : Sig) (P : Prog) : Prop where
  enc : EncEnv env
  lit : LitEnv env
  instN : InstN env
  brLitN : HasTy env "br_litN" [] (piN [(tNat, false)] (eqE 1 tNat
      (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0)))
      (.bvar 0)))
  casesN : CasesNEnv env
  iota : IotaEnv env
  casesP : CasesPEnv env
  prodC : ProdCEnv env
  bnew : HasTy env "bnew" [] (.const "Buf" [])
  primTy : PrimTyEnv env
  defs : DefEnv env sig P

/-- the still-open facts -/
structure Open (M : Model O env) (sig : Sig) (P : Prog) (junk : S) : Prop where
  binTy : ∀ {ρ op n i H X Y}, binHead op = (n, i) → n ∈ binList →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.mem X (tyS M .uw) → O.mem Y (tyS M .uw) → O.mem (O.app (O.app H X) Y) (tyS M .uw)
  iteTy : ∀ {ρ r n cmp a b c d H X Y}, condX n cmp a b = (c, d) → (cmp = 1 ∨ cmp = 2) →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  bin : ∀ {ρ op n i H x y z}, binHead op = (n, i) → 1 ≤ op → op ≤ 7 → binV n x y = some z →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.app (O.app H (encM M (.w x))) (encM M (.w y)) = encM M (.w z)
  ite : ∀ {env r n cmp a b c d va vb H Xt Xe}, condX n cmp a b = (c, d) → (cmp = 1 ∨ cmp = 2) →
    VSh (if n then .nt else .uw) va → VSh (if n then .nt else .uw) vb →
    (∀ A, D O M.cval (ρE (encM M) junk env) (trM a) A → A = encM M va) →
    (∀ B, D O M.cval (ρE (encM M) junk env) (trM b) B → B = encM M vb) →
    D O M.cval (ρE (encM M) junk env) (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem Xt (tyS M r) → O.mem Xe (tyS M r) →
    O.app (O.app H Xt) Xe = if cmpV cmp va vb then Xt else Xe
  prim : PrimFactsM O M.cval (encM M)

variable (L : SetLaws O)
include L

theorem headTy (E : Env env sig P) (Op : Open M sig P junk) : HeadTy M sig where
  litU := fun hk hR => litU_ty L E.enc E.lit hk hR
  litN := fun hR => litN_ty L E.enc E.lit E.instN hR
  bin := Op.binTy
  ite := Op.iteTy
  pair := fun hH hX hY => pair_ty L E.enc hH hX hY
  cases := fun hH hP hL => cases_ty L E.enc E.casesP hH hP hL
  natC := fun hH hN hZ hL => natC_ty L E.enc E.casesN hH hN hZ hL
  nil := fun hR => nil_ty L E.enc hR
  prim := fun {_ _ _ r _} hp _ h0 h1 h2 hXs =>
    app_piS L r (mem_ty M L (E.primTy hp h0 h1 h2) (ρ := fun _ => M.cval "Nat" []) (piPs_D r _)) hXs
  bnew := bnew_ty L E.bnew (ρ := fun _ => M.cval "Nat" [])
  call := fun hs _ hXs => call_ty L E.defs hs hXs

theorem facts (E : Env env sig P) (Op : Open M sig P junk) (hP : PWf sig P) :
    FactsM O M.cval sig P (encM M) junk (tyS M) where
  letβ := fun {env Γ s v b a R} _ _ _ hva ih hR => by
    rw [ρE_cons]; exact letβ_field (M := M) (L := L) E.enc hva ih hR
  litU := fun hk hR => litU_field M L E.lit hk hR
  litN := fun hR => litN_field L E.enc E.lit E.instN E.brLitN hR
  bin := Op.bin
  ite := Op.ite
  pair := fun hx hy hH => pair_field M L hx hy hH
  cases := fun hx hy hH hLD hL hR => cases_field L E.enc E.casesP E.prodC hx hy hH hLD hL hR
  natZ := fun hH hZ hL => natZ_field L E.enc E.casesN E.iota hH hZ hL
  natS := fun hH hLD hZ hL hR => natS_field L E.enc E.casesN E.iota hH hLD hZ hL hR
  nil := fun hR => nil_field M hR
  prim := Op.prim
  call := fun hs hvs hl hst ih => call_field L E.enc E.defs (headTy L E Op) hP hs hvs hl hst ih

/-- **Ev ⇒ Denotes, assembled** (trimmed model): only `Open` remains as a hypothesis -/
theorem ev_denotes_assembled (E : Env env sig P) (Op : Open M sig P junk) (hP : PWf sig P)
    {envV : List ExprSpec.V} {e : X} {v : ExprSpec.V} (h : Ev P envV e v) {Γ : List Sh} {s : Sh}
    (hw : Wf sig Γ e s) (he : Typed.Fa2 VSh Γ envV) :
    ∀ R, D O M.cval (ρE (encM M) junk envV) (trM e) R → R = encM M v :=
  EvM.ev_denotes (facts L E Op hP) (typingW L E.enc (headTy L E Op)) hP h hw he

end Bridge.Asm
