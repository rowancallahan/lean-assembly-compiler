/- Bridge.General: skeleton of the GENERAL bridge theorem (Testing/notes/DENOTES_GENERAL.md).

`general`: for ANY emitted program `o`, if con-leche accepts a stream `ds` and the open pieces hold, then every run
`Ev (progOf o) [.l inp] mainX (.l out)` is the con-leche denotation of `m` at the input, in the shape of
`Bridge.nano_input`.  Proved here: the induction over `Ev`/`EvB`/`EvL` (`ev_R`), the final step from a conversion to
the denotation (`final_of_conv`), the assembly (`general`) and the `bv` case (`case_bv`).
OPEN, as named hypotheses (no `sorry`, no `axiom`):
* `Cases`: one conversion lemma per `Ev` rule (DENOTES_GENERAL.md §2 says which exist in the library);
* `hsem`/`hthms`: `TabOk`/`EqsOk`/`ThmsOk` for the program's tables (from the generator's Bool stream checks, §3);
* `hwf`: the emitted well-formedness predicate at `mainX`. -/
import Bridge.Main

namespace Bridge.General
open ConLeche ConLeche.SetModel SetTheory Bridge Bridge.Real Bridge.ModelExists2 Bridge.Real.Engine
open Bridge.Real.NanoDen (encL LU8c u64C nm nm2)
open Bridge.Real.NanoLDen (litC u64ofC boolC boolTy)
open Bridge.Real.Tiny (natC)

universe w
variable {V : Type w} [SetTheory V]

/-- substitute closed terms for the free variables at depth `≥ d` (under binders) -/
def substD (as : List Expr) (d : Nat) : Expr → Expr
  | .bvar j => if j < d then .bvar j else as.getD (j - d) (.bvar 0)
  | .app f a => .app (substD as d f) (substD as d a)
  | .lam t b m => .lam (substD as d t) (substD as (d + 1) b) m
  | .forallE t b m => .forallE (substD as d t) (substD as (d + 1) b) m
  | e => e

/-- pointwise relation of two lists -/
inductive Pw {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | nil : Pw r [] []
  | cons {a b as bs} : r a b → Pw r as bs → Pw r (a :: as) (b :: bs)

section
-- buffers (`.b`) are encoded by the prelude's choice: left open
variable (tyB : Expr) (encB : List UInt64 → Expr)

/-- the type of a nano value's encoding -/
def tyV : ExprSpec.V → Expr
  | .w _ => u64C
  | .n _ => natC
  | .l _ => LU8c
  | .b _ => tyB
  | .p a b => .app (.app (.const (nm "Prod") [.zero, .zero]) (tyV a)) (tyV b)

/-- the closed encoding of a nano value -/
def encV : ExprSpec.V → Expr
  | .w x => u64ofC (litC x.toNat)
  | .n k => litC k
  | .l bs => encL bs
  | .b ws => encB ws
  | .p a b => .app (.app (.app (.app (.const (nm2 "Prod" "mk") [.zero, .zero]) (tyV tyB a)) (tyV tyB b)) (encV a)) (encV b)

variable (tab : Tab) (eqs : List (Expr × Expr)) (thms : List Thm) (Wf : ExprSpec.X → Prop)

/-- **the invariant**: an evaluation step is a conversion of the emitted term, with the environment's values
substituted, to the encoding of the result -/
def R (env : List ExprSpec.V) (e : ExprSpec.X) (r : ExprSpec.V) : Prop :=
  Wf e → Conv tab eqs thms [] (substD (env.map (encV tyB encB)) 0 (tr e)) (encV tyB encB r) (tyV tyB r)

/-- for a condition: its `decide` converts to the Boolean -/
def RB (env : List ExprSpec.V) (c : ExprSpec.X) (bb : Bool) : Prop :=
  ∀ d : ExprSpec.X, Wf (ExprSpec.apps (.c "Decidable.decide" []) [c, d]) →
    Conv tab eqs thms [] (substD (env.map (encV tyB encB)) 0 (tr (ExprSpec.apps (.c "Decidable.decide" []) [c, d])))
      (boolC bb) boolTy

/-- **the open pieces**: one conversion lemma per rule of `Ev`/`EvB` (`EvL` needs none) -/
structure Cases (P : ExprSpec.Prog) : Prop where
  bv {env i v} : env[i]? = some v → R tyB encB tab eqs thms Wf env (.bv i) v
  lt {env nd t v b a r} : R tyB encB tab eqs thms Wf env v a → R tyB encB tab eqs thms Wf (a :: env) b r →
    R tyB encB tab eqs thms Wf env (.lt nd t v b) r
  litU {env ls k i} :
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "OfNat.ofNat" ls) [.c "UInt64" [], .nat k, i]) (.w (UInt64.ofNat k))
  litN {env ls k i} : R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "OfNat.ofNat" ls) [.c "Nat" [], .nat k, i]) (.n k)
  bin {env n ls t1 t2 t3 i a b x y z} : ExprSpec.binV n x y = some z →
    R tyB encB tab eqs thms Wf env a (.w x) → R tyB encB tab eqs thms Wf env b (.w y) →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c n ls) [t1, t2, t3, i, a, b]) (.w z)
  iteT {env ls T c d t e r} : RB tyB encB tab eqs thms Wf env c true → R tyB encB tab eqs thms Wf env t r →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "ite" ls) [T, c, d, t, e]) r
  iteF {env ls T c d t e r} : RB tyB encB tab eqs thms Wf env c false → R tyB encB tab eqs thms Wf env e r →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "ite" ls) [T, c, d, t, e]) r
  pmk {env ls A B a b x y} : R tyB encB tab eqs thms Wf env a x → R tyB encB tab eqs thms Wf env b y →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "Prod.mk" ls) [A, B, a, b]) (.p x y)
  cases {env ls A B M v T1 T2 body x y r} : R tyB encB tab eqs thms Wf env v (.p x y) →
    R tyB encB tab eqs thms Wf (y :: x :: env) body r →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "Prod.casesOn" ls) [A, B, M, v, .lam T1 (.lam T2 body)]) r
  natZ {env ls M d z T s r} : R tyB encB tab eqs thms Wf env d (.n 0) → R tyB encB tab eqs thms Wf env z r →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "Nat.casesOn" ls) [M, d, z, .lam T s]) r
  natS {env ls M d z T s k r} : R tyB encB tab eqs thms Wf env d (.n (k + 1)) →
    R tyB encB tab eqs thms Wf (.n k :: env) s r →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "Nat.casesOn" ls) [M, d, z, .lam T s]) r
  nil {env ls T} : R tyB encB tab eqs thms Wf env (.app (.c "List.nil" ls) T) (.l [])
  prim {env n as vs r} : Pw (R tyB encB tab eqs thms Wf env) as vs → ExprSpec.prim n vs = some r →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c n []) as) r
  call {env n as vs body b r} : Pw (R tyB encB tab eqs thms Wf env) as vs → P.lookup n = some body →
    ExprSpec.strip vs.length body = some b → R tyB encB tab eqs thms Wf vs.reverse b r →
    R tyB encB tab eqs thms Wf env (ExprSpec.apps (.c n []) as) r
  bEq {env ls ls' B T I a b tr x y} : R tyB encB tab eqs thms Wf env a (.w x) → R tyB encB tab eqs thms Wf env b (.w y) →
    RB tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "Eq" ls) [B, ExprSpec.apps (.c "BEq.beq" ls') [T, I, a, b], tr]) (x == y)
  bLt {env ls T I a b x y} : R tyB encB tab eqs thms Wf env a (.w x) → R tyB encB tab eqs thms Wf env b (.w y) →
    RB tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "LT.lt" ls) [T, I, a, b]) (decide (x < y))
  bEqN {env ls ls' B T I a b tr x y} : R tyB encB tab eqs thms Wf env a (.n x) → R tyB encB tab eqs thms Wf env b (.n y) →
    RB tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "Eq" ls) [B, ExprSpec.apps (.c "BEq.beq" ls') [T, I, a, b], tr]) (x == y)
  bLtN {env ls T I a b x y} : R tyB encB tab eqs thms Wf env a (.n x) → R tyB encB tab eqs thms Wf env b (.n y) →
    RB tyB encB tab eqs thms Wf env (ExprSpec.apps (.c "LT.lt" ls) [T, I, a, b]) (decide (x < y))

variable {tyB encB tab eqs thms Wf}

mutual
/-- **the induction** (proved): every evaluation is a conversion, given the per-rule lemmas -/
theorem ev_R {P : ExprSpec.Prog} (h : Cases tyB encB tab eqs thms Wf P) :
    ∀ {env e r}, ExprSpec.Ev P env e r → R tyB encB tab eqs thms Wf env e r
  | _, _, _, .bv hi => h.bv hi
  | _, _, _, .lt h1 h2 => h.lt (ev_R h h1) (ev_R h h2)
  | _, _, _, .litU => h.litU
  | _, _, _, .litN => h.litN
  | _, _, _, .bin hb h1 h2 => h.bin hb (ev_R h h1) (ev_R h h2)
  | _, _, _, .iteT hc ht => h.iteT (evB_R h hc) (ev_R h ht)
  | _, _, _, .iteF hc he => h.iteF (evB_R h hc) (ev_R h he)
  | _, _, _, .mk h1 h2 => h.pmk (ev_R h h1) (ev_R h h2)
  | _, _, _, .cases hv hb => h.cases (ev_R h hv) (ev_R h hb)
  | _, _, _, .natZ hd hz => h.natZ (ev_R h hd) (ev_R h hz)
  | _, _, _, .natS hd hs => h.natS (ev_R h hd) (ev_R h hs)
  | _, _, _, .nil => h.nil
  | _, _, _, .prim ha hp => h.prim (evL_R h ha) hp
  | _, _, _, .call ha hl hs hb => h.call (evL_R h ha) hl hs (ev_R h hb)
theorem evB_R {P : ExprSpec.Prog} (h : Cases tyB encB tab eqs thms Wf P) :
    ∀ {env c bb}, ExprSpec.EvB P env c bb → RB tyB encB tab eqs thms Wf env c bb
  | _, _, _, .eq h1 h2 => h.bEq (ev_R h h1) (ev_R h h2)
  | _, _, _, .lt h1 h2 => h.bLt (ev_R h h1) (ev_R h h2)
  | _, _, _, .eqN h1 h2 => h.bEqN (ev_R h h1) (ev_R h h2)
  | _, _, _, .ltN h1 h2 => h.bLtN (ev_R h h1) (ev_R h h2)
theorem evL_R {P : ExprSpec.Prog} (h : Cases tyB encB tab eqs thms Wf P) :
    ∀ {env as vs}, ExprSpec.EvL P env as vs → Pw (R tyB encB tab eqs thms Wf env) as vs
  | _, _, _, .nil => .nil
  | _, _, _, .cons h1 h2 => .cons (ev_R h h1) (evL_R h h2)
end

/-- **the `bv` case** (proved), from typing of the encodings (`encTy`, open for pairs and buffers) -/
theorem case_bv (encTy : ∀ v, HasTy tab eqs [] (encV tyB encB v) (tyV tyB v)) {env : List ExprSpec.V} {i : Nat}
    {v : ExprSpec.V} (hi : env[i]? = some v) : R tyB encB tab eqs thms Wf env (.bv i) v := by
  intro _
  have : (env.map (encV tyB encB)).getD i (.bvar 0) = encV tyB encB v := by
    simp [List.getD_eq_getElem?_getD, hi]
  simp only [tr, substD, Nat.not_lt_zero, if_false, Nat.sub_zero, this]
  exact .refl (encTy v)
end

/-- **the last step** (proved): a conversion of `m` at the encoded input to the encoded output gives the
denotation statement of `Bridge.nano_input` -/
theorem final_of_conv {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (acc : Cached.checkDecls .verified pins ds = .ok env) {M : Model V env} (hP : CvalParams M)
    (hnat : natLitSupported env = true) {tab : Tab} (htab : TabOk M tab) {eqs : List (Expr × Expr)}
    (heqs : EqsOk M eqs) {thms : List Thm} (hthms : ThmsOk ds tab eqs thms) {inp out : List UInt8}
    (c : Conv tab eqs thms [] (.app (.const (nm "m") []) (encL inp)) (encL out) LU8c)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    ∃ x, Denotes M.cval env φ ρ (encL inp) x ∧
      ∀ Y, Denotes M.cval env φ ρ (encL out) Y → Denotes M.cval env φ (push x ρ) (tr NanoTiny.mainX) Y := by
  have h0 : GammaOk M φ ρ ([] : List Expr) := fun _ _ h => by simp at h
  obtain ⟨X, -, d1, d2, -, -⟩ := conv_sound acc hP hnat htab heqs hthms h0 c
  obtain ⟨F, x, dF, dx, rfl⟩ := app_inv d1
  refine ⟨x, dx, fun Y hY => ?_⟩
  obtain rfl := Denotes_functional hY d2
  rw [NanoDen.tr_mainX]
  cases dF with
  | const hf hl => exact .app (.const hf hl) .bvar

/-- **THE GENERAL THEOREM (skeleton)**: for any emitted program `o` and any accepted stream, given the open
pieces as hypotheses, every run of `m` is the con-leche denotation of `m` at the input. -/
theorem general (V : Type w) [SetTheory V] (o : List (String × ExprSpec.X × ExprSpec.X))
    {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env) (hpin : natPin ds = true)
    {tyB : Expr} {encB : List UInt64 → Expr} {tab : Tab} {eqs : List (Expr × Expr)} {thms : List Thm}
    {Wf : ExprSpec.X → Prop}
    (hsem : ∀ M : Model V env, CvalParams M → TabOk M tab ∧ EqsOk M eqs)
    (hthms : ThmsOk ds tab eqs thms)
    (hcases : Cases tyB encB tab eqs thms Wf (ExprSpec.progOf o))
    (hwf : Wf NanoTiny.mainX) :
    ∃ M : Model V env, CvalParams M ∧
      ∀ (inp out : List UInt8), ExprSpec.Ev (ExprSpec.progOf o) [.l inp] NanoTiny.mainX (.l out) →
        ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), ∃ x,
          Denotes M.cval env φ ρ (encL inp) x ∧
          ∀ Y, Denotes M.cval env φ ρ (encL out) Y → Denotes M.cval env φ (push x ρ) (tr NanoTiny.mainX) Y := by
  obtain ⟨b, nP, hb, hpin'⟩ := natPin_of hpin
  have hnat : natLitSupported env = true := NatLit.natLit_of_accepted V accepted hb hpin'
  obtain ⟨M, hP⟩ := model_exists' V pins ds env accepted
  obtain ⟨htab, heqs⟩ := hsem M hP
  refine ⟨M, hP, fun inp out hev φ ρ => ?_⟩
  have c := ev_R hcases hev hwf
  rw [NanoDen.tr_mainX] at c
  simp only [substD, List.map, Nat.not_lt_zero, if_false, List.getD_cons_zero] at c
  exact final_of_conv accepted hP hnat htab heqs hthms c φ ρ

end Bridge.General
