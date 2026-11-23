/- Bridge.EvMini: the Ev ⇒ Denotes induction (EvBridge.lean) restated over the trimmed con-leche model of
MiniModel.lean, so the induction and the derived per-constant facts (MiniModel `litU_fact`, below `pair`/`nil`)
live in ONE model.  `trM` maps nano's Expr to the trimmed terms; data binders get `pw = false` (the regime the
checker computes for them; a real-bridge obligation, DENOTES_SPIKE §3).

STATUS: proved, no sorry (the `FactsM` fields are hypotheses; some are discharged below). -/
import Bridge.MiniModel
import Bridge.Typed

namespace Bridge.EvM
open ExprSpec ParSpec Bridge.Typed Bridge.Mini

/-- nano's Expr → trimmed terms; `let` as a beta-redex -/
def trM : X → E
  | .bv i => .bvar i
  | .c n ls => .const n ls
  | .app f a => .app (trM f) (trM a)
  | .lam t b => .lam (trM t) (trM b) false
  | .pi t b => .forallE (trM t) (trM b) false
  | .lt _ t v b => .app (.lam (trM t) (trM b) false) (trM v)
  | .nat k => .lit k

theorem trM_apps (f : X) : ∀ as : List X, trM (apps f as) = (as.map trM).foldl E.app (trM f)
  | [] => rfl
  | a :: as => trM_apps (.app f a) as

def ρE {S : Type} (enc : ExprSpec.V → S) (junk : S) (env : List ExprSpec.V) (i : Nat) : S :=
  (env[i]?.map enc).getD junk

theorem ρE_cons {S : Type} (enc : ExprSpec.V → S) (junk : S) (a : ExprSpec.V) (env : List ExprSpec.V) :
    ρE enc junk (a :: env) = push (enc a) (ρE enc junk env) := by
  funext i; cases i <;> rfl

inductive Fa2D {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | nil : Fa2D r [] []
  | cons {a b as bs} : r a b → Fa2D r as bs → Fa2D r (a :: as) (b :: bs)

theorem Fa2D_map {α β γ : Type} {r : β → γ → Prop} {f : α → β} :
    ∀ {as : List α} {cs : List γ}, Fa2D r (as.map f) cs → Fa2D (fun a c => r (f a) c) as cs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons h (Fa2D_map t)

section
variable {S : Type} {O : SetOps S} {cval : String → List Nat → S}

theorem D_const_inv {ρ : Nat → S} {n : String} {ls : List Nat} {R : S} (h : D O cval ρ (.const n ls) R) :
    R = cval n ls := by cases h; rfl

theorem D_foldl_inv {ρ : Nat → S} : ∀ (as : List E) (f : E) (R : S), D O cval ρ (as.foldl E.app f) R →
    ∃ F Xs, D O cval ρ f F ∧ Fa2D (D O cval ρ) as Xs ∧ R = Xs.foldl O.app F
  | [], f, R, h => ⟨R, [], h, .nil, rfl⟩
  | a :: as, f, R, h => by
    obtain ⟨F', Xs, hF', hXs, rfl⟩ := D_foldl_inv as (.app f a) R h
    obtain ⟨F, X, hF, hX, rfl⟩ := app_inv hF'
    exact ⟨F, X :: Xs, hF, .cons hX hXs, rfl⟩

theorem two_args {ρ : Nat → S} {g : X} {l : List X} {a b : X} {R : S}
    (h : D O cval ρ (trM (apps g (l ++ [a, b]))) R) :
    ∃ H A B, D O cval ρ (trM (apps g l)) H ∧ D O cval ρ (trM a) A ∧ D O cval ρ (trM b) B ∧
      R = O.app (O.app H A) B := by
  rw [show apps g (l ++ [a, b]) = .app (.app (apps g l) a) b by simp [apps, List.foldl_append]] at h
  obtain ⟨F1, B, h1, hb, rfl⟩ := app_inv h
  obtain ⟨H, A, hH, ha, rfl⟩ := app_inv h1
  exact ⟨H, A, B, hH, ha, hb, rfl⟩

/-- `Facts.prim` per op, over the trimmed model -/
structure PrimFactsM (O : SetOps S) (cval : String → List Nat → S) (enc : ExprSpec.V → S) : Prop where
  rd : ∀ x i, O.app (O.app (cval "rd" []) (enc (.l x))) (enc (.w i)) = enc (.w (x.getD i.toNat 0).toUInt64)
  len : ∀ x, O.app (cval "len" []) (enc (.l x)) = enc (.w x.length.toUInt64)
  len' : ∀ x, O.app (cval "len'" []) (enc (.l x)) = enc (.n x.length)
  put : ∀ o v, O.app (O.app (cval "put" []) (enc (.l o))) (enc (.w v)) = enc (.l (o ++ [v.toUInt8]))
  bnew : cval "bnew" [] = enc (.b [])
  bsize : ∀ b, O.app (cval "bsize" []) (enc (.b b)) = enc (.w b.length.toUInt64)
  bget : ∀ b i, O.app (O.app (cval "bget" []) (enc (.b b))) (enc (.w i)) = enc (.w (b.getD i.toNat 0))
  bset : ∀ b i v, O.app (O.app (O.app (cval "bset" []) (enc (.b b))) (enc (.w i))) (enc (.w v)) =
    enc (.b (b.set i.toNat v))
  bpush : ∀ b v, O.app (O.app (cval "bpush" []) (enc (.b b))) (enc (.w v)) = enc (.b (b ++ [v]))

theorem PrimFactsM.prim {enc : ExprSpec.V → S} (F : PrimFactsM O cval enc) :
    ∀ {n : String} {vs : List ExprSpec.V} {r : ExprSpec.V}, ExprSpec.prim n vs = some r →
      (vs.map enc).foldl O.app (cval n []) = enc r := by
  intro n vs r h
  unfold ExprSpec.prim at h
  split at h <;> (try cases h) <;> simp only [List.map, List.foldl]
  · exact F.rd _ _
  · exact F.len _
  · exact F.len' _
  · exact F.put _ _
  · exact F.bnew
  · exact F.bsize _
  · exact F.bget _ _
  · exact F.bset _ _ _
  · exact F.bpush _ _
end

variable {S : Type} {O : SetOps S} {cval : String → List Nat → S}

/-- the open per-constant lemmas, canonical arguments only.  `ρ` is any variable environment; `ρE env` the one
of an Ev environment. -/
structure FactsM (O : SetOps S) (cval : String → List Nat → S) (sig : Sig) (P : Prog) (enc : ExprSpec.V → S) (junk : S) : Prop where
  /-- `have x : shTy s := v; b` as `(λ (shTy s). b) v`: beta + `enc a ∈ ⟦shTy s⟧` -/
  letβ : ∀ {env Γ s v b a R}, Typed.Fa2 VSh Γ env → Wf sig Γ v s → Ev P env v a → VSh s a →
    (∀ X, D O cval (ρE enc junk env) (trM v) X → X = enc a) →
    D O cval (ρE enc junk env) (trM (.lt true (shTy s) v b)) R →
    D O cval (ρE enc junk (a :: env)) (trM b) R
  litU : ∀ {ρ k R}, k < UInt64.size → D O cval ρ
    (trM (apps (.c "OfNat.ofNat" [0]) [U, .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)])) R →
    R = enc (.w (UInt64.ofNat k))
  litN : ∀ {ρ k R}, D O cval ρ
    (trM (apps (.c "OfNat.ofNat" [0]) [.c "Nat" [], .nat k, .app (.c "instOfNatNat" []) (.nat k)])) R →
    R = enc (.n k)
  bin : ∀ {ρ op n i H x y z}, binHead op = (n, i) → 1 ≤ op → op ≤ 7 → binV n x y = some z →
    D O cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.app (O.app H (enc (.w x))) (enc (.w y)) = enc (.w z)
  /-- `ite` with the emitted condition/instance; the condition's truth value comes from its `EvB` -/
  ite : ∀ {env r n cmp a b c d bc H Xt Xe}, condX n cmp a b = (c, d) → (cmp = 1 ∨ cmp = 2) → EvB P env c bc →
    D O cval (ρE enc junk env) (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.app (O.app H Xt) Xe = if bc then Xt else Xe
  pair : ∀ {ρ A B H x y}, VSh A x → VSh B y →
    D O cval ρ (trM (apps (.c "Prod.mk" [0, 0]) [shTy A, shTy B])) H →
    O.app (O.app H (enc x)) (enc y) = enc (.p x y)
  cases : ∀ {ρ l r Rs body H L x y R}, VSh l x → VSh r y →
    D O cval ρ (trM (apps (.c "Prod.casesOn" [1, 0, 0]) [shTy l, shTy r, .lam (shTy (.p l r)) (shTy Rs)])) H →
    D O cval ρ (trM (.lam (shTy l) (.lam (shTy r) body))) L → R = O.app (O.app H (enc (.p x y))) L →
    D O cval (push (enc y) (push (enc x) ρ)) (trM body) R
  natZ : ∀ {ρ Rs H Z L}, D O cval ρ (trM (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy Rs)])) H →
    O.app (O.app (O.app H (enc (.n 0))) Z) L = Z
  natS : ∀ {ρ Rs s H Z L k R},
    D O cval ρ (trM (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy Rs)])) H →
    D O cval ρ (trM (.lam (.c "Nat" []) s)) L → R = O.app (O.app (O.app H (enc (.n (k + 1)))) Z) L →
    D O cval (push (enc (.n k)) ρ) (trM s) R
  nil : ∀ {ρ R}, D O cval ρ (trM (apps (.c "List.nil" [0]) [.c "UInt8" []])) R → R = enc (.l [])
  prim : PrimFactsM O cval enc
  /-- a program def: its stored equation + typing of the (shaped) arguments; `hb` = the IH for the body -/
  call : ∀ {n ps r vs body b v}, sig n = some (ps, r) → Typed.Fa2 VSh ps vs → P.lookup n = some body →
    strip vs.length body = some b →
    (∀ R, D O cval (ρE enc junk vs.reverse) (trM b) R → R = enc v) →
    (vs.map enc).foldl O.app (cval n []) = enc v

theorem fa2_map_tr {ρ : Nat → S} {as : List X} {Xs : List S}
    (h : Fa2D (D O cval ρ) (as.map trM) Xs) :
    Fa2D (fun a X => D O cval ρ (trM a) X) as Xs := Fa2D_map h

/-- **Ev agrees with Denotes on well-formed terms** (uniqueness form: whatever `tr e` denotes is `enc v`). -/
theorem ev_denotes {sig : Sig} {P : Prog} {enc : ExprSpec.V → S} {junk : S}
    (F : FactsM O cval sig P enc junk) (hP : PWf sig P) {env e v} (h : Ev P env e v) :
    ∀ {Γ s}, Wf sig Γ e s → Typed.Fa2 VSh Γ env →
      ∀ R, D O cval (ρE enc junk env) (trM e) R → R = enc v := by
  refine Ev.rec
    (motive_1 := fun env e v _ => ∀ {Γ s}, Wf sig Γ e s → Typed.Fa2 VSh Γ env →
      ∀ R, D O cval (ρE enc junk env) (trM e) R → R = enc v)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun env as vs _ => ∀ {Γ ss}, WfL sig Γ as ss → Typed.Fa2 VSh Γ env →
      ∀ Xs, Fa2D (fun a X => D O cval (ρE enc junk env) (trM a) X) as Xs → Xs = vs.map enc)
    ?bv ?lt ?litU ?litN ?bin ?iteT ?iteF ?mk ?cases ?natZ ?natS ?nil ?prim ?call
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    ?lnil ?lcons h
  case bv =>
    intro env i v hi Γ s _ _ R hR
    cases hR; simp [ρE, hi]
  case lt =>
    intro env nd t vx b a r hv _ ihv ihb Γ s hw he R hR
    cases hw with
    | lt h1 h2 h3 =>
      unif
      have ha := ev_shape hP hv h2 he
      exact ihb h3 (.cons ha he) R (F.letβ he h2 hv ha (ihv h2 he) hR)
    | _ => kill
  case litU =>
    intro env ls k i Γ s hw he R hR
    cases hw with
    | litU h1 h2 => unif; exact F.litU h2 hR
    | _ => kill
  case litN =>
    intro env ls k i Γ s hw he R hR
    cases hw with
    | litN => unif; exact F.litN hR
    | _ => kill
  case bin =>
    intro env n ls t1 t2 t3 i a b x y z hz _ _ iha ihb Γ s hw he R hR
    have hn := binV_names hz
    cases hw with
    | bin h1 h2 _ h3 h4 h5 h6 =>
      unif
      obtain ⟨H, A, B, hH, hA, hB, rfl⟩ := two_args (l := [U, U, U, _]) hR
      rw [iha h5 he A hA, ihb h6 he B hB]; exact F.bin h2 h3 h4 hz hH
    | _ => kill
  case iteT =>
    intro env ls T c d t e r hc _ _ iht Γ s hw he R hR
    cases hw with
    | ite h1 h2 h3 _ _ h5 _ =>
      unif
      obtain ⟨H, A, B, hH, hA, hB, rfl⟩ := two_args (l := [_, _, _]) hR
      rw [F.ite h2 h3 hc hH]; exact iht h5 he A hA
    | _ => kill
  case iteF =>
    intro env ls T c d t e r hc _ _ ihe Γ s hw he R hR
    cases hw with
    | ite h1 h2 h3 _ _ _ h6 =>
      unif
      obtain ⟨H, A, B, hH, hA, hB, rfl⟩ := two_args (l := [_, _, _]) hR
      rw [F.ite h2 h3 hc hH]; exact ihe h6 he B hB
    | _ => kill
  case mk =>
    intro env ls A B a b x y ha hb iha ihb Γ s hw he R hR
    cases hw with
    | mk h1 h2 h3 =>
      unif
      obtain ⟨H, X1, X2, hH, h1', h2', rfl⟩ := two_args (l := [_, _]) hR
      rw [iha h2 he X1 h1', ihb h3 he X2 h2']
      exact F.pair (ev_shape hP ha h2 he) (ev_shape hP hb h3 he) hH
    | _ => kill
  case cases =>
    intro env ls A B M vx T1 T2 body x y r hv hb ihv ihb Γ s hw he R hR
    cases hw with
    | cases h1 h2 h3 =>
      unif
      have hp := ev_shape hP hv h2 he
      cases hp with
      | p hx hy =>
        obtain ⟨H, X1, L, hH, h1', hL, rfl⟩ := two_args (l := [_, _, _]) hR
        rw [ihv h2 he X1 h1'] at *
        refine ihb h3 (.cons hy (.cons hx he)) _ ?_
        rw [ρE_cons, ρE_cons]; exact F.cases hx hy hH hL rfl
    | _ => kill
  case natZ =>
    intro env ls M d z T sx r hd hz ihd ihz Γ s' hw he R hR
    cases hw with
    | natCases h1 h2 h3 h4 =>
      unif
      rw [show [X.lam (.c "Nat" []) (shTy _), _, _, _] = [X.lam (.c "Nat" []) (shTy _), _] ++ [_, _] from rfl] at hR
      obtain ⟨H1, Z, L, hH1, hZ, hL, rfl⟩ := two_args hR
      obtain ⟨H, X1, hH, h1', rfl⟩ := app_inv hH1
      rw [ihd h2 he X1 h1', F.natZ hH]; exact ihz h3 he Z hZ
    | _ => kill
  case natS =>
    intro env ls M d z T sx k r hd hs ihd ihs Γ s' hw he R hR
    cases hw with
    | natCases h1 h2 h3 h4 =>
      unif
      rw [show [X.lam (.c "Nat" []) (shTy _), _, _, _] = [X.lam (.c "Nat" []) (shTy _), _] ++ [_, _] from rfl] at hR
      obtain ⟨H1, Z, L, hH1, hZ, hL, rfl⟩ := two_args hR
      obtain ⟨H, X1, hH, h1', rfl⟩ := app_inv hH1
      rw [ihd h2 he X1 h1']
      refine ihs h4 (.cons (.nt _) he) _ ?_
      rw [ρE_cons]; exact F.natS hH hL rfl
    | _ => kill
  case nil =>
    intro env ls T Γ s hw he R hR
    rw [nil_apps] at hw
    cases hw with
    | nil h1 => unif; exact F.nil hR
    | _ => kill
  case prim =>
    intro env n as vs r hl hp ihl Γ s hw he R hR
    have hn := prim_names hp
    rw [trM_apps] at hR
    obtain ⟨H, Xs, hH, hXs, rfl⟩ := D_foldl_inv _ _ _ hR
    cases hw with
    | prim h1 h2 _ h3 h4 h5 h6 =>
      unif
      rw [D_const_inv hH, ihl h6 he Xs (fa2_map_tr hXs)]; exact F.prim.prim hp
    | bnew h1 =>
      unif
      cases hl; cases hXs; simp [ExprSpec.prim] at hp; subst hp
      rw [D_const_inv hH]; exact F.prim.bnew
    | _ => kill
  case call =>
    intro env n as vs body b r hl hlook hstrip hb ihl ihb Γ s hw he R hR
    obtain ⟨ps, r', b', hs, hst, hwb⟩ := hP.defs hlook
    have hres := hP.sig_res hs
    rw [trM_apps] at hR
    obtain ⟨H, Xs, hH, hXs, rfl⟩ := D_foldl_inv _ _ _ hR
    cases hw with
    | call h1 _ h2 h3 =>
      unif
      obtain ⟨rfl, rfl⟩ := hP.sig_fun hs h2
      have hvs := evL_shape_of hP hl h3 he
      rw [D_const_inv hH, ihl h3 he Xs (fa2_map_tr hXs)]
      rw [fa2_len hvs, hstrip] at hst; cases hst
      exact F.call hs hvs hlook hstrip (ihb hwb (fa2_reverse hvs))
    | _ => kill
  case lnil =>
    intro env Γ ss hw he Xs hXs
    cases hXs; rfl
  case lcons =>
    intro env a as v vs _ _ iha ihl Γ ss hw he Xs hXs
    cases hw with
    | cons h1 h2 =>
      cases hXs with
      | cons hX hXs => rw [iha h1 he _ hX, ihl h2 he _ hXs]; rfl


/-! ## the encoding, and the fields that are discharged here -/

section Enc
variable {S : Type} {O : SetOps S} {env : List Const} (M : Model O env)

/-- canonical lists: constructor terms `List.cons.{0} T a l` / `List.nil.{0} T` -/
def listEnc {α : Type} (T : S) (f : α → S) : List α → S
  | [] => O.app (M.cval "List.nil" [0]) T
  | a :: l => O.app (O.app (O.app (M.cval "List.cons" [0]) T) (f a)) (listEnc T f l)

/-- the set of a value's type (`⟦shTy s⟧` for its shape `s`) -/
def tyE : ExprSpec.V → S
  | .w _ => M.cval "UInt64" []
  | .n _ => M.cval "Nat" []
  | .l _ => O.app (M.cval "List" [0]) (M.cval "UInt8" [])
  | .b _ => M.cval "Buf" []
  | .p x y => O.app (O.app (M.cval "Prod" [0, 0]) (tyE x)) (tyE y)

/-- **the encoding of nano values** (DENOTES_SPIKE §2): canonical constructor terms over `ofNat` numerals -/
def encM : ExprSpec.V → S
  | .w x => O.app (M.cval "UInt64.ofNat" []) (natEnc M x.toNat)
  | .n k => natEnc M k
  | .l bs => listEnc M (M.cval "UInt8" []) (fun b => O.app (M.cval "UInt8.ofNat" []) (natEnc M b.toNat)) bs
  | .b ws => listEnc M (M.cval "UInt64" []) (fun w => O.app (M.cval "UInt64.ofNat" []) (natEnc M w.toNat)) ws
  | .p x y => O.app (O.app (O.app (O.app (M.cval "Prod.mk" [0, 0]) (tyE M x)) (tyE M y)) (encM x)) (encM y)

/-- `⟦shTy s⟧` is the type set of every value of shape `s` -/
theorem shTy_denotes {ρ : Nat → S} : ∀ {s v}, VSh s v → D O M.cval ρ (trM (shTy s)) (tyE M v)
  | _, _, .uw _ => .const
  | _, _, .nt _ => .const
  | _, _, .ls _ => .app .const .const
  | _, _, .bf _ => .const
  | _, _, .p hx hy => .app (.app .const (shTy_denotes hx)) (shTy_denotes hy)

variable (L : SetLaws O)
include L

/-- `FactsM.litU`, discharged (MiniModel `litU_fact` + `k < 2^64`) -/
theorem litU_field (H : LitEnv env) {ρ : Nat → S} {k : Nat} {R : S} (hk : k < UInt64.size)
    (hR : D O M.cval ρ (trM (apps (.c "OfNat.ofNat" [0]) [U, .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)])) R) :
    R = encM M (.w (UInt64.ofNat k)) := by
  rw [litU_fact L M H ρ k hR]
  have : (UInt64.ofNat k).toNat = k := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hk
  simp only [encM, this]

omit L in
/-- `FactsM.nil`, discharged: a constructor term IS its encoding -/
theorem nil_field {ρ : Nat → S} {R : S}
    (hR : D O M.cval ρ (trM (apps (.c "List.nil" [0]) [.c "UInt8" []])) R) : R = encM M (.l []) := by
  obtain ⟨F, X, hF, hX, rfl⟩ := app_inv hR
  cases hF; cases hX; rfl

/-- `FactsM.pair`, discharged: the type arguments are the shapes' type sets -/
theorem pair_field {ρ : Nat → S} {A B : Sh} {x y : ExprSpec.V} {H : S} (hx : VSh A x) (hy : VSh B y)
    (hH : D O M.cval ρ (trM (apps (.c "Prod.mk" [0, 0]) [shTy A, shTy B])) H) :
    O.app (O.app H (encM M x)) (encM M y) = encM M (.p x y) := by
  obtain ⟨F, Bv, hF, hB, rfl⟩ := app_inv hH
  obtain ⟨G, Av, hG, hA, rfl⟩ := app_inv hF
  cases hG
  rw [D_functional L hA (shTy_denotes M hx), D_functional L hB (shTy_denotes M hy)]; rfl

end Enc

/-! ## typing of the encoding (task 3, the con-leche half, in the trimmed model) -/

section Typing
variable {S : Type} {O : SetOps S} {env : List Const} (M : Model O env) (L : SetLaws O)

/-- the stored constant `n`, used at levels `ls`, has the type `T` there -/
def HasTy (env : List Const) (n : String) (ls : List Nat) (T : E) : Prop := ∃ ty, (n, ty) ∈ env ∧ ty ls = T

include L in
theorem mem_ty {n : String} {ls : List Nat} {T : E} (h : HasTy env n ls T) {ρ : Nat → S} {Tv : S}
    (hT : D O M.cval ρ T Tv) : O.mem (M.cval n ls) Tv := by
  obtain ⟨ty, hc, rfl⟩ := h
  exact mem_closed L M hc hT

/-- the constructors' Lean types (level 0), and `Buf = List UInt64` (a stored theorem, `rfl`) -/
structure EncEnv (env : List Const) : Prop where
  nat : HasTy env "Nat" [] (.sort 1)
  zero : HasTy env "Nat.zero" [] tNat
  succ : HasTy env "Nat.succ" [] (.forallE tNat tNat false)
  u64 : HasTy env "UInt64" [] (.sort 1)
  ofNat : HasTy env "UInt64.ofNat" [] (.forallE tNat tU false)
  u8 : HasTy env "UInt8" [] (.sort 1)
  ofNat8 : HasTy env "UInt8.ofNat" [] (.forallE tNat (.const "UInt8" []) false)
  list : HasTy env "List" [0] (.forallE (.sort 1) (.sort 1) false)
  nil : HasTy env "List.nil" [0] (.forallE (.sort 1) (.app (.const "List" [0]) (.bvar 0)) false)
  cons : HasTy env "List.cons" [0] (.forallE (.sort 1) (.forallE (.bvar 0)
    (.forallE (.app (.const "List" [0]) (.bvar 1)) (.app (.const "List" [0]) (.bvar 2)) false) false) false)
  prod : HasTy env "Prod" [0, 0] (.forallE (.sort 1) (.forallE (.sort 1) (.sort 1) false) false)
  pmk : HasTy env "Prod.mk" [0, 0] (.forallE (.sort 1) (.forallE (.sort 1) (.forallE (.bvar 1) (.forallE (.bvar 1)
    (.app (.app (.const "Prod" [0, 0]) (.bvar 3)) (.bvar 2)) false) false) false) false)
  buf : HasTy env "Buf" [] (.sort 1)
  bufEq : HasTy env "buf_eq" [] (eqE 2 (.sort 1) (.const "Buf" []) (.app (.const "List" [0]) tU))

variable {M} {L}

theorem np {pw : Bool} (h : pw = false) {P : Prop} : regime pw = 0 → P := by
  subst h; intro h; simp [regime] at h

include L in
theorem natEnc_mem' (H : EncEnv env) (ρ : Nat → S) : ∀ k, O.mem (natEnc M k) (M.cval "Nat" []) := by
  intro k
  induction k with
  | zero => exact mem_ty M L H.zero (ρ := ρ) .const
  | succ k ih =>
    have dP : D O M.cval ρ (.forallE tNat tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
    exact mem_app' L dP (mem_ty M L H.succ dP) .const ih .const

include L in
theorem univ1 (_H : EncEnv env) {n : String} (h : HasTy env n [] (.sort 1)) (ρ : Nat → S) :
    O.mem (M.cval n []) (O.univ 1) := mem_ty M L h (ρ := ρ) .sort

include L in
/-- canonical lists are in `List T` -/
theorem listEnc_mem (H : EncEnv env) (ρ : Nat → S) {α : Type} {T : S} (hT : O.mem T (O.univ 1)) (f : α → S)
    (hf : ∀ a, O.mem (f a) T) :
    ∀ l, O.mem (listEnc M T f l) (O.app (M.cval "List" [0]) T) := by
  intro l
  induction l with
  | nil =>
    have dP : D O M.cval ρ (.forallE (.sort 1) (.app (.const "List" [0]) (.bvar 0)) false)
        (O.piR (regime false) (O.univ 1) fun a => O.app (M.cval "List" [0]) a) :=
      .pi .sort (fun _ _ => .app .const .bvar) (np rfl)
    exact mem_app' L dP (mem_ty M L H.nil dP) .sort hT (.app .const .bvar)
  | cons a l ih =>
    have dP : D O M.cval ρ (.forallE (.sort 1) (.forallE (.bvar 0)
        (.forallE (.app (.const "List" [0]) (.bvar 1)) (.app (.const "List" [0]) (.bvar 2)) false) false) false)
        (O.piR (regime false) (O.univ 1) fun t => O.piR (regime false) t fun _ =>
          O.piR (regime false) (O.app (M.cval "List" [0]) t) fun _ => O.app (M.cval "List" [0]) t) :=
      .pi .sort (fun t _ => .pi .bvar (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .app .const .bvar) (np rfl))
        (np rfl)) (np rfl)
    have h1 := L.app_mem_piR (mem_ty M L H.cons dP) hT (np rfl)
    have h2 := L.app_mem_piR h1 (hf a) (np rfl)
    exact L.app_mem_piR h2 ih (np rfl)

include L in
/-- `⟦Buf⟧ = ⟦List UInt64⟧` from the stored `buf_eq : Buf = List UInt64` (transfer, no binder) -/
theorem buf_eq (H : EncEnv env) (ρ : Nat → S) :
    M.cval "Buf" [] = O.app (M.cval "List" [0]) (M.cval "UInt64" []) := by
  obtain ⟨ty, hc, hty⟩ := H.bufEq
  have dL : D O M.cval ρ (.forallE (.sort 1) (.sort 1) false) (O.piR (regime false) (O.univ 1) fun _ => O.univ 1) :=
    .pi .sort (fun _ _ => .sort) (np rfl)
  have hLU : O.mem (O.app (M.cval "List" [0]) (M.cval "UInt64" [])) (O.univ 1) :=
    mem_app' L dL (mem_ty M L H.list dL) .sort (univ1 (L := L) H H.u64 ρ) .sort
  exact transferN L M hc (ls := []) (ts := []) hty ρ .nil .sort .const (.app .const .const)
    (L.univ_mem_univ 1) (univ1 (L := L) H H.buf ρ) hLU

include L in
/-- **the typing lemma**: every encoded value is in its type's set -/
theorem encM_mem (H : EncEnv env) (ρ : Nat → S) : ∀ v, O.mem (encM M v) (tyE M v) ∧ O.mem (tyE M v) (O.univ 1)
  | .w x => by
    have dP : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
    exact ⟨mem_app' L dP (mem_ty M L H.ofNat dP) .const (natEnc_mem' (L := L) H ρ _) .const,
      univ1 (L := L) H H.u64 ρ⟩
  | .n k => ⟨natEnc_mem' (L := L) H ρ k, univ1 (L := L) H H.nat ρ⟩
  | .l bs => by
    have dP : D O M.cval ρ (.forallE tNat (.const "UInt8" []) false) _ := .pi .const (fun _ _ => .const) (np rfl)
    have dL : D O M.cval ρ (.forallE (.sort 1) (.sort 1) false) (O.piR (regime false) (O.univ 1) fun _ => O.univ 1) :=
      .pi .sort (fun _ _ => .sort) (np rfl)
    exact ⟨listEnc_mem (L := L) H ρ (univ1 (L := L) H H.u8 ρ) _
        (fun b => mem_app' L dP (mem_ty M L H.ofNat8 dP) .const (natEnc_mem' (L := L) H ρ _) .const) bs,
      mem_app' L dL (mem_ty M L H.list dL) .sort (univ1 (L := L) H H.u8 ρ) .sort⟩
  | .b ws => by
    have dP : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
    refine ⟨?_, univ1 (L := L) H H.buf ρ⟩
    show O.mem (listEnc M _ _ ws) (M.cval "Buf" [])
    rw [buf_eq (L := L) H ρ]
    exact listEnc_mem (L := L) H ρ (univ1 (L := L) H H.u64 ρ) _
      (fun w => mem_app' L dP (mem_ty M L H.ofNat dP) .const (natEnc_mem' (L := L) H ρ _) .const) ws
  | .p x y => by
    obtain ⟨hx, hxT⟩ := encM_mem H ρ x
    obtain ⟨hy, hyT⟩ := encM_mem H ρ y
    have dP : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1) (.forallE (.bvar 1) (.forallE (.bvar 1)
        (.app (.app (.const "Prod" [0, 0]) (.bvar 3)) (.bvar 2)) false) false) false) false)
        (O.piR (regime false) (O.univ 1) fun a => O.piR (regime false) (O.univ 1) fun b =>
          O.piR (regime false) a fun _ => O.piR (regime false) b fun _ =>
            O.app (O.app (M.cval "Prod" [0, 0]) a) b) :=
      .pi .sort (fun _ _ => .pi .sort (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar
        (fun _ _ => .app (.app .const .bvar) .bvar) (np rfl)) (np rfl)) (np rfl)) (np rfl)
    have h1 := L.app_mem_piR (mem_ty M L H.pmk dP) hxT (np rfl)
    have h2 := L.app_mem_piR h1 hyT (np rfl)
    have h3 := L.app_mem_piR h2 hx (np rfl)
    have h4 := L.app_mem_piR h3 hy (np rfl)
    have dQ : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1) (.sort 1) false) false)
        (O.piR (regime false) (O.univ 1) fun _ => O.piR (regime false) (O.univ 1) fun _ => O.univ 1) :=
      .pi .sort (fun _ _ => .pi .sort (fun _ _ => .sort) (np rfl)) (np rfl)
    have g1 := L.app_mem_piR (mem_ty M L H.prod dQ) hxT (np rfl)
    exact ⟨h4, L.app_mem_piR g1 hyT (np rfl)⟩

include L in
/-- **`FactsM.letβ`, discharged**: beta (both regimes) + the typing lemma -/
theorem letβ_field (H : EncEnv env) {ρ : Nat → S} {v b : X} {s : Sh} {a : ExprSpec.V} {R : S}
    (hva : VSh s a) (ih : ∀ X, D O M.cval ρ (trM v) X → X = encM M a)
    (hR : D O M.cval ρ (trM (.lt true (shTy s) v b)) R) : D O M.cval (push (encM M a) ρ) (trM b) R := by
  have hR' := hR
  obtain ⟨Lv, X, hL, hv, -⟩ := app_inv hR'
  obtain rfl := ih X hv
  exact beta L hR (shTy_denotes M hva) hv (encM_mem (L := L) H ρ a).1

end Typing

end Bridge.EvM
