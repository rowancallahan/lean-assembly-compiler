/- Bridge.EvBridge: the Ev induction over WELL-FORMED (emitted) terms.  Supersedes `EvSkeleton.ev_denotes`,
whose `Facts` quantify over arbitrary type/instance arguments and so cannot all hold in a real model.

Here every field of `FactsW` speaks only about the canonical arguments `emit` writes (`Typed.Wf`), and gets the
shapes of the values involved (`Typed.VSh`, from subject reduction `ev_shape`), which is what the con-leche half
needs for `enc v ∈ ⟦shTy s⟧`.  Each field is one open lemma of the real bridge (a transfer from one or two
stored theorems + typing; DENOTES_SPIKE §2/§4, Transfer.lean, DENOTES-S2's BridgeOpsSet.lean).

STATUS: proved, no sorry (the `FactsW` fields are hypotheses). -/
import Bridge.EvSkeleton
import Bridge.Typed

namespace Bridge.EvW
open ExprSpec ParSpec Bridge.Skel Bridge.Typed

variable {S : Type} {sapp : S → S → S} {mem : S → S → Prop} {lamS : S → (S → S) → S}
  {cval : String → List Nat → S}

/-- the open per-constant lemmas, canonical arguments only.  `ρ` is any variable environment; `ρE env` the one
of an Ev environment. -/
structure FactsW (sapp : S → S → S) (mem : S → S → Prop) (lamS : S → (S → S) → S)
    (cval : String → List Nat → S) (sig : Sig) (P : Prog) (enc : ExprSpec.V → S) (junk : S) : Prop where
  /-- `have x : shTy s := v; b` as `(λ (shTy s). b) v`: beta + `enc a ∈ ⟦shTy s⟧` -/
  letβ : ∀ {env Γ s v b a R}, Typed.Fa2 VSh Γ env → Wf sig Γ v s → Ev P env v a → VSh s a →
    D sapp mem lamS cval (ρE enc junk env) (tr (.lt true (shTy s) v b)) R →
    D sapp mem lamS cval (ρE enc junk (a :: env)) (tr b) R
  litU : ∀ {ρ k R}, k < UInt64.size → D sapp mem lamS cval ρ
    (tr (apps (.c "OfNat.ofNat" [0]) [U, .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)])) R →
    R = enc (.w (UInt64.ofNat k))
  litN : ∀ {ρ k R}, D sapp mem lamS cval ρ
    (tr (apps (.c "OfNat.ofNat" [0]) [.c "Nat" [], .nat k, .app (.c "instOfNatNat" []) (.nat k)])) R →
    R = enc (.n k)
  bin : ∀ {ρ op n i H x y z}, binHead op = (n, i) → 1 ≤ op → op ≤ 7 → binV n x y = some z →
    D sapp mem lamS cval ρ (tr (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    sapp (sapp H (enc (.w x))) (enc (.w y)) = enc (.w z)
  /-- `ite` with the emitted condition/instance; the condition's truth value comes from its `EvB` -/
  ite : ∀ {env r n cmp a b c d bc H Xt Xe}, condX n cmp a b = (c, d) → iteOk n cmp a b → EvB P env c bc →
    D sapp mem lamS cval (ρE enc junk env) (tr (apps (.c "ite" [1]) [shTy r, c, d])) H →
    sapp (sapp H Xt) Xe = if bc then Xt else Xe
  pair : ∀ {ρ A B H x y}, VSh A x → VSh B y →
    D sapp mem lamS cval ρ (tr (apps (.c "Prod.mk" [0, 0]) [shTy A, shTy B])) H →
    sapp (sapp H (enc x)) (enc y) = enc (.p x y)
  cases : ∀ {ρ l r Rs body H L x y R}, VSh l x → VSh r y →
    D sapp mem lamS cval ρ (tr (apps (.c "Prod.casesOn" [1, 0, 0]) [shTy l, shTy r, .lam (shTy (.p l r)) (shTy Rs)])) H →
    D sapp mem lamS cval ρ (tr (.lam (shTy l) (.lam (shTy r) body))) L → R = sapp (sapp H (enc (.p x y))) L →
    D sapp mem lamS cval (push (enc y) (push (enc x) ρ)) (tr body) R
  natZ : ∀ {ρ Rs H Z L}, D sapp mem lamS cval ρ (tr (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy Rs)])) H →
    sapp (sapp (sapp H (enc (.n 0))) Z) L = Z
  natS : ∀ {ρ Rs s H Z L k R},
    D sapp mem lamS cval ρ (tr (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy Rs)])) H →
    D sapp mem lamS cval ρ (tr (.lam (.c "Nat" []) s)) L → R = sapp (sapp (sapp H (enc (.n (k + 1)))) Z) L →
    D sapp mem lamS cval (push (enc (.n k)) ρ) (tr s) R
  nil : ∀ {ρ R}, D sapp mem lamS cval ρ (tr (apps (.c "List.nil" [0]) [.c "UInt8" []])) R → R = enc (.l [])
  prim : PrimFacts sapp cval enc
  /-- a program def: its stored equation + typing of the (shaped) arguments; `hb` = the IH for the body -/
  call : ∀ {n ps r vs body b v}, sig n = some (ps, r) → Typed.Fa2 VSh ps vs → P.lookup n = some body →
    strip vs.length body = some b →
    (∀ R, D sapp mem lamS cval (ρE enc junk vs.reverse) (tr b) R → R = enc v) →
    (vs.map enc).foldl sapp (cval n []) = enc v

theorem fa2_map_tr {ρ : Nat → S} {as : List X} {Xs : List S}
    (h : Skel.Fa2 (D sapp mem lamS cval ρ) (as.map tr) Xs) :
    Skel.Fa2 (fun a X => D sapp mem lamS cval ρ (tr a) X) as Xs := Skel.Fa2_map h

/-- **Ev agrees with Denotes on well-formed terms** (uniqueness form: whatever `tr e` denotes is `enc v`). -/
theorem ev_denotes {sig : Sig} {P : Prog} {enc : ExprSpec.V → S} {junk : S}
    (F : FactsW sapp mem lamS cval sig P enc junk) (hP : PWf sig P) {env e v} (h : Ev P env e v) :
    ∀ {Γ s}, Wf sig Γ e s → Typed.Fa2 VSh Γ env →
      ∀ R, D sapp mem lamS cval (ρE enc junk env) (tr e) R → R = enc v := by
  refine Ev.rec
    (motive_1 := fun env e v _ => ∀ {Γ s}, Wf sig Γ e s → Typed.Fa2 VSh Γ env →
      ∀ R, D sapp mem lamS cval (ρE enc junk env) (tr e) R → R = enc v)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun env as vs _ => ∀ {Γ ss}, WfL sig Γ as ss → Typed.Fa2 VSh Γ env →
      ∀ Xs, Skel.Fa2 (fun a X => D sapp mem lamS cval (ρE enc junk env) (tr a) X) as Xs → Xs = vs.map enc)
    ?bv ?lt ?litU ?litN ?bin ?iteT ?iteF ?mk ?cases ?natZ ?natS ?nil ?prim ?call
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial)
    ?lnil ?lcons h
  case bv =>
    intro env i v hi Γ s _ _ R hR
    cases hR; simp [ρE, hi]
  case lt =>
    intro env nd t vx b a r hv _ _ ihb Γ s hw he R hR
    cases hw with
    | lt h1 h2 h3 =>
      unif
      have ha := ev_shape hP hv h2 he
      exact ihb h3 (.cons ha he) R (F.letβ he h2 hv ha hR)
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
      obtain ⟨H, X1, hH, h1', rfl⟩ := D_app_inv hH1
      rw [ihd h2 he X1 h1', F.natZ hH]; exact ihz h3 he Z hZ
    | _ => kill
  case natS =>
    intro env ls M d z T sx k r hd hs ihd ihs Γ s' hw he R hR
    cases hw with
    | natCases h1 h2 h3 h4 =>
      unif
      rw [show [X.lam (.c "Nat" []) (shTy _), _, _, _] = [X.lam (.c "Nat" []) (shTy _), _] ++ [_, _] from rfl] at hR
      obtain ⟨H1, Z, L, hH1, hZ, hL, rfl⟩ := two_args hR
      obtain ⟨H, X1, hH, h1', rfl⟩ := D_app_inv hH1
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
    rw [tr_apps] at hR
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
    rw [tr_apps] at hR
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

end Bridge.EvW
