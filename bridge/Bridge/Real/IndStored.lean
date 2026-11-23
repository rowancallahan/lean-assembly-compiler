/- Bridge.Real.IndStored: the stored types of an accepted ONE-MEMBER inductive block, from acceptance.

con-leche's `checkDecls_consts` covers defs/theorems only.  Here, for an `indDecl` record that is not a pinned
basis block and whose block reads as ONE member (`blockParts?`), the run relation `DeclBlockRun`
(Semantics/Inductives/DeclBlock.lean) is inverted with con-leche's own inversions (`checkBlockInds_shape`,
`checkBlockCtors_inv`, `constantValRun_of`): the type former is stored as the annotation of its declared type
when that type is already a Π-telescope ending in a sort (`checkSumTele`'s syntactic branch), every constructor
as the annotation of its declared type.  The install's later stages only push. -/
import Bridge.Real.NatLit
import Bridge.Real.Stored
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.ExceptBind

namespace Bridge.Real.Ind
open ConLeche ConLeche.Cached ConLeche.Semantics

variable {μ : CheckMode} {F : Nat}

/-- `checkConstantVal` stores the annotation of the declared type (con-leche's `ConstantValRun` +
`annotateCore_annotOf`, as in `checkDecl_declares`) -/
theorem ccv_annot {env : Env} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps μ F) env cv = .ok cv') :
    cv'.name = cv.name ∧ cv'.levelParams = cv.levelParams ∧ AnnotOf cv.type cv'.type := by
  obtain ⟨type', rfl, -, -, hrun⟩ := constantValRun_of h
  obtain ⟨-, -, -, -, hb, hfv, hann, -, -, -⟩ := hrun
  exact ⟨rfl, rfl, annotateCore_annotOf F hann hb ((Expr.WScoped.of_not_hasFvar hfv).fvarsBelow)⟩

/-- an annotation of a binder-free telescope is that telescope with some binder data -/
theorem annot_tele {Ts : List Expr} {ms : List BinderMeta} {B t : Expr} (hl : ms.length = Ts.length)
    (hT : ∀ T ∈ Ts, BF T) (hB : BF B) (h : AnnotOf (piN (Ts.zip ms) B) t) :
    ∃ ms' : List BinderMeta, ms'.length = Ts.length ∧ t = piN (Ts.zip ms') B := by
  have hT' : ∀ p ∈ Ts.zip ms, BF p.1 := fun p hp => hT p.1 (List.of_mem_zip hp).1
  unfold AnnotOf at h
  rw [piN_zeta _ hT' hB, piD_rm Ts ms hl hT hB] at h
  exact piD_inv Ts hT hB h

theorem stripPis_piN : ∀ (ps : List (Expr × BinderMeta)) (B : Expr), Expr.stripPis ps.length (piN ps B) = some (ps, B)
  | [], B => rfl
  | (T, m) :: ps, B => by simp [piN, Expr.stripPis, stripPis_piN ps B]

/-! ## the pushes keep what is there -/

theorem consSumCtors_keep (nP : Nat) : ∀ (cs : List (ConstantVal × Nat)) (env : Env),
    ∀ c ∈ env.consts, c ∈ (consSumCtors nP cs env).consts
  | [], _, _, h => h
  | _ :: cs, _, _, h => consSumCtors_keep nP cs _ _ (List.mem_cons_of_mem _ h)

theorem consSumCtors_new (nP : Nat) : ∀ (cs : List (ConstantVal × Nat)) (env : Env),
    ∀ p ∈ cs, ConstantInfo.ctorInfo p.1 nP p.2 ∈ (consSumCtors nP cs env).consts
  | [], _, _, h => absurd h List.not_mem_nil
  | q :: cs, env, p, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact consSumCtors_keep nP cs _ _ List.mem_cons_self
    · exact consSumCtors_new nP cs _ p h'

theorem consBlockRecsT_keep {find? : Name → Option ConstantInfo} {res : Expr → Bool} {p : BlockShape} :
    ∀ (m : Nat) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env),
      ∀ c ∈ env.consts, c ∈ (consBlockRecsT find? res p m out env).consts
  | _, [], _, _, h => h
  | _, _ :: out, _, _, h => consBlockRecsT_keep _ out _ _ (List.mem_cons_of_mem _ h)

theorem checkStructProjTable_keep {T C : Name} {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal} {env env' : Env}
    (h : checkStructProjTable (m := CheckM) T C lps nP nF resSort guards off cvCa env = .ok env') :
    ∀ c ∈ env.consts, c ∈ env'.consts := by
  unfold checkStructProjTable at h
  obtain ⟨bodies, -, h⟩ := exceptBind_ok h
  simp only [bind, Except.bind] at h
  split at h
  · split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; intro c hc; exact List.mem_cons_of_mem _ hc
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem checkBlockTables_keep {p : BlockShape} :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) {env env' : Env},
      checkBlockTables (m := CheckM) p l env = .ok env' → ∀ c ∈ env.consts, c ∈ env'.consts
  | [], env, env', h => by
    simp only [checkBlockTables, pure, Except.pure, Except.ok.injEq] at h; subst h; exact fun _ h => h
  | (ms, ctorsA, sortss) :: rest, env, env', h => by
    unfold checkBlockTables at h
    obtain ⟨env₁, h1, h2⟩ := exceptBind_ok h
    have k2 := checkBlockTables_keep rest h2
    intro c hc
    apply k2
    split at h1
    · split at h1
      · exact checkStructProjTable_keep h1 c hc
      · simp only [pure, Except.pure, Except.ok.injEq] at h1; subst h1; exact hc
    · simp only [pure, Except.pure, Except.ok.injEq] at h1; subst h1; exact hc

theorem consBlockCtors_keep (nP : Nat) : ∀ (css : List (List (ConstantVal × Nat))) (env : Env),
    ∀ c ∈ env.consts, c ∈ (consBlockCtors nP css env).consts
  | [], _, _, h => h
  | cs :: css, env, c, h => consBlockCtors_keep nP css _ c (consSumCtors_keep nP cs env c h)

/-- each constructor's checked record comes from `checkConstantVal` on the declared one -/
theorem checkSumCtors_each {env₀ env : Env} {T : Name} {lps : List Name} {nP nIdx : Nat} {rs : Level}
    {isProp large : Bool} {cvTa : ConstantVal} :
    ∀ {cs : List (ConstantVal × Nat)} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)},
      checkSumCtors (fueledOps μ F) env₀ env T lps nP nIdx rs isProp large cvTa cs = .ok (ctorsA, sortss) →
      ∀ c ∈ cs, ∃ cvCa, (cvCa, c.2) ∈ ctorsA ∧ checkConstantVal (fueledOps μ F) env c.1 = .ok cvCa
  | [], _, _, _, c, hc => absurd hc List.not_mem_nil
  | c0 :: cs, ctorsA, sortss, h, c, hc => by
    unfold checkSumCtors at h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨cvCa, sorts⟩ := r
    try simp only at h
    obtain ⟨r', hr', h⟩ := exceptBind_ok h
    obtain ⟨rest, srest⟩ := r'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases List.mem_cons.mp hc with rfl | hc'
    · unfold checkSumCtor at hr
      obtain ⟨cvCa', hccv, hr⟩ := exceptBind_ok hr
      have : cvCa' = cvCa := by
        repeat (first
          | (obtain ⟨_, _, hr⟩ := exceptBind_ok hr)
          | (split at hr))
        all_goals first
          | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr; exact hr.1)
          | (cases hr; rfl)
          | ((repeat' (split at hr)) <;>
              (first
                | (simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hr; done)
                | (simp at hr; done)))
      subst this
      exact ⟨cvCa', List.mem_cons_self, hccv⟩
    · obtain ⟨cvCa', hm, hcc⟩ := checkSumCtors_each hr' c hc'
      exact ⟨cvCa', List.mem_cons_of_mem _ hm, hcc⟩

/-- what a one-member block install stores: its former (as the annotation of the declared type, when that type
is a Π-telescope ending in a sort) and each constructor (as the annotation of its declared type) -/
theorem oneBlock {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockParts}
    (h : DeclBlockRun μ F env block p₀ env₂) {ms0 : MemberShape} (hm : p₀.members = [ms0])
    {s : Level}
    (hstrip : ∀ t : Expr, AnnotOf ms0.cvT.type t → ∃ bs, t.stripPis (p₀.nP + ms0.nIdx) = some (bs, .sort s)) :
    (∃ c ∈ env₂.consts, c.name = ms0.cvT.name ∧ c.toConstantVal.levelParams = ms0.cvT.levelParams ∧
        AnnotOf ms0.cvT.type c.toConstantVal.type) ∧
    (∀ cC ∈ ms0.ctors, ∃ c ∈ env₂.consts, c.name = cC.1.name ∧
        c.toConstantVal.levelParams = cC.1.levelParams ∧ AnnotOf cC.1.type c.toConstantVal.type) := by
  obtain ⟨-, -, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, -, -, -, -, -, -, -, -, -, out,
    hInd, hp, hCtors, -, -, -, -, -, -, -, htab⟩ := h
  obtain ⟨ms0', rest, cvTa0, s0, cvs, hmem, hcv, hp1, henv1, htele, hteles, -⟩ := checkBlockInds_shape hInd
  rw [hm] at hmem
  obtain ⟨rfl, rfl⟩ := List.cons.inj hmem
  simp only [checkBlockTeles, pure, Except.pure, Except.ok.injEq] at hteles
  subst hteles
  simp only [List.map_nil] at hcv
  subst hcv
  -- the former: checkConstantVal's annotation, kept by `checkSumTele`'s syntactic branch
  unfold checkBlockTele at htele
  obtain ⟨cvTa₀, hccv₀, htele⟩ := exceptBind_ok htele
  obtain ⟨q, hsum, htele⟩ := exceptBind_ok htele
  obtain ⟨hn0, hl0, ha0⟩ := ccv_annot hccv₀
  have hq : q.1 = cvTa₀ := by
    unfold checkSumTele at hsum
    obtain ⟨bs, hb⟩ := hstrip _ ha0
    rw [hb] at hsum
    simp only [pure, Except.pure, Except.ok.injEq] at hsum
    rw [← hsum]
  have hc0 : cvTa0 = q.1 := by
    obtain ⟨cvTa', s'⟩ := q
    obtain ⟨r, -, htele⟩ := exceptBind_ok htele
    obtain ⟨bs', tb⟩ := r
    simp only at htele
    split at htele
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at htele; exact htele.1.symm
    · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at htele
  rw [hq] at hc0; subst hc0
  -- everything consed into env₁ survives to env₂
  have keep : ∀ c ∈ env₁.consts, c ∈ env₂.consts := fun c hc =>
    checkBlockTables_keep _ htab c (consBlockRecsT_keep _ _ _ c (consBlockCtors_keep _ _ _ c hc))
  refine ⟨⟨.indInfo cvTa0 (blockCapsAt p₁ 0 isRec), keep _ (by rw [henv1]; simp [consBlockInds]), hn0, hl0, ha0⟩, ?_⟩
  -- the constructors
  subst hp
  simp only [BlockParts.complete_members] at hCtors
  rw [hp1, BlockShape.withSort_members, show p₀.members = [ms0] from hm] at hCtors
  obtain ⟨hlen, -, hall⟩ := checkBlockCtors_inv hCtors
  obtain ⟨ctorsA, sortss, hA, -, hsc⟩ := hall 0 (ms0, cvTa0) rfl
  intro cC hcC
  obtain ⟨cvCa, hmemA, hccv⟩ := checkSumCtors_each hsc cC hcC
  obtain ⟨hn, hl, ha⟩ := ccv_annot hccv
  obtain ⟨ctorsA', rfl⟩ : ∃ x, ctorsAs = [x] := by
    match ctorsAs, hlen with | [x], _ => exact ⟨x, rfl⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hA; subst hA
  refine ⟨.ctorInfo cvCa (p₀.complete p₁).nP cC.2, ?_, hn, hl, ha⟩
  apply checkBlockTables_keep _ htab
  apply consBlockRecsT_keep
  simp only [consBlockCtors]
  exact consSumCtors_new _ _ _ (cvCa, cC.2) hmemA

/-! ## the walk, with a predicate (structure COPIED from con-leche's `installRun_declares`) -/

universe w

theorem installRun_step_ex {V : Type w} [SetTheory V] {pins : List NatOpPinSet} (hμ : μ.verifiedChecks = true)
    {ds : List Declaration} {p q : Nat × FEnv × Array PendingCheck} (hrun : InstallRun μ pins ds p q) :
    p.2.1 = mkFEnv p.2.1.env → Model.EnvModelOk V μ p.2.1.env → NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) →
    ∀ pd ∈ ds, ∀ Q : ConstantInfo → Prop,
      (∀ (env env₂ : Env) (F : Nat), checkDecl μ (fueledOps μ F) pins env pd = .ok env₂ → ∃ c ∈ env₂.consts, Q c) →
      ∃ c ∈ q.2.1.env.consts, Q c := by
  induction hrun with
  | nil p => exact fun _ _ _ _ pd hmem => absurd hmem List.not_mem_nil
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hm hnd hB pd' hmem Q hc
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨fe₁, pend₁, s₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    simp only at hfe hstepC
    obtain ⟨hpush₁, -⟩ := annotStepC_push μ i (PushChain.self hfe) pend pd {} (fe₁, pend₁) s₁ hstepC
    have hfe₁ : fe₁ = mkFEnv fe₁.env := hpush₁.canon
    obtain ⟨hchainF, new₁, hpend₁⟩ := installRun_trace μ rest (PushChain.self hfe₁)
    obtain ⟨hm₁, -, F, hF⟩ :=
      annotStepC_model (V := V) hμ hfe hfe₁ hm CSOKF.empty hstepC hchainF hpend₁ hnd hB
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · obtain ⟨new, hnew⟩ := hchainF.2.1
      obtain ⟨c, hc1, hc2⟩ := hc _ _ F hF
      exact ⟨c, by rw [hnew]; exact List.mem_append_right _ hc1, hc2⟩
    · exact ih hfe₁ hm₁ hnd hB pd' hmem' Q hc

theorem checkDecls_step_ex (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration}
    {env : Env} (accepted : checkDecls .verified pins ds = .ok env) {pd : Declaration} (hmem : pd ∈ ds)
    (Q : ConstantInfo → Prop)
    (hc : ∀ (env env₂ : Env) (F : Nat), checkDecl .verified (fueledOps .verified F) pins env pd = .ok env₂ →
      ∃ c ∈ env₂.consts, Q c) :
    (∃ c ∈ env.consts, Q c) ∧ NodupNames env := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked _ accepted
  obtain ⟨n, run⟩ := fc.1.run
  have hchain := installRun_trace _ run (PushChain.refl Env.empty)
  have hnd : NodupNames fc.1.fe.env := hchain.1.2.2 List.nodup_nil
  exact ⟨installRun_step_ex (V := V) rfl run rfl Model.EnvModelOk.empty hnd fc.records pd
    (Array.mem_toList_iff.mpr hmem) Q hc, hnd⟩

/-- an accepted `checkDecl` step of a non-pinned one-member block record runs `DeclBlockRun` -/
theorem ind_step {pins : List NatOpPinSet} {block : List ConstantInfo} {nP : Nat} {p₀ : BlockParts}
    (hpin : basisPinHit block = none) (hp : blockParts? nP block = some p₀) {env env₂ : Env} {F : Nat}
    (h : checkDecl .verified (fueledOps .verified F) pins env (.indDecl block nP) = .ok env₂) :
    DeclBlockRun .verified F env block p₀ env₂ := by
  have hrun := checkDeclRun_ofEnvFactsK h
  simp only [DeclRun, hpin, DeclIndRunDispatchK, hp] at hrun
  exact hrun


theorem zeta_stripPis : ∀ (n : Nat) {d : Expr} {bs : List (Expr × BinderMeta)} {s : Level},
    d.stripPis n = some (bs, .sort s) → ∃ bs', d.zeta.stripPis n = some (bs', .sort s)
  | 0, d, bs, s, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨[], rfl⟩
  | n + 1, d, bs, s, h => by
    cases d <;> simp only [Expr.stripPis, reduceCtorEq, Option.map_eq_some_iff] at h
    case forallE ty b m =>
      obtain ⟨⟨bs1, e⟩, h1, h2⟩ := h
      simp only [Prod.mk.injEq] at h2; obtain ⟨-, rfl⟩ := h2
      obtain ⟨bs', h'⟩ := zeta_stripPis n h1
      exact ⟨(ty.zeta, m) :: bs', by simp [Expr.zeta, Expr.stripPis, h']⟩

theorem rm_stripPis : ∀ (n : Nat) {e t : Expr} {bs : List (Expr × BinderMeta)} {s : Level},
    e.stripPis n = some (bs, .sort s) → t.resetMeta = e.resetMeta → ∃ bs', t.stripPis n = some (bs', .sort s)
  | 0, e, t, bs, s, h, hr => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    cases t <;> simp [Expr.resetMeta] at hr
    case sort u => subst hr; exact ⟨[], rfl⟩
  | n + 1, e, t, bs, s, h, hr => by
    cases e <;> simp only [Expr.stripPis, reduceCtorEq, Option.map_eq_some_iff] at h
    case forallE ty b m =>
      obtain ⟨⟨bs1, e⟩, h1, h2⟩ := h
      simp only [Prod.mk.injEq] at h2; obtain ⟨-, rfl⟩ := h2
      cases t <;> simp only [Expr.resetMeta, reduceCtorEq] at hr
      case forallE ty' b' m' =>
        obtain ⟨-, hb, -⟩ := Expr.forallE.inj hr
        obtain ⟨bs', h'⟩ := rm_stripPis n h1 hb
        exact ⟨(ty', m') :: bs', by simp [Expr.stripPis, h']⟩

theorem annot_stripPis {n : Nat} {d t : Expr} {bs : List (Expr × BinderMeta)} {s : Level}
    (h : d.stripPis n = some (bs, .sort s)) (ha : AnnotOf d t) : ∃ bs', t.stripPis n = some (bs', .sort s) := by
  obtain ⟨bs', h'⟩ := zeta_stripPis n h
  exact rm_stripPis n h' ha

/-! ## a decidable check on the stream, and what it gives -/

/-- the stream holds a non-pinned one-member block whose former is declared `former` (a Π-telescope ending in a
sort) and among whose constructors are `ctors` -/
def blockHas (ds : Array Declaration) (former : ConstantVal) (ctors : List ConstantVal) : Bool :=
  ds.any fun
    | .indDecl b nP => basisPinHit b == none && (match blockParts? nP b with
        | some p => (match p.members with
          | [ms] => ms.cvT == former && ctors.all (fun c => ms.ctors.any (·.1 == c)) &&
              (match Expr.stripPis (p.nP + ms.nIdx) former.type with
               | some (_, .sort _) => true | _ => false)
          | _ => false)
        | none => false)
    | _ => false

/-- **stored as declared**: for a listed former or constructor `cv` of such a block, the accepted env stores
`cv.name` with `cv`'s level parameters and the annotation of `cv`'s type -/
theorem blockHas_stored (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : checkDecls .verified pins ds = .ok env) {former : ConstantVal} {ctors : List ConstantVal}
    (h : blockHas ds former ctors = true) :
    ∀ cv ∈ former :: ctors, ∃ c, env.find? cv.name = some c ∧ c.toConstantVal.levelParams = cv.levelParams ∧
      AnnotOf cv.type c.toConstantVal.type := by
  obtain ⟨d, hd, hp⟩ := Array.any_eq_true'.mp h
  match d, hp with
  | .indDecl b nP, hp =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨hpin, hp⟩ := hp
    split at hp
    · rename_i p₀ hbp
      split at hp
      · rename_i ms hms
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true] at hp
        obtain ⟨⟨rfl, hct⟩, hsort⟩ := hp
        split at hsort
        · rename_i bs s hstr
          have hstrip : ∀ t : Expr, AnnotOf ms.cvT.type t → ∃ bs', t.stripPis (p₀.nP + ms.nIdx) = some (bs', .sort s) := by
            intro t ht
            exact annot_stripPis hstr ht
          intro cv hcv
          obtain ⟨⟨c, hc, hn, hl, ha⟩, hnd⟩ := checkDecls_step_ex V accepted hd
            (fun c => c.name = cv.name ∧ c.toConstantVal.levelParams = cv.levelParams ∧
              AnnotOf cv.type c.toConstantVal.type) (by
              intro env' env₂ F hF
              have hb := oneBlock (ind_step hpin hbp hF) hms hstrip
              rcases List.mem_cons.mp hcv with rfl | hcv'
              · exact hb.1
              · obtain ⟨cC, hcC, hcq⟩ := hct cv hcv'
                obtain ⟨c, hc, h1, h2, h3⟩ := hb.2 cC hcC
                subst hcq
                exact ⟨c, hc, h1, h2, h3⟩)
          exact ⟨c, hn ▸ find?_of_mem_nodup hnd hc, hl, ha⟩
        · simp at hsort
      · simp at hp
    · simp at hp

end Bridge.Real.Ind
