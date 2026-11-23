/- Bridge.Real.NatLit: discharging `natLitSupported` from ACCEPTANCE, with con-leche's own walk.

`installRun_step_mem` is con-leche's `installRun_declares` (Model/StreamConsts.lean:724) with its per-step
conclusion generalised: whatever ONE accepted `checkDecl` step of a record is guaranteed to push survives to the
end of phase A.  The proof is that walk, re-run (COPIED structure, marked); the per-step fact used here is the
pinned Nat block: a record recognised as the Nat pin installs `natA, natZeroA, natSuccA, natRecA`
(`DeclBasisRun`).  `natLit_of_accepted`: an accepted stream holding such a record has `natLitSupported`. -/
import ConLeche.MainTheorem
import ConLeche.Model.StreamConsts
import ConLeche.Semantics.Bridge.Sound

namespace Bridge.Real.NatLit
open ConLeche ConLeche.Cached ConLeche.Semantics ConLeche.Model

universe w
variable {V : Type w} [SetTheory V] {μ : CheckMode} {pins : List NatOpPinSet}

/-- (structure COPIED from `installRun_declares`, StreamConsts.lean:724) -/
theorem installRun_step_mem (hμ : μ.verifiedChecks = true) {ds : List Declaration}
    {p : Nat × FEnv × Array PendingCheck} {q : Nat × FEnv × Array PendingCheck}
    (hrun : InstallRun μ pins ds p q) :
    p.2.1 = mkFEnv p.2.1.env → EnvModelOk V μ p.2.1.env →
    NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) →
    ∀ pd ∈ ds, ∀ c : ConstantInfo,
      (∀ (env env₂ : Env) (F : Nat), checkDecl μ (fueledOps μ F) pins env pd = .ok env₂ → c ∈ env₂.consts) →
      c ∈ q.2.1.env.consts := by
  induction hrun with
  | nil p => exact fun _ _ _ _ pd hmem => absurd hmem List.not_mem_nil
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hm hnd hB pd' hmem c hc
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨fe₁, pend₁, s₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    simp only at hfe hstepC
    obtain ⟨hpush₁, -⟩ :=
      annotStepC_push μ i (PushChain.self hfe) pend pd {} (fe₁, pend₁) s₁ hstepC
    have hfe₁ : fe₁ = mkFEnv fe₁.env := hpush₁.canon
    obtain ⟨hchainF, new₁, hpend₁⟩ := installRun_trace μ rest (PushChain.self hfe₁)
    obtain ⟨hm₁, -, F, hF⟩ :=
      annotStepC_model (V := V) hμ hfe hfe₁ hm CSOKF.empty hstepC hchainF hpend₁ hnd hB
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · obtain ⟨new, hnew⟩ := hchainF.2.1
      rw [hnew]; exact List.mem_append_right _ (hc _ _ F hF)
    · exact ih hfe₁ hm₁ hnd hB pd' hmem' c hc

/-- the accepted env holds `c` whenever one record's accepted step must push it (structure COPIED from
`checkDecls_consts`, StreamConsts.lean:764) -/
theorem checkDecls_step_mem (V : Type w) [SetTheory V] {ds : Array Declaration} {env : Env}
    (accepted : checkDecls .verified pins ds = .ok env) {pd : Declaration} (hmem : pd ∈ ds) (c : ConstantInfo)
    (hc : ∀ (env env₂ : Env) (F : Nat), checkDecl .verified (fueledOps .verified F) pins env pd = .ok env₂ →
      c ∈ env₂.consts) :
    c ∈ env.consts ∧ NodupNames env := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked _ accepted
  obtain ⟨n, run⟩ := fc.1.run
  have hchain := installRun_trace _ run (PushChain.refl Env.empty)
  have hnd : NodupNames fc.1.fe.env := hchain.1.2.2 List.nodup_nil
  exact ⟨installRun_step_mem (V := V) rfl run rfl EnvModelOk.empty hnd fc.records pd
    (Array.mem_toList_iff.mpr hmem) c hc, hnd⟩

theorem basisInstall_mem : ∀ {env env₂ : Env} {cs : List ConstantInfo}, Semantics.BasisInstallRun env cs env₂ →
    ∀ c ∈ cs, c ∈ env₂.consts
  | _, _, [], _, c, hc => absurd hc List.not_mem_nil
  | env, env₂, ci :: rest, ⟨_, hr⟩, c, hc => by
    have hkeep : ∀ {e e₂ : Env} {cs : List ConstantInfo}, Semantics.BasisInstallRun e cs e₂ →
        ∀ d ∈ e.consts, d ∈ e₂.consts := by
      intro e e₂ cs h
      induction cs generalizing e with
      | nil => cases h; exact fun d hd => hd
      | cons x xs ih => exact fun d hd => ih h.2 d (List.mem_cons_of_mem _ hd)
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hkeep hr _ List.mem_cons_self
    · exact basisInstall_mem hr c hc'

/-- a record recognised as the Nat pin pushes the pinned Nat block -/
theorem natPin_step {block : List ConstantInfo} {nP : Nat} (hpin : basisPinHit block = some .natK)
    (c : ConstantInfo) (hc : c ∈ BasisKind.natK.declsA) :
    ∀ (env env₂ : Env) (F : Nat), checkDecl .verified (fueledOps .verified F) pins env (.indDecl block nP) = .ok env₂ →
      c ∈ env₂.consts := by
  intro env env₂ F h
  have hrun := Semantics.checkDeclRun_ofEnvFactsK h
  simp only [Semantics.DeclRun, hpin] at hrun
  exact basisInstall_mem hrun.2 c hc

/-- **`natLitSupported` from acceptance**: an accepted stream holding a record recognised as the pinned Nat
block. -/
theorem natLit_of_accepted (V : Type w) [SetTheory V] {ds : Array Declaration} {env : Env}
    (accepted : checkDecls .verified pins ds = .ok env) {block : List ConstantInfo} {nP : Nat}
    (hmem : Declaration.indDecl block nP ∈ ds) (hpin : basisPinHit block = some .natK) :
    natLitSupported env = true := by
  have h : ∀ c ∈ BasisKind.natK.declsA, c ∈ env.consts ∧ NodupNames env := fun c hc =>
    checkDecls_step_mem V accepted hmem c (natPin_step hpin c hc)
  have hA := h natA (by show natA ∈ [natA, natZeroA, natSuccA, natRecA]; exact List.mem_cons_self)
  have hZ := h natZeroA (by show natZeroA ∈ [natA, natZeroA, natSuccA, natRecA]; simp)
  have hS := h natSuccA (by show natSuccA ∈ [natA, natZeroA, natSuccA, natRecA]; simp)
  have e1 : env.find? natName = some natA := by
    have := find?_of_mem_nodup hA.2 hA.1; rwa [show natA.name = natName by decide +kernel] at this
  have e2 : env.find? natZeroName = some natZeroA := by
    have := find?_of_mem_nodup hZ.2 hZ.1; rwa [show natZeroA.name = natZeroName by decide +kernel] at this
  have e3 : env.find? natSuccName = some natSuccA := by
    have := find?_of_mem_nodup hS.2 hS.1; rwa [show natSuccA.name = natSuccName by decide +kernel] at this
  unfold natLitSupported
  rw [e1, e2, e3]
  decide +kernel

end Bridge.Real.NatLit
