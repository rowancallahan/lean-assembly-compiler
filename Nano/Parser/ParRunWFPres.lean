/- Nano/Parser/ParRunWFPres: `wf_step`: one step of a WF configuration is WF; `wf_star`: every configuration reachable from
`([defs], init toks)` is WF. -/
import Nano.Parser.ParRunWFFr
set_option backward.isDefEq.respectTransparency false
namespace ParRun
open ParSpec

theorem effL_append (c : Ctx) (k r : List Frame) (g : G) : effL c (k ++ r) g = (effL c k g).bind (effL c r) := by
  induction k generalizing g with
  | nil => simp [effL]
  | cons f k ih =>
    simp only [List.cons_append, effL]
    cases effF c f g with
    | none => rfl
    | some g1 => simp [ih]

theorem effF_mono {c f g g' g1} (h : effF c f g = some g1) (hl : g.le g') : ∃ g1', effF c f g' = some g1' ∧ g1.le g1' := by
  obtain ⟨v, b, t⟩ := g
  obtain ⟨v', b', t'⟩ := g'
  obtain ⟨rfl, rfl, ht⟩ := hl
  simp only at ht
  cases f <;> simp only [effF] at h ⊢ <;> (repeat' split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    (try subst g1) <;> (try contradiction) <;> (cases t <;> cases t' <;> simp_all [G.le])

theorem effL_mono {c fs g g'} (h : (effL c fs g).isSome) (hl : g.le g') : (effL c fs g').isSome := by
  induction fs generalizing g g' with
  | nil => simp [effL]
  | cons f r ih =>
    simp only [effL] at h ⊢
    cases hf : effF c f g with
    | none => simp [hf] at h
    | some g1 =>
      rw [hf] at h
      obtain ⟨g1', hf', hl'⟩ := effF_mono hf hl
      rw [hf']; exact ih h hl'

theorem finalsLast_append {k r : List Frame} (hk : ∀ x ∈ k, x.final = false) (hr : finalsLast r = true) :
    finalsLast (k ++ r) = true := by
  induction k with
  | nil => simpa using hr
  | cons x k ih =>
    have hx := hk x (by simp)
    have ih' := ih (fun y hy => hk y (by simp [hy]))
    cases hkr : k ++ r with
    | nil => simp only [List.cons_append, hkr, finalsLast]
    | cons y t => simp only [List.cons_append, hkr, finalsLast, hx, Bool.not_false, Bool.true_and]; rw [← hkr]; exact ih'

theorem finalsLast_cons {f r} (h : finalsLast (f :: r) = true) : finalsLast r = true ∧ (f.final = true → r = []) := by
  cases r with
  | nil => simp [finalsLast]
  | cons y t => simp only [finalsLast, Bool.and_eq_true, Bool.not_eq_true'] at h; simp [h.2, h.1]

theorem shape_step {f r k} (hs : Shape (f :: r)) (hk : KOK f k) : Shape (k ++ r) := by
  obtain ⟨hfl, hgr, has⟩ := hs
  obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := hk
  obtain ⟨hr, hfr⟩ := finalsLast_cons hfl
  by_cases hf : f.final = true
  · have hr0 := hfr hf; subst hr0
    simp only [List.append_nil]
    refine ⟨hk1, fun a ha => (hk4 a ha).1, fun a sz ha => ?_⟩
    rcases hk5 a sz ha with ⟨_, hk⟩ | ⟨rfl, _, _⟩
    · exact ⟨[.tyAtom, .rparen], by simp [Frame.isTy], by simp [hk]⟩
    · simp [Frame.final] at hf
  · have hf' : f.final = false := by simpa using hf
    refine ⟨finalsLast_append (hk2 hf') hr, fun a ha => ?_, fun a sz ha => ?_⟩
    · rcases List.mem_append.mp ha with ha | ha
      · rw [(hk4 a ha).2] at hf'; simp at hf'
      · have := hgr a (List.mem_cons_of_mem _ ha); simp at this; obtain ⟨_, rfl⟩ := this; simp at ha
    · rcases List.mem_append.mp ha with ha | ha
      · rcases hk5 a sz ha with ⟨rfl, _⟩ | ⟨rfl, ha1, rfl⟩
        · simp [Frame.final] at hf'
        · obtain ⟨tys, hty, heq⟩ := has (a - 1) sz (by simp)
          cases tys with
          | nil => simp at heq; obtain ⟨_, rfl⟩ := heq; exact ⟨[], by simp, rfl⟩
          | cons t tys => simp at heq; obtain ⟨rfl, _⟩ := heq; simp [Frame.isTy] at hty
      · obtain ⟨tys, hty, heq⟩ := has a sz (List.mem_cons_of_mem _ ha)
        cases tys with
        | nil => simp at heq; obtain ⟨rfl, rfl⟩ := heq; simp at ha
        | cons t tys =>
          simp at heq; obtain ⟨rfl, rfl⟩ := heq
          refine ⟨k ++ tys, fun x hx => ?_, by simp⟩
          rcases List.mem_append.mp hx with hx | hx
          · exact hk3 (hty f (by simp)) x hx
          · exact hty x (by simp [hx])

theorem noPh {f r st} (hs : Shape (f :: r)) (hp : PhOK (f :: r) st) (hf : f.isTy = false) (hg : ∀ a, f ≠ .group a)
    (ha : ∀ a sz, f ≠ .assign a sz) : ∀ bd ∈ st.binds, bd.sh.isSome := by
  intro bd hbd
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbd
  cases hsh : st.binds[i].sh with
  | some _ => rfl
  | none =>
    exfalso
    obtain ⟨a, _, hw | ⟨sz, hw⟩⟩ := hp i hi hsh
    · have := hs.2.1 a hw; simp at this; exact hg a this.1
    · obtain ⟨tys, hty, heq⟩ := hs.2.2 a sz hw
      cases tys with
      | nil => simp at heq; exact ha a sz heq.1
      | cons t tys => simp at heq; obtain ⟨rfl, _⟩ := heq; rw [hty f (by simp)] at hf; simp at hf

theorem ph_of_all {fs st} (h : ∀ bd ∈ st.binds, bd.sh.isSome) : PhOK fs st := by
  intro i hi hn
  have := h _ (List.getElem_mem hi); rw [hn] at this; simp at this

theorem ph_same {f r k st st'} (hp : PhOK (f :: r) st) (hb : st'.binds = st.binds) (hf : ∀ a, f ≠ .group a ∧ ∀ sz, f ≠ .assign a sz) :
    PhOK (k ++ r) st' := by
  intro i hi hn
  rw [hb] at hi
  have hn' : st.binds[i].sh = none := by simpa [hb] using hn
  obtain ⟨a, hai, hw | hw⟩ := hp i hi hn'
  · rcases List.mem_cons.mp hw with hw | hw
    · exact absurd hw.symm (hf a).1
    · exact ⟨a, hai, Or.inl (List.mem_append_right _ hw)⟩
  · obtain ⟨sz, hw⟩ := hw
    rcases List.mem_cons.mp hw with hw | hw
    · exact absurd hw.symm ((hf a).2 sz)
    · exact ⟨a, hai, Or.inr ⟨sz, List.mem_append_right _ hw⟩⟩

theorem ph_group {a st k st'} (h : stepF (.group a) st = some (k, st')) (hab : a ≤ st.binds.length)
    (hp : PhOK [.group a] st) : PhOK k st' := by
  step_norm
  · intro i hi hn
    simp at hi
    by_cases hlt : i < st.binds.length
    · have hn' : st.binds[i].sh = none := by simpa [List.getElem_append_left hlt] using hn
      obtain ⟨a', hai, hw | ⟨_, hw⟩⟩ := hp i hlt hn' <;> simp at hw
      exact ⟨a', hai, Or.inl (by simp [hw])⟩
    · exact ⟨a, by omega, Or.inl (by simp)⟩
  · intro i hi hn
    obtain ⟨a', hai, hw | ⟨_, hw⟩⟩ := hp i hi hn <;> simp at hw
    subst hw
    exact ⟨_, hai, Or.inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩⟩

theorem ph_assign {a sz st k st'} (h : stepF (.assign a sz) st = some (k, st'))
    (hp : PhOK [.assign a sz, .binders] st) : PhOK (k ++ [.binders]) st' := by
  step_norm
  · intro i hi hn
    obtain ⟨a', hai, hw | ⟨_, hw⟩⟩ := hp i hi hn <;> simp at hw
    omega
  all_goals
    intro i hi hn
    simp at hi
    have hne : i ≠ a := by
      rintro rfl; simp at hn
    have hn' : st.binds[i].sh = none := by simpa [List.getElem_set, Ne.symm hne] using hn
    obtain ⟨a', hai, hw | ⟨_, hw⟩⟩ := hp i hi hn' <;> simp at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨_, Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hai (Ne.symm hne)), Or.inr ⟨_, List.mem_append_left _ (List.mem_singleton_self _)⟩⟩

theorem wf_gen {f : Frame} {r k : List Frame} {st st' : St} {g1 : G} (hs : Shape (f :: r)) (he : effF st.ctx f st.g = some g1) (hg : (effL st.ctx r g1).isSome)
    (hgh : ∃ g2, effL st'.ctx k st'.g = some g2 ∧ (f.final = true ∨ g1.le g2)) (hk : KOK f k)
    (hr : f.final = false → ∀ g g', g.le g' → (effL st.ctx r g).isSome → (effL st'.ctx r g').isSome)
    (hsi : SInv st') (hph : PhOK (k ++ r) st') : WF (k ++ r) st' := by
  refine ⟨?_, shape_step hs hk, hph, hsi⟩
  obtain ⟨g2, hk2, hfin⟩ := hgh
  rw [effL_append, hk2]
  simp only [Option.bind_some]
  cases hf : f.final
  · rcases hfin with hfin | hfin
    · simp [hf] at hfin
    · exact hr hf g1 g2 hfin hg
  · have := (finalsLast_cons hs.1).2 hf; subst this; simp [effL]

theorem hr_ctx {f : Frame} {r : List Frame} {st st' : St} (hc : st'.ctx = st.ctx) : f.final = false → ∀ g g', g.le g' → (effL st.ctx r g).isSome → (effL st'.ctx r g').isSome :=
  fun _ _ _ hl h => by rw [hc]; exact effL_mono h hl

theorem hr_final {f : Frame} {r : List Frame} {st st' : St} (hf : f.final = true) : f.final = false → ∀ g g', g.le g' → (effL st.ctx r g).isSome → (effL st'.ctx r g').isSome :=
  fun h => by rw [hf] at h; cases h

theorem wf_step {f r k st st'} (h : stepF f st = some (k, st')) (hw : WF (f :: r) st) : WF (k ++ r) st' := by
  obtain ⟨hg, hs, hp, hi⟩ := hw
  simp only [effL] at hg
  cases he : effF st.ctx f st.g with
  | none => simp [he] at hg
  | some g1 =>
  rw [he] at hg
  simp only [Option.bind_some] at hg
  have hr0 : f.final = true → r = [] := (finalsLast_cons hs.1).2
  cases f with
  | expr m tl => exact wf_gen hs he hg (gh_expr h hi.1 he) (ks_expr h) (hr_ctx (cx_expr h)) (si_expr h he hi) (ph_of_all (bs_expr h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | binLoop m => exact wf_gen hs he hg (gh_binLoop h hi.1 he) (ks_binLoop h) (hr_ctx (cx_binLoop h)) (si_binLoop h he hi) (ph_of_all (bs_binLoop h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | prim tl => exact wf_gen hs he hg (gh_prim h hi.1 he) (ks_prim h) (hr_ctx (cx_prim h)) (si_prim h he hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))) (ph_of_all (bs_prim h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | rparen => exact wf_gen hs he hg (gh_rparen h hi.1 he) (ks_rparen h) (hr_ctx (cx_rparen h)) (si_rparen h he hi) (ph_same hp (bt_rparen h) (by intro _; exact ⟨(by intro h; cases h), (by intro _ h; cases h)⟩))
  | mkBin op => exact wf_gen hs he hg (gh_mkBin h hi.1 he) (ks_mkBin h) (hr_ctx (cx_mkBin h)) (si_mkBin h he hi) (ph_of_all (bs_mkBin h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | ifCmp tl => exact wf_gen hs he hg (gh_ifCmp h hi.1 he) (ks_ifCmp h) (hr_ctx (cx_ifCmp h)) (si_ifCmp h he hi) (ph_of_all (bs_ifCmp h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | ifThen c tl => exact wf_gen hs he hg (gh_ifThen h hi.1 he) (ks_ifThen h) (hr_ctx (cx_ifThen h)) (si_ifThen h he hi) (ph_of_all (bs_ifThen h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | ifElse => exact wf_gen hs he hg (gh_ifElse h hi.1 he) (ks_ifElse h) (hr_ctx (cx_ifElse h)) (si_ifElse h he hi) (ph_of_all (bs_ifElse h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | mkIte c => exact wf_gen hs he hg (gh_mkIte h hi.1 he) (ks_mkIte h) (hr_ctx (cx_mkIte h)) (si_mkIte h he hi) (ph_of_all (bs_mkIte h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | letSemi x tl => exact wf_gen hs he hg (gh_letSemi h hi.1 he) (ks_letSemi h) (hr_ctx (cx_letSemi h)) (si_letSemi h he hi) (ph_of_all (bs_letSemi h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | letEnd s d => exact wf_gen hs he hg (gh_letEnd h hi.1 he) (ks_letEnd h) (hr_ctx (cx_letEnd h)) (si_letEnd h he hi) (ph_of_all (bs_letEnd h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | parenClose => exact wf_gen hs he hg (gh_parenClose h hi.1 he) (ks_parenClose h) (hr_ctx (cx_parenClose h)) (si_parenClose h he hi) (ph_of_all (bs_parenClose h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | letStart tl => exact wf_gen hs he hg (gh_letStart h hi.1 he) (ks_letStart h) (hr_ctx (cx_letStart h)) (si_letStart h he hi) (ph_of_all (bs_letStart h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | mkPair => exact wf_gen hs he hg (gh_mkPair h hi.1 he) (ks_mkPair h) (hr_ctx (cx_mkPair h)) (si_mkPair h he hi) (ph_of_all (bs_mkPair h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | argAtom => exact wf_gen hs he hg (gh_argAtom h hi.1 he) (ks_argAtom h) (hr_ctx (cx_argAtom h)) (si_argAtom h he hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))) (ph_of_all (bs_argAtom h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | args c n => exact wf_gen hs he hg (gh_args h hi.1 he) (ks_args h) (hr_ctx (cx_args h)) (si_args h he hi) (ph_of_all (bs_args h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | mkCallN c d => exact wf_gen hs he hg (gh_mkCallN h hi.1 he) (ks_mkCallN h) (hr_ctx (cx_mkCallN h)) (si_mkCallN h he hi) (ph_of_all (bs_mkCallN h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | selfArgs => exact wf_gen hs he hg (gh_selfArgs h hi.1 he) (ks_selfArgs h) (hr_ctx (cx_selfArgs h)) (si_selfArgs h he hi) (ph_of_all (bs_selfArgs h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | argCheck c n => exact wf_gen hs he hg (gh_argCheck h hi.1 he) (ks_argCheck h) (hr_ctx (cx_argCheck h)) (si_argCheck h he hi) (ph_of_all (bs_argCheck h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | mkCall c n => exact wf_gen hs he hg (gh_mkCall h hi.1 he) (ks_mkCall h) (hr_ctx (cx_mkCall h)) (si_mkCall h he hi) (ph_of_all (bs_mkCall h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | shiftNum op => exact wf_gen hs he hg (gh_shiftNum h hi.1 he) (ks_shiftNum h) (hr_ctx (cx_shiftNum h)) (si_shiftNum h he hi) (ph_of_all (bs_shiftNum h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | letPairX tl => exact wf_gen hs he hg (gh_letPairX h hi.1 he) (ks_letPairX h) (hr_ctx (cx_letPairX h)) (si_letPairX h he hi) (ph_of_all (bs_letPairX h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | letPairY x tl => exact wf_gen hs he hg (gh_letPairY h hi.1 he) (ks_letPairY h) (hr_ctx (cx_letPairY h)) (si_letPairY h he hi) (ph_of_all (bs_letPairY h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | stash x => exact wf_gen hs he hg (gh_stash h hi.1 he) (ks_stash h) (hr_ctx (cx_stash h)) (si_stash h he hi) (ph_of_all (bs_stash h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | letPairSemi y tl => exact wf_gen hs he hg (gh_letPairSemi h hi.1 he) (ks_letPairSemi h) (hr_ctx (cx_letPairSemi h)) (si_letPairSemi h he hi) (ph_of_all (bs_letPairSemi h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | mkCont f n => exact wf_gen hs he hg (gh_mkCont h hi.1 he) (ks_mkCont h) (hr_ctx (cx_mkCont h)) (si_mkCont h he hi) (ph_of_all (bs_mkCont h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | argName => exact wf_gen hs he hg (gh_argName h hi.1 he) (ks_argName h) (hr_ctx (cx_argName h)) (si_argName h he hi) (ph_of_all (bs_argName h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | defs => exact wf_gen hs he hg (gh_defs h hi.1 he) (ks_defs h) (hr_final rfl) (si_defs h he hi) (ph_of_all (bs_defs h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | tyAtom => exact wf_gen hs he hg (gh_tyAtom h hi.1 he) (ks_tyAtom h) (hr_ctx (cx_tyAtom h)) (si_tyAtom h he hi) (ph_same hp (bt_tyAtom h) (by intro _; exact ⟨(by intro h; cases h), (by intro _ h; cases h)⟩))
  | tyCross => exact wf_gen hs he hg (gh_tyCross h hi.1 he) (ks_tyCross h) (hr_ctx (cx_tyCross h)) (si_tyCross h he hi) (ph_same hp (bt_tyCross h) (by intro _; exact ⟨(by intro h; cases h), (by intro _ h; cases h)⟩))
  | tyPair l => exact wf_gen hs he hg (gh_tyPair h hi.1 he) (ks_tyPair h) (hr_ctx (cx_tyPair h)) (si_tyPair h he hi) (ph_same hp (bt_tyPair h) (by intro _; exact ⟨(by intro h; cases h), (by intro _ h; cases h)⟩))
  | binders => exact wf_gen hs he hg (gh_binders h hi.1 he) (ks_binders h) (hr_final rfl) (si_binders h he hi) (ph_of_all (bs_binders h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | group a => exact wf_gen hs he hg (gh_group h hi.1 he) (ks_group h) (hr_final rfl) (si_group h he hi) (by have := hr0 rfl; subst this; simp only [List.append_nil]; exact ph_group h (by simp only [effF, St.g] at he; split at he; assumption; simp at he) hp)
  | assign a sz => exact wf_gen hs he hg (gh_assign h hi.1 he) (ks_assign h) (fun _ _ _ _ _ => by obtain ⟨tys, _, heq⟩ := hs.2.2 _ _ (List.mem_cons_self ..); cases tys with | nil => (simp at heq; obtain ⟨_, rfl⟩ := heq; simp [effL, effF]) | cons t _ => (simp at heq; obtain ⟨rfl, _⟩ := heq; simp [Frame.isTy] at *)) (si_assign h he hi) (by obtain ⟨tys, hty, heq⟩ := hs.2.2 _ _ (List.mem_cons_self ..); cases tys with | nil => (simp at heq; obtain ⟨_, rfl⟩ := heq; exact ph_assign h hp) | cons t _ => (simp at heq; obtain ⟨rfl, _⟩ := heq; simp [Frame.isTy] at hty))
  | plainBody => exact wf_gen hs he hg (gh_plainBody h hi.1 he) (ks_plainBody h) (hr_final rfl) (si_plainBody h he hi) (ph_of_all (bs_plainBody h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | afterColon => exact wf_gen hs he hg (gh_afterColon h hi.1 he) (ks_afterColon h) (hr_final rfl) (si_afterColon h he hi) (ph_of_all (bs_afterColon h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | stateTy => exact wf_gen hs he hg (gh_stateTy h hi.1 he) (ks_stateTy h) (hr_final rfl) (si_stateTy h he hi) (ph_of_all (bs_stateTy h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | armsStart => exact wf_gen hs he hg (gh_armsStart h hi.1 he) (ks_armsStart h) (hr_final rfl) (si_armsStart h he hi) (ph_of_all (bs_armsStart h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | armBind stp i => exact wf_gen hs he hg (gh_armBind h hi.1 he) (ks_armBind h) (hr_final rfl) (si_armBind h he hi) (ph_of_all (bs_armBind h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | zeroDone => exact wf_gen hs he hg (gh_zeroDone h hi.1 he) (ks_zeroDone h) (hr_final rfl) (si_zeroDone h he hi) (ph_of_all (bs_zeroDone h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | mkLoop => exact wf_gen hs he hg (gh_mkLoop h hi.1 he) (ks_mkLoop h) (hr_ctx (cx_mkLoop h)) (si_mkLoop h he hi) (ph_of_all (bs_mkLoop h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | defEnd => exact wf_gen hs he hg (gh_defEnd h hi.1 he) (ks_defEnd h) (hr_final rfl) (si_defEnd h he hi) (ph_of_all (bs_defEnd h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | flat nd => exact wf_gen hs he hg (gh_flat h hi.1 he) (ks_flat h) (hr_ctx (cx_flat h)) (si_flat h he hi) (ph_of_all (bs_flat h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | flatL ns => exact wf_gen hs he hg (gh_flatL h hi.1 he) (ks_flatL h) (hr_ctx (cx_flatL h)) (si_flatL h he hi) (ph_of_all (bs_flatL h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | defClose => exact wf_gen hs he hg (gh_defClose h hi.1 he) (ks_defClose h) (hr_final rfl) (si_defClose h he hi) (ph_of_all (bs_defClose h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))
  | tupRest => exact wf_gen hs he hg (gh_tupRest h hi.1 he) (ks_tupRest h) (hr_ctx (cx_tupRest h)) (si_tupRest h he hi) (ph_of_all (bs_tupRest h hi (noPh hs hp rfl (by intro _ h; cases h) (by intro _ _ h; cases h))))


/-- every configuration reachable from the initial one is WF -/
theorem wf_reach {c d : List Frame × St} (h : Star c d) : WF c.1 c.2 → WF d.1 d.2 := by
  induction h with
  | refl => exact id
  | @step c0 d0 e0 hs _ ih =>
    intro hc
    match c0, hs, hc with
    | (f :: r, st), hs, hc =>
      obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
      exact ih (wf_step h1 hc)
    | ([], st), hs, _ => simp [stepS] at hs

theorem wf_star {toks fs st} (h : Star ([.defs], init toks) (fs, st)) : WF fs st := wf_reach h (wf_init toks)

/-- for box C: in a WF configuration the top frame's precondition holds (operand depth, `ty` set, index ranges, …) -/
theorem wf_pre {f r st} (h : WF (f :: r) st) : ∃ g1, effF st.ctx f st.g = some g1 := by
  have := h.ghost; simp only [effL] at this
  cases he : effF st.ctx f st.g with
  | none => simp [he] at this
  | some g1 => exact ⟨g1, rfl⟩

end ParRun
