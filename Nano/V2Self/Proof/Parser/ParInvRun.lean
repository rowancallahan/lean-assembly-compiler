/- Nano/V2Self/Proof/Parser/ParInvRun: `api_of_rep` (parser lead) — box C's `Rep` plus Layer-2 reachability meets `RepAPI`.
The handlers' side conditions come from the reachability invariants (`WF` / `wf_pre`, `CInv`, `DInv`, `StkInv`, `ArenaInv`,
`CallInv`); `WF`-independent ones are in ParRunBnd (parser lead) and ParRunObl (box B). -/
import Nano.V2Self.Proof.Parser.ParRunSmall
import Nano.V2Self.Proof.Parser.ParInvInit
import Nano.V2Self.Proof.Parser.ParInvSelf
import Nano.V2Self.Proof.Parser.ParInvDefs
import Nano.V2Self.Proof.Parser.ParInvHdr
import Nano.V2Self.Proof.Parser.ParInvFinish
import Nano.V2Self.Proof.Parser.ParInvArm
import Nano.V2Self.Proof.Parser.ParInvAssign
import Nano.V2Self.Proof.Parser.ParInvBind
import Nano.V2Self.Proof.Parser.ParInvGroup
import Nano.V2Self.Proof.Parser.ParInvTy
import Nano.V2Self.Proof.Parser.ParInvPair
import Nano.V2Self.Proof.Parser.ParInvLet
import Nano.V2Self.Proof.Parser.ParInvLetSemi
import Nano.V2Self.Proof.Parser.ParInvLetEnd
import Nano.V2Self.Proof.Parser.ParInvLetPair
import Nano.V2Self.Proof.Parser.ParInvIte
import Nano.V2Self.Proof.Parser.ParInvMkPair
import Nano.V2Self.Proof.Parser.ParInvNum
import Nano.V2Self.Proof.Parser.ParInvPrimary
import Nano.V2Self.Proof.Parser.ParInvExpr
import Nano.V2Self.Proof.Parser.ParInvExpr2
import Nano.V2Self.Proof.Parser.ParInvBuild
import Nano.V2Self.Proof.Parser.ParInvCall
import Nano.V2Self.Proof.Parser.ParInvArg
import Nano.V2Self.Proof.Parser.ParInvAtom
import Nano.V2Self.Proof.Parser.ParInvArgName
import Nano.V2Self.Proof.Parser.ParInvPrev
import Nano.V2Self.Proof.Parser.ParInvApi
import Nano.V2Self.Proof.Parser.ParRunWFPres
import Nano.V2Self.Proof.Parser.ParRunCInv
import Nano.V2Self.Proof.Parser.ParRunShape
import Nano.V2Self.Proof.Parser.ParRunArena
import Nano.V2Self.Proof.Parser.ParRunDef
import Nano.V2Self.Proof.Parser.ParRunProg
import Nano.V2Self.Proof.Parser.ParRunBnd
import Nano.V2Self.Proof.Parser.ParRunObl
set_option backward.isDefEq.respectTransparency false
namespace ParInv
open C BufL ParSpec ParRun

abbrev Reach (toks : List Tok) (fs : List Frame) (st : St) : Prop := Star ([.defs], init toks) (fs, st)

theorem isFlat_eq : Frame.isFlat = Frame.isFl := by funext f; cases f <;> rfl

theorem reach_inDef {toks : List Tok} {f : Frame} {fs : List Frame} {st : St} (hR : Reach toks (f :: fs) st) (hf : f ≠ .defs) :
    inDefF fs = true := by
  have D := dinv_reach hR
  simp only [inDefF, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  intro x hx
  cases x with
  | defs => have := D (List.mem_cons_of_mem _ hx); simp at this; exact absurd this.1 hf
  | _ => rfl

theorem reach_noflat {toks : List Tok} {f : Frame} {fs : List Frame} {st : St} (hR : Reach toks (f :: fs) st)
    (hf : f.isFl = false) : fs.all (fun f => !f.isFlat) = true := by
  rw [isFlat_eq]; exact cinv_noflat (hR.cinv (cinv_init _)) hf


theorem tokL_kw {ts : Buf} {toks : List Tok} (hT : TokL ts toks) : ∀ t, Tok.k t ∈ toks → t < 2 ^ 64 := by
  induction hT with
  | nil => intro t ht; simp at ht
  | kw x _ _ _ _ ih =>
    intro t ht; rcases List.mem_cons.mp ht with e | e
    · cases e; exact x.toNat_lt
    · exact ih t e
  | num _ _ _ _ ih =>
    intro t ht; rcases List.mem_cons.mp ht with e | e
    · cases e
    · exact ih t e
  | id _ _ _ ih =>
    intro t ht; rcases List.mem_cons.mp ht with e | e
    · cases e
    · exact ih t e

theorem rep_tok0 {h ts : Buf} {st : St} {fs : List Frame} {toks : List Tok} (hT : TokL ts toks) (r : Rep h ts st fs) :
    TokAt h 0 toks := tokAt_of r.1.1 r.2.1 r.1.2.2.2 hT 0 (Nat.zero_le _) rfl

/-- `hprev` of task 73 from the reachability obligation "the token before `afterColon` is no numeral" -/
theorem hprev_of {h ts : Buf} {toks : List Tok} (hT : TokL ts toks) {fs : List Frame} {st : St}
    (r : Rep h ts st (.afterColon :: fs)) (hR : Reach toks (.afterColon :: fs) st) :
    bget h (d11 + bget h 3 - 1) = 35 → prevTok st = some (.k 35) := by
  intro hc
  obtain ⟨t, ht, hnum⟩ := reach_prev hR
  obtain ⟨hall, ⟨pre, hpre⟩⟩ := hR.toks
  simp only [ParRun.init] at hall hpre
  have hp : prevTok st = pre.getLast? := by
    simp only [prevTok, hall, ← hpre, List.length_append, Nat.add_sub_cancel, List.take_left']
  rw [hp] at ht ⊢
  have hne : pre ≠ [] := by intro e; simp [e] at ht
  obtain ⟨hn, _, _⟩ := rep_bounds r
  have x : TokAt h 0 (pre ++ st.toks) := by rw [hpre]; exact rep_tok0 hT r
  rcases prev_cell hn x r.2.2.2.1 hne with ⟨t', e1, e2⟩ | ⟨y, e1, e2⟩ | ⟨v, e1⟩
  · rw [e1] at ht ⊢
    have hm : Tok.k t' ∈ toks := by rw [← hpre]; exact List.mem_append_left _ (List.mem_of_getLast? e1)
    have := tokL_kw hT t' hm
    rw [show d11 + (bget h 3 - 1) = d11 + bget h 3 - 1 by rw [UInt64.sub_eq_add_neg, UInt64.sub_eq_add_neg, UInt64.add_assoc]] at e2
    rw [hc] at e2
    have := congrArg UInt64.toNat e2; simp at this
    rw [show t' = 35 by omega]
  · rw [show d11 + (bget h 3 - 1) = d11 + bget h 3 - 1 by rw [UInt64.sub_eq_add_neg, UInt64.sub_eq_add_neg, UInt64.add_assoc]] at e2
    rw [hc] at e2; exact absurd e2 (by decide)
  · rw [e1] at ht; cases ht; exact absurd rfl (hnum v)

/-- **one running step** of every frame but `.defs` / `.defClose` -/
theorem step_sim {h ts : Buf} {toks : List Tok} 
    (hprev : ∀ {fs st}, Rep h ts st (.afterColon :: fs) → Reach toks (.afterColon :: fs) st →
      bget h (d11 + bget h 3 - 1) = 35 → prevTok st = some (.k 35))
    {f : Frame} {fs : List Frame} {st : St} (r : Rep h ts st (f :: fs)) (hR : Reach toks (f :: fs) st)
    (hf : f ≠ .defs) (hf2 : f ≠ .defClose) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF f st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  have W := wf_star hR
  obtain ⟨g1, hg⟩ := wf_pre W
  have hD := reach_inDef hR hf
  have hN := fun (e : f.isFl = false) => reach_noflat hR e
  have hsv := W.inv.1
  have hSm := hR.small (small_init _)
  obtain ⟨sm1, sm2, sm3, sm4, -, sm6, -, -, sm9⟩ := hSm
  dsimp only at sm1 sm2 sm3 sm4 sm6 sm9
  have hv4 : st.vals.length ≤ 4096 := r.2.2.2.2.2.2.2.1.2.2.2.1
  have hnni : st.cur.nni < 2 ^ 63 := by
    have rD := r.2.2.2.2.2.2.1
    have hfd : f.isDefs = false := by cases f <;> first | rfl | exact absurd rfl hf
    have hD2 : inDefF (f :: fs) = true := by
      simp only [inDefF, List.all_cons, hfd, Bool.not_false, Bool.true_and]; exact hD
    rw [hD2] at rD
    have := rD.2.2.2.2.1.1.1.2.2.2.2.2.2.1
    have := reach_nni hR
    unfold NniOK at this; omega
  cases f with
  | expr m md => exact h_expr r hs
  | binLoop m => simp [effF, St.g] at hg; exact h_binLoop r (by intro e; simp [e] at hg) hs
  | prim md => exact h_prim r (cinv_mode (hR.cinv (cinv_init _))) hD (hN rfl) hs
  | rparen => exact h_rparen r hs
  | mkBin op => exact h_mkBin r (hN rfl) hs
  | ifCmp tl => exact h_ifCmp r hs
  | ifThen c tl => exact h_ifThen r hs
  | ifElse => exact h_ifElse r hs
  | mkIte c => exact h_mkIte r (hN rfl) hs
  | letSemi x tl => simp [effF, St.g] at hg; exact h_letSemi r (by intro e; simp [e] at hg) sm1 sm6 hs
  | letEnd sl d =>
    simp [effF, St.g] at hg; exact h_letEnd r hg.1.2 (hN rfl) hs
  | parenClose => exact h_parenClose r hs
  | letStart tl => exact h_letStart r hs
  | mkPair => simp [effF, St.g] at hg; exact h_mkPair r (hN rfl) hg.1 hsv sm6 hs
  | argAtom => exact h_argAtom r (hN rfl) hs
  | args c k => exact h_args r hs
  | mkCallN c d => simp [effF, St.g] at hg; exact h_mkCallN r hg.1.1 hs
  | selfArgs => exact h_selfArgs r hD (reach_selfP hR) hs
  | argCheck c k =>
    simp [effF, St.g] at hg
    refine h_argCheck r hD hg.1.1 ?_ ?_ hs
    · have := hg.1.2.1; cases c <;> simpa [arity, Ctx.arity, St.ctx] using this
    · cases c with
      | df j => have := hg.1.2.2; simpa [calleeOK, Ctx.callee, St.ctx] using this
      | pr p => exact reach_prim32 hR ⟨k, Or.inl rfl⟩
  | mkCall c n =>
    simp [effF, St.g] at hg
    refine h_mkCall r hD (hN rfl) (by have := hg.1.1; omega) ?_ hs
    cases c with
    | df j => have := hg.1.2; simp [calleeOK, Ctx.callTgt, St.ctx] at this ⊢; omega
    | pr p => exact reach_prim32 hR ⟨n, Or.inr rfl⟩
  | shiftNum op => exact h_shiftNum r (hN rfl) hs
  | letPairX tl => exact h_letPairX r hs
  | letPairY x tl => exact h_letPairY r hs
  | stash x => exact h_stash r hs
  | letPairSemi y tl =>
    simp [effF, St.g] at hg; exact h_letPairSemi r (by intro e; simp [e] at hg) (cinv_stash (hR.cinv (cinv_init _))) sm1 sm6 hs
  | mkCont f' k =>
    simp [effF, St.g] at hg
    exact h_mkCont r hD (hN rfl) (by have := hg.1.2.1; simp [St.ctx, rows] at this; omega) (by have := hg.1.1; omega) hs
  | argName => exact h_argName r (hN rfl) hs
  | defs => exact absurd rfl hf
  | tyAtom => exact h_tyAtom r hs
  | tyCross => simp [effF, St.g] at hg; exact h_tyCross r hg.1 hs
  | tyPair l => simp [effF, St.g] at hg; exact h_tyPair r hg.1 (sm9 l (List.mem_cons_self ..)) sm3 hs
  | binders => exact h_binders r hs
  | group a => exact h_group r hs
  | assign i sz => simp [effF, St.g] at hg; exact h_assign r hD hg.1.1 (reach_assignTy hR) hnni sm1 sm3 hs
  | plainBody =>
    simp [effF, St.g] at hg
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hg.1
    obtain ⟨st', a, b⟩ := h_plainBody r hD hw hs; exact ⟨_, st', a, b⟩
  | afterColon =>
    simp [effF, St.g] at hg
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hg.1
    exact h_afterColon r hD hw hnni (hprev r hR) hs
  | stateTy =>
    simp [effF, St.g] at hg
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hg.1.1
    exact h_stateTy r hD hw hnni sm2 sm3 hs
  | armsStart =>
    simp [effF, St.g] at hg
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hg.1.1
    exact h_armsStart r hD hw hs
  | armBind stp b0 =>
    simp [effF, St.g] at hg
    exact h_armBind r hD (by have := hg.1.2.1; simpa [Ctx.npar, St.ctx, rows] using this) hs
  | zeroDone => simp [effF, St.g] at hg; exact h_zeroDone r hD (by intro e; simp [e] at hg) hs
  | mkLoop => exact h_mkLoop r hD (hN rfl) hs
  | defEnd => exact h_defEnd r hD sm1 sm4 hs
  | flat n => obtain ⟨a, b, c⟩ := reach_flat hR; exact h_flat r hD (by have := (rep_bounds r).2.2; omega) b c hs
  | flatL ns => exact h_flatL r hD hs
  | defClose => exact absurd rfl hf2
  | tupRest => exact h_tupRest r hs


/-- the relation handed to `RepAPI`: box C's `Rep`, reachable, running -/
def RepR (ts : Buf) (toks : List Tok) (h : Buf) (fs : List Frame) (st : St) : Prop :=
  Rep h ts st fs ∧ Reach toks fs st ∧ st.acc = false

theorem reach_defs {toks : List Tok} {fs : List Frame} {st : St} (hR : Reach toks (.defs :: fs) st) : fs = [] := by
  have := dinv_reach hR (List.mem_cons_self ..); simp at this; exact this

theorem reach_defClose {toks : List Tok} {fs : List Frame} {st : St} (hR : Reach toks (.defClose :: fs) st) : fs = [] := by
  have := (wf_star hR).shape.1
  cases fs with
  | nil => rfl
  | cons x r => simp [finalsLast, Frame.final] at this

theorem status_acc {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (e : bget h 0 = 1) : st.acc = false := by
  have := r.2.2.1; rw [e] at this
  cases ha : st.acc
  · rfl
  · rw [ha] at this; exact absurd this (by decide)

theorem status_acc2 {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (e : bget h 0 = 2) : st.acc = true := by
  have := r.2.2.1; rw [e] at this
  cases ha : st.acc
  · rw [ha] at this; exact absurd this (by decide)
  · rfl

/-- the step of every frame (incl. `.defs` / `.defClose`) as long as the machine keeps running or is not `.defs` -/
theorem step_any {h ts : Buf} {toks : List Tok} (hT : TokL ts toks) {f : Frame} {fs : List Frame} {st : St}
    (r : RepR ts toks h (f :: fs) st) (hf : f ≠ .defs) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF f st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨r, hR, _⟩ := r
  by_cases hc : f = .defClose
  · subst hc; have e := reach_defClose hR; subst e
    obtain ⟨k, st', a, b⟩ := h_defClose r; exact ⟨k, st', a, by simpa using b⟩
  · exact step_sim (fun r hR => hprev_of hT r hR) r hR hf hc hs

/-- **Layer 3 meets `RepAPI`** -/
theorem api_of_rep (ts : Buf) (toks : List Tok) (hT : TokL ts toks) (hts : ts.length < 2 ^ 24) :
    RepAPI ts toks (RepR ts toks) where
  init := ⟨rep_init ts toks hT hts, .refl _, rfl⟩
  running := fun r => by have := r.1.2.2.1; rw [r.2.2] at this; simpa using this
  ntasks := fun r => ntasks_of r.1.2.2.2.2.2.2.2.2.2.2.2.2.2
  step := by
    intro h f fs st r s1
    have hs : bget (step h) 0 ≠ 0 := by rw [s1]; decide
    by_cases hd : f = .defs
    · subst hd
      obtain ⟨r0, hR, ha⟩ := r
      have e := reach_defs hR; subst e
      obtain ⟨k, st', a, b⟩ := (h_defs r0 isInpW ((hR.inv (init_inv toks)).1) (callInv_star hR) ha hs).1 s1
      exact ⟨k, st', a, by simpa using b, by simpa using hR.trans (Star.one (fs := []) a), status_acc b s1⟩
    · obtain ⟨k, st', a, b⟩ := step_any hT r hd hs
      exact ⟨k, st', a, b, r.2.1.trans (Star.one a), status_acc b s1⟩
  accept := by
    intro h f fs st r s2
    have hs : bget (step h) 0 ≠ 0 := by rw [s2]; decide
    by_cases hd : f = .defs
    · subst hd
      obtain ⟨r0, hR, ha⟩ := r
      have e := reach_defs hR; subst e
      obtain ⟨st', a, hacc, hl, hdrop, hD⟩ := (h_defs r0 isInpW ((hR.inv (init_inv toks)).1) (callInv_star hR) ha hs).2 s2
      have hR' : Reach toks [] st' := by simpa using hR.trans (Star.one (fs := []) a)
      exact ⟨st', a, rfl, hacc, hl, fun _ => hdrop, fun h12 hm => main_of hD h12 hm (reach_names hT hR')⟩
    · exfalso
      obtain ⟨k, st', a, b⟩ := step_any hT r hd hs
      have := (stepF_shape a).2 (status_acc2 b s2)
      rw [r.2.2] at this; simp [hd] at this


/-- **the parser theorem** -/
theorem parserSound_main {ts : Buf} {toks : List Tok} (hT : TokL ts toks) (hts : ts.length < 2 ^ 24) :
    ParserSound ts :=
  parserSound_of (api_of_rep ts toks hT hts) (by omega) (accepts_sound (tokens_of hT))

/-- **ParserSound** for every well-formed token buffer below 2^24 words -/
theorem parserSound {ts : Buf} (hW : TokWF ts) (hts : ts.length < 2 ^ 24) : ParserSound ts := by
  obtain ⟨toks, hT⟩ := hW; exact parserSound_main hT hts

end ParInv
