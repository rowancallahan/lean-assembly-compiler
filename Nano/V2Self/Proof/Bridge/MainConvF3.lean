/- Nano/V2Self/Proof/Bridge/MainConvF3: the failure kinds forward — prims (only a full buffer's push gives `cap`, never `stuck`)
and calls. -/
import Nano.V2Self.Proof.Bridge.MainConvF2

namespace NanoMain
open Templates

theorem fail_prim (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (hX : CtxR cx K) (p : Nat) (as : List ParSpec.Nd)
    (hN : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeFail cx K fsX oc D n) : NodeFail cx K fsX oc D (.prim p as) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H f hT hc hE hA h8 hhb hr h
  cases hT with
  | prim tl hpk hnil =>
    rename_i ps
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨⟨x1, x2⟩, hl, ⟨yF, yE⟩, hfn, -⟩ := hc
    obtain ⟨-, hk⟩ := evL_ok hC tl env hE.ty
    obtain ⟨-, hfc, hfb⟩ := fin_some hfn
    have hNO : ∀ n ∈ as, NodeOK cx K oc D n := fun n h => (hN n h).1
    have hNF := hN
    rcases kinds_cases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp (config := { decide := true }) only [svF, if_true, if_false, leafF] at h
      split at h
      · cases h
      · cases h; exact .inl rfl
    · simp (config := { decide := true }) only [svF, if_true, if_false, fin1F] at h
      rcases bind_err h with h1 | ⟨r1, h1, h2⟩
      · rcases lst_fail cx K fsX hf oc D hC hK2 hW as hNF tl hl hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, bind, Except.bind]⟩
      · have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        simp only [List.nil_append] at hesA; subst hesA
        have kv := hk v' evl'
        have ln := hR1.len
        have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
        obtain ⟨x, rfl⟩ := kOf_w kv
        obtain ⟨u0, hu⟩ := List.length_eq_one_iff.1 (show r1.1.length = 1 by simp at ln; omega)
        rw [hu] at h2; simp [primF1, rdF1, ofO] at h2; try cases h2
    · simp (config := { decide := true }) only [svF, if_true, if_false, leafF] at h
      split at h
      · cases h
      · cases h; exact .inl rfl
    · simp (config := { decide := true }) only [svF, if_true, if_false, fin2F] at h
      rcases bind_err h with h1 | ⟨r1, h1, h2⟩
      · rcases lst_fail cx K fsX hf oc D hC hK2 hW as hNF tl hl hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, bind, Except.bind]⟩
      · have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        simp only [List.nil_append] at hesA; subst hesA
        have kv := hk v' evl'
        have ln := hR1.len
        have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
        obtain ⟨l, x, rfl⟩ := kOf_bw kv
        obtain ⟨a, xw, hu⟩ := len2 (show r1.1.length = 2 by simp at ln; omega)
        obtain ⟨e0, e1, rfl⟩ := len2 (show x2.length = 2 by simp at ln; omega)
        obtain ⟨G, hG⟩ := hok 0 e0 rfl
        simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG
        simp at hG
        have hd : OwnSpec.dest (some (OwnSpec.dsP 4)) 0 = 1 := by simp [OwnSpec.dest, OwnSpec.dsP]
        obtain ⟨hσ, -, -⟩ := own0 hR1 hE1 hS1 hM1 hfc hd (e0 := e0) (l := l) (a := a) rfl rfl (by rw [hu]; rfl) hG
        rw [hu] at h2
        simp (config := { decide := true }) only [primF2F, if_false] at h2
        rcases Nat.lt_or_ge l.length K.κ with hlt | hge
        · obtain ⟨H2, hp, -⟩ := bpush_at (bufAt_of hA1 hσ) hlt xw 0
          have e := map_err h2
          unfold bpushFF at e
          rw [bufInfo_at (bufAt_of hA1 hσ)] at e
          simp only at e
          rw [if_pos (by rw [toNat_ofNat_lt (by have := (bufAt_of hA1 hσ).2.2.2.2.2.1; omega),
            toNat_ofNat_lt (by have := (bufAt_of hA1 hσ).2.2.2.2.2.1; omega)]; exact hlt)] at e
          rw [show (bpushF K.hb a xw (sp - 16) r1.2) = bpushF K.hb a xw 0 r1.2 from rfl, hp] at e
          cases e
        · rw [bpushFF_cap (bufAt_of hA1 hσ) hge] at h2
          cases h2
          refine .inr ⟨rfl, ?_⟩
          have hge' : ¬ l.length < cx.κ := by rw [← hX.κ]; omega
          simp [ev, evl', prim, push, hge', bind, Except.bind]
    · simp (config := { decide := true }) only [svF, if_true, if_false, oneF, bnewF] at h
      have := map_err h
      cases hb : bnewS K.κ ew sp H with
      | some _ => rw [hb] at this; cases this
      | none => rw [hb] at this; cases this; exact .inl rfl
    · simp (config := { decide := true }) only [svF, if_true, if_false, fin1F] at h
      rcases bind_err h with h1 | ⟨r1, h1, h2⟩
      · rcases lst_fail cx K fsX hf oc D hC hK2 hW as hNF tl hl hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, bind, Except.bind]⟩
      · have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        simp only [List.nil_append] at hesA; subst hesA
        have kv := hk v' evl'
        have ln := hR1.len
        have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
        obtain ⟨l, rfl⟩ := kOf_b kv
        obtain ⟨a, hu⟩ := List.length_eq_one_iff.1 (show r1.1.length = 1 by simp at ln; omega)
        obtain ⟨e0, rfl⟩ := List.length_eq_one_iff.1 (show x2.length = 1 by simp at ln; omega)
        obtain ⟨G, hG⟩ := hok 0 e0 rfl
        simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.add_zero] at hG
        have := finC_none1 _ _ _ _ (fun i hi => by simp at hi; subst hi; simp [OwnSpec.dest, OwnSpec.dsP]) hfc; subst this
        have hσ := arg_buf hR1 hE1 hr1 (i := 0) rfl rfl (by rw [hu]; rfl) hG (.inr rfl)
          (fun ho => finB_own2 0 _ hfb 0 e0 rfl ho (by simp [OwnSpec.dest, OwnSpec.dsP]))
        rw [hu] at h2; simp (config := { decide := true }) [primF1, bsize_at (bufAt_of hA1 hσ), ofO] at h2; try cases h2
    · simp (config := { decide := true }) only [svF, if_true, if_false, fin2F] at h
      rcases bind_err h with h1 | ⟨r1, h1, h2⟩
      · rcases lst_fail cx K fsX hf oc D hC hK2 hW as hNF tl hl hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, bind, Except.bind]⟩
      · have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        simp only [List.nil_append] at hesA; subst hesA
        have kv := hk v' evl'
        have ln := hR1.len
        have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
        obtain ⟨l, i, rfl⟩ := kOf_bw kv
        obtain ⟨a, iw, hu⟩ := len2 (show r1.1.length = 2 by simp at ln; omega)
        obtain ⟨e0, e1, rfl⟩ := len2 (show x2.length = 2 by simp at ln; omega)
        obtain ⟨G, hG⟩ := hok 0 e0 rfl
        simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG
        simp at hG
        have := finC_none1 _ _ _ _ (fun j hi => by
          simp at hi; rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [OwnSpec.dest, OwnSpec.dsP]) hfc
        subst this
        have hσ := arg_buf hR1 hE1 hr1 (i := 0) rfl rfl (by rw [hu]; rfl) hG (.inr rfl)
          (fun ho => finB_own2 0 _ hfb 0 e0 rfl ho (by simp [OwnSpec.dest, OwnSpec.dsP]))
        rw [hu] at h2; simp (config := { decide := true }) [primF2F, bget_at (bufAt_of hA1 hσ), ofO] at h2; try cases h2
    · simp (config := { decide := true }) only [svF, if_true, if_false, fin3F] at h
      rcases bind_err h with h1 | ⟨r1, h1, h2⟩
      · rcases lst_fail cx K fsX hf oc D hC hK2 hW as hNF tl hl hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, bind, Except.bind]⟩
      · have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        simp only [List.nil_append] at hesA; subst hesA
        have kv := hk v' evl'
        have ln := hR1.len
        have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
        obtain ⟨l, i, x, rfl⟩ := kOf_bww kv
        obtain ⟨a, iw, xw, hu⟩ := len3 (show r1.1.length = 3 by simp at ln; omega)
        obtain ⟨e0, e1, e2, rfl⟩ := len3 (show x2.length = 3 by simp at ln; omega)
        obtain ⟨G, hG⟩ := hok 0 e0 rfl
        simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG
        simp at hG
        have hd : OwnSpec.dest (some (OwnSpec.dsP 8)) 0 = 1 := by simp [OwnSpec.dest, OwnSpec.dsP]
        obtain ⟨hσ, -, -⟩ := own0 hR1 hE1 hS1 hM1 hfc hd (e0 := e0) (l := l) (a := a) rfl rfl (by rw [hu]; rfl) hG
        obtain ⟨H2, hp, -⟩ := bset_at (bufAt_of hA1 hσ) iw xw 0
        rw [hu] at h2
        simp only at h2
        rw [show (bsetF K.hb a iw xw (sp - 24) r1.2) = bsetF K.hb a iw xw 0 r1.2 from rfl, hp] at h2
        simp [ofO] at h2; try cases h2
    · simp (config := { decide := true }) only [svF, if_true, if_false, fin2F] at h
      rcases bind_err h with h1 | ⟨r1, h1, h2⟩
      · rcases lst_fail cx K fsX hf oc D hC hK2 hW as hNF tl hl hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, bind, Except.bind]⟩
      · have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        simp only [List.nil_append] at hesA; subst hesA
        have kv := hk v' evl'
        have ln := hR1.len
        have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
        obtain ⟨l, x, rfl⟩ := kOf_bw kv
        obtain ⟨a, xw, hu⟩ := len2 (show r1.1.length = 2 by simp at ln; omega)
        obtain ⟨e0, e1, rfl⟩ := len2 (show x2.length = 2 by simp at ln; omega)
        obtain ⟨G, hG⟩ := hok 0 e0 rfl
        simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG
        simp at hG
        have hd : OwnSpec.dest (some (OwnSpec.dsP 9)) 0 = 1 := by simp [OwnSpec.dest, OwnSpec.dsP]
        obtain ⟨hσ, -, -⟩ := own0 hR1 hE1 hS1 hM1 hfc hd (e0 := e0) (l := l) (a := a) rfl rfl (by rw [hu]; rfl) hG
        rw [hu] at h2
        simp (config := { decide := true }) only [primF2F, if_false] at h2
        rcases Nat.lt_or_ge l.length K.κ with hlt | hge
        · obtain ⟨H2, hp, -⟩ := bpush_at (bufAt_of hA1 hσ) hlt xw 0
          have e := map_err h2
          unfold bpushFF at e
          rw [bufInfo_at (bufAt_of hA1 hσ)] at e
          simp only at e
          rw [if_pos (by rw [toNat_ofNat_lt (by have := (bufAt_of hA1 hσ).2.2.2.2.2.1; omega),
            toNat_ofNat_lt (by have := (bufAt_of hA1 hσ).2.2.2.2.2.1; omega)]; exact hlt)] at e
          rw [show (bpushF K.hb a xw (sp - 16) r1.2) = bpushF K.hb a xw 0 r1.2 from rfl, hp] at e
          cases e
        · rw [bpushFF_cap (bufAt_of hA1 hσ) hge] at h2
          cases h2
          refine .inr ⟨rfl, ?_⟩
          have hge' : ¬ l.length < cx.κ := by rw [← hX.κ]; omega
          simp [ev, evl', prim, push, hge', bind, Except.bind]

/-- a def's failure contract: on related arguments, E's kinded def fails only by room, or by cap when `Sem`'s does -/
def DefFail (hb κ : Nat) (Pk : List Kd) (P : List Nat) (f : List W → Except Stop (List W)) (g : SemDX) : Prop :=
  ∀ σ args ws sp H fl, AHeap hb κ H σ → H.top % 8 = 0 → hb ≤ H.top → kOf args = Pk → ArgsR σ P args ws →
    g ws sp H = .error fl → FailOK fl (f args)

def CallFail (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) : Prop :=
  ∀ (i : Nat) P R, oc.ps[i]? = some P → oc.rs[i]? = some R → ∃ f, cx.defs[i]? = some f ∧
    ∀ sg, D[i]? = some sg → DefFail K.hb K.κ sg.1 P f (fsX i)

theorem fail_call (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx)
    (D : List Sig) (hW : RsW oc) (hCF : CallFail cx K fsX oc D) (i : Nat) (as : List ParSpec.Nd)
    (hN : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeFail cx K fsX oc D n) : NodeFail cx K fsX oc D (.call i as) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H fl hT hc hE hA h8 hhb hr h
  cases hT with
  | call tl hd =>
    simp only [OwnSpec.chk] at hc
    split at hc
    · rename_i P R hP hRr
      obtain ⟨⟨x1, x2⟩, hl, h'⟩ := Option.bind_eq_some_iff.1 hc
      obtain ⟨⟨yF, yE⟩, hfn, -⟩ := Option.map_eq_some_iff.1 h'
      simp only [svF, callF] at h
      rcases bind_err h with h1 | ⟨r1, h1, h2⟩
      · rcases lst_fail cx K fsX hf oc D hC hK2 hW as hN tl hl hE hA h8 hhb hr h1 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, he, bind, Except.bind]⟩
      · have hNO : ∀ n ∈ as, NodeOK cx K oc D n := fun n h => (hN n h).1
        have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        simp only [List.nil_append] at hesA; subst hesA
        have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
        obtain ⟨hlP, hfc, hfb⟩ := fin_some hfn
        simp only at hlP hfc hfb
        obtain ⟨hArgs, -, -⟩ := fin_args hR1 hE1 hr1 hS1 hM1 hfc hfb hlP (fun i e he => by simpa using hok i e he)
        obtain ⟨f, hfd, hDF⟩ := hCF i P R hP hRr
        rcases hDF _ hd σ1 v' r1.1 _ r1.2 fl hA1 h81 hb1 ((evL_ok hC tl env hE.ty).2 v' evl') hArgs h2 with h | ⟨rfl, he⟩
        · exact .inl h
        · exact .inr ⟨rfl, by simp [ev, evl', hfd, he, bind, Except.bind]⟩
    · cases hc

mutual
/-- **value mode, every node**: E's kinded semantics fails only by room, or by cap when `ev` does -/
theorem fail_all (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K) (hCR : CallR cx K oc D) (hCF : CallFail cx K fsX oc D) :
    ∀ e : ParSpec.Nd, NodeFail cx K fsX oc D e
  | .const c => fail_const cx K fsX oc D c
  | .loc s w => fail_loc cx K fsX oc D s w
  | .bin op a b => fail_bin cx K fsX hf oc D hW op a b (node_all cx K oc D hRs hW hX hCR a) (node_all cx K oc D hRs hW hX hCR b) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF a) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF b)
  | .ite c a b t e => fail_ite cx K fsX hf oc D hW c a b t e (node_all cx K oc D hRs hW hX hCR a) (node_all cx K oc D hRs hW hX hCR b) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF a) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF b)
      (fail_all cx K fsX hf oc D hRs hW hX hCR hCF t) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF e)
  | .letE s w v b => fail_let cx K fsX hf oc D hW s w v b (node_all cx K oc D hRs hW hX hCR v) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF v) (fail_all cx K fsX hf oc D hRs hW hX hCR hCF b)
  | .pair cs => fail_pair cx K fsX hf oc D hW cs (fails_all cx K fsX hf oc D hRs hW hX hCR hCF cs)
  | .call i as => fail_call cx K fsX hf oc D hW hCF i as (fails_all cx K fsX hf oc D hRs hW hX hCR hCF as)
  | .prim p as => fail_prim cx K fsX hf oc D hW hX p as (fails_all cx K fsX hf oc D hRs hW hX hCR hCF as)
  | .loop z s => fun _ _ Γ ks F F' es env ew σ sp H f _ hc => by simp [OwnSpec.chk] at hc
  | .cont e => fun _ _ Γ ks F F' es env ew σ sp H f hT => by cases hT
theorem fails_all (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K) (hCR : CallR cx K oc D) (hCF : CallFail cx K fsX oc D) :
    ∀ cs : List ParSpec.Nd, ∀ n ∈ cs, NodeOK cx K oc D n ∧ NodeFail cx K fsX oc D n
  | [] => fun _ h => by simp at h
  | c :: cs => fun n hn => by
    rcases List.mem_cons.1 hn with h | h
    · rw [h]; exact ⟨node_all cx K oc D hRs hW hX hCR c, fail_all cx K fsX hf oc D hRs hW hX hCR hCF c⟩
    · exact fails_all cx K fsX hf oc D hRs hW hX hCR hCF cs n h
end

end NanoMain
