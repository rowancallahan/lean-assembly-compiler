/- Nano/V2Self/Proof/MainConv3: the converse bridge — existence for prims and calls. -/
import Nano.V2Self.Proof.MainConv2

namespace NanoMain
open Templates

theorem ex_some {α : Type} {S : Nat → Hp → Option α} {H : Hp} (h : ∀ sp, S sp H ≠ none) : Ex S H :=
  ⟨0, fun sp _ _ => Option.ne_none_iff_exists'.1 (h sp)⟩

theorem bnew_ex (κ : Nat) (hκ : κ < 2 ^ 40) (env : Env) (H : Hp) : Ex (one (bnewS κ) env) H :=
  ⟨8 * (κ + 2) + 8, fun sp a b => Option.ne_none_iff_exists'.1 (by
    simp [one, bnewS, show H.top + 8 * (κ + 2) + 8 ≤ sp by omega, b, hκ])⟩

theorem ex_prim (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (hX : CtxR cx K)
    (hFM : ∀ i args, Mo (K.fs i args)) (hκ : K.κ < 2 ^ 40) (p : Nat) (as : List ParSpec.Nd)
    (hN : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeEx cx K oc D n) : NodeEx cx K oc D (.prim p as) := by
  intro hC hK2 Γ ks F F' es env ew σ H v hT hc hE hA h8 hhb hr hev
  cases hT with
  | prim tl hpk hnil =>
    rename_i ps
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨⟨x1, x2⟩, hl, ⟨yF, yE⟩, hf, -⟩ := hc
    obtain ⟨-, hk⟩ := evL_ok hC tl env hE.ty
    obtain ⟨-, hfc, hfb⟩ := fin_some hf
    simp only [ev, bind, Except.bind] at hev
    cases el : evL cx as env with
    | error e => rw [el] at hev; cases hev
    | ok va =>
    rw [el] at hev
    have hNO : ∀ n ∈ as, NodeOK cx K oc D n := fun n h => (hN n h).1
    have LE := lst_ex cx K oc D hC hK2 hW hFM as hN tl hl hE hA h8 hhb hr el
    have kv := hk va el
    rcases kinds_cases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp (config := { decide := true }) only [sv, if_true, if_false]; exact leafS_ex _ _ H
    · simp (config := { decide := true }) only [sv, if_true, if_false]
      refine ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) (ex_seq (T := fun r1 sp' H' => match r1.1 with
        | [a] => (primF1 K 2 a (sp' - 8) H').map fun x => ([x.1], x.2) | _ => none) 0 Prod.snd LE (svL_mo K hFM as ew) fun sp r1 _ h1 => ?_)
      obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr (show svL K as ew sp H = some (r1.1, r1.2) from h1)
      rw [el] at evl'; cases evl'
      simp only [List.nil_append] at hesA; subst hesA
      have ln := hR1.len
      have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
      obtain ⟨x, rfl⟩ := kOf_w kv
      obtain ⟨u0, hu⟩ := List.length_eq_one_iff.1 (show r1.1.length = 1 by simp at ln; omega)
      exact ex_some fun sp' => by simp [hu, primF1, rdF1]
    · simp (config := { decide := true }) only [sv, if_true, if_false]; exact leafS_ex _ _ H
    · simp (config := { decide := true }) only [sv, if_true, if_false]
      refine ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) (ex_seq (T := fun r1 sp' H' => match r1.1 with
        | [a, b] => (primF2 K 4 a b (sp' - 16) H').map fun x => ([x.1], x.2) | _ => none) 0 Prod.snd LE (svL_mo K hFM as ew) fun sp r1 _ h1 => ?_)
      obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr (show svL K as ew sp H = some (r1.1, r1.2) from h1)
      rw [el] at evl'; cases evl'
      simp only [List.nil_append] at hesA; subst hesA
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
      have hlt : l.length < K.κ := by
        rcases Nat.lt_or_ge l.length cx.κ with h | h
        · rw [hX.κ]; exact h
        · exfalso; simp [prim, push, Nat.not_lt.2 h] at hev
      obtain ⟨H2, hp, -⟩ := bpush_at (bufAt_of hA1 hσ) hlt xw 0
      exact ex_some fun sp' => by
        simp (config := { decide := true }) only [hu, primF2, if_false]
        rw [show (bpushF K.hb a xw (sp' - 16) r1.2) = bpushF K.hb a xw 0 r1.2 from rfl, hp]; simp
    · simp (config := { decide := true }) only [sv, if_true, if_false]; exact bnew_ex _ hκ _ H
    · simp (config := { decide := true }) only [sv, if_true, if_false]
      refine ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) (ex_seq (T := fun r1 sp' H' => match r1.1 with
        | [a] => (primF1 K 6 a (sp' - 8) H').map fun x => ([x.1], x.2) | _ => none) 0 Prod.snd LE (svL_mo K hFM as ew) fun sp r1 _ h1 => ?_)
      obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr (show svL K as ew sp H = some (r1.1, r1.2) from h1)
      rw [el] at evl'; cases evl'
      simp only [List.nil_append] at hesA; subst hesA
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
      exact ex_some fun sp' => by simp (config := { decide := true }) [hu, primF1, bsize_at (bufAt_of hA1 hσ)]
    · simp (config := { decide := true }) only [sv, if_true, if_false]
      refine ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) (ex_seq (T := fun r1 sp' H' => match r1.1 with
        | [a, b] => (primF2 K 7 a b (sp' - 16) H').map fun x => ([x.1], x.2) | _ => none) 0 Prod.snd LE (svL_mo K hFM as ew) fun sp r1 _ h1 => ?_)
      obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr (show svL K as ew sp H = some (r1.1, r1.2) from h1)
      rw [el] at evl'; cases evl'
      simp only [List.nil_append] at hesA; subst hesA
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
      exact ex_some fun sp' => by simp (config := { decide := true }) [hu, primF2, bget_at (bufAt_of hA1 hσ)]
    · simp (config := { decide := true }) only [sv, if_true, if_false]
      refine ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) (ex_seq (T := fun r1 sp' H' => match r1.1 with
        | [a, b, c] => (bsetF K.hb a b c (sp' - 24) H').map fun x => ([x.1], x.2) | _ => none) 0 Prod.snd LE (svL_mo K hFM as ew) fun sp r1 _ h1 => ?_)
      obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr (show svL K as ew sp H = some (r1.1, r1.2) from h1)
      rw [el] at evl'; cases evl'
      simp only [List.nil_append] at hesA; subst hesA
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
      exact ex_some fun sp' => by
        simp only [hu]
        rw [show (bsetF K.hb a iw xw (sp' - 24) r1.2) = bsetF K.hb a iw xw 0 r1.2 from rfl, hp]; simp
    · simp (config := { decide := true }) only [sv, if_true, if_false]
      refine ex_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) (ex_seq (T := fun r1 sp' H' => match r1.1 with
        | [a, b] => (primF2 K 9 a b (sp' - 16) H').map fun x => ([x.1], x.2) | _ => none) 0 Prod.snd LE (svL_mo K hFM as ew) fun sp r1 _ h1 => ?_)
      obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr (show svL K as ew sp H = some (r1.1, r1.2) from h1)
      rw [el] at evl'; cases evl'
      simp only [List.nil_append] at hesA; subst hesA
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
      have hlt : l.length < K.κ := by
        rcases Nat.lt_or_ge l.length cx.κ with h | h
        · rw [hX.κ]; exact h
        · exfalso; simp [prim, push, Nat.not_lt.2 h] at hev
      obtain ⟨H2, hp, -⟩ := bpush_at (bufAt_of hA1 hσ) hlt xw 0
      exact ex_some fun sp' => by
        simp (config := { decide := true }) only [hu, primF2, if_false]
        rw [show (bpushF K.hb a xw (sp' - 16) r1.2) = bpushF K.hb a xw 0 r1.2 from rfl, hp]; simp


/-- a def's existence contract: on related arguments, if `Sem`'s meaning succeeds, E's def succeeds with enough room -/
def DefEx (hb κ : Nat) (Pk : List Kd) (P : List Nat) (f : List W → Except Stop (List W))
    (g : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)) : Prop :=
  ∀ σ args ws H res, AHeap hb κ H σ → H.top % 8 = 0 → hb ≤ H.top → kOf args = Pk → ArgsR σ P args ws →
    f args = .ok res → Ex (g ws) H

def CallEx (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) : Prop :=
  ∀ (i : Nat) P R, oc.ps[i]? = some P → oc.rs[i]? = some R → ∃ f, cx.defs[i]? = some f ∧
    ∀ sg, D[i]? = some sg → DefEx K.hb K.κ sg.1 P f (K.fs i)

theorem ex_call (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args))
    (hCE : CallEx cx K oc D) (i : Nat) (as : List ParSpec.Nd) (hN : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeEx cx K oc D n) :
    NodeEx cx K oc D (.call i as) := by
  intro hC hK2 Γ ks F F' es env ew σ H v hT hc hE hA h8 hhb hr hev
  cases hT with
  | call tl hd =>
    simp only [OwnSpec.chk] at hc
    split at hc
    · rename_i P R hP hRr
      obtain ⟨⟨x1, x2⟩, hl, h⟩ := Option.bind_eq_some_iff.1 hc
      obtain ⟨⟨yF, yE⟩, hf, -⟩ := Option.map_eq_some_iff.1 h
      simp only [ev, bind, Except.bind] at hev
      cases el : evL cx as env with
      | error e => rw [el] at hev; cases hev
      | ok va =>
      rw [el] at hev
      obtain ⟨f, hfd, hDE⟩ := hCE i P R hP hRr
      rw [hfd] at hev
      simp only at hev
      cases ef : f va with
      | error e => rw [ef] at hev; cases hev
      | ok res =>
      have hNO : ∀ n ∈ as, NodeOK cx K oc D n := fun n h => (hN n h).1
      have LE := lst_ex cx K oc D hC hK2 hW hFM as hN tl hl hE hA h8 hhb hr el
      simp only [sv]
      refine ex_of_eq (fun sp => rfl) (ex_seq (T := fun (r1 : List UInt64 × Hp) sp' H' => K.fs i r1.1 sp' H') (8 * K.npwOf i) Prod.snd LE
        (svL_mo K hFM as ew) fun sp r1 _ h1 => ?_)
      obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr (show svL K as ew sp H = some (r1.1, r1.2) from h1)
      rw [el] at evl'; cases evl'
      simp only [List.nil_append] at hesA; subst hesA
      have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
      obtain ⟨hlP, hfc, hfb⟩ := fin_some hf
      simp only at hlP hfc hfb
      obtain ⟨hArgs, -, -⟩ := fin_args hR1 hE1 hr1 hS1 hM1 hfc hfb hlP (fun i e he => by simpa using hok i e he)
      exact hDE _ hd σ1 va r1.1 r1.2 res hA1 h81 hb1 ((evL_ok hC tl env hE.ty).2 va el) hArgs ef
    · cases hc


mutual
/-- **value mode, every node**: `ev` succeeding ⇒ E's `sv` succeeds given enough room -/
theorem ex_all (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K)
    (hCR : CallR cx K oc D) (hCE : CallEx cx K oc D) (hFM : ∀ i args, Mo (K.fs i args)) (hκ : K.κ < 2 ^ 40) :
    ∀ e : ParSpec.Nd, NodeEx cx K oc D e
  | .const c => ex_nconst cx K oc D c
  | .loc s w => ex_loc cx K oc D s w
  | .bin op a b => ex_bin cx K oc D hW hFM op a b (node_all cx K oc D hRs hW hX hCR a) (node_all cx K oc D hRs hW hX hCR b)
      (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ a) (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ b)
  | .ite c a b t e => ex_ite cx K oc D hW hFM c a b t e (node_all cx K oc D hRs hW hX hCR a)
      (node_all cx K oc D hRs hW hX hCR b) (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ a)
      (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ b) (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ t)
      (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ e)
  | .letE s w v b => ex_let cx K oc D hW hFM s w v b (node_all cx K oc D hRs hW hX hCR v)
      (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ v) (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ b)
  | .pair cs => ex_pair cx K oc D hW hFM cs (exs_all cx K oc D hRs hW hX hCR hCE hFM hκ cs)
  | .call i as => ex_call cx K oc D hW hFM hCE i as (exs_all cx K oc D hRs hW hX hCR hCE hFM hκ as)
  | .prim p as => ex_prim cx K oc D hW hX hFM hκ p as (exs_all cx K oc D hRs hW hX hCR hCE hFM hκ as)
  | .loop z s => fun _ _ Γ ks F F' es env ew σ H v _ hc => by simp [OwnSpec.chk] at hc
  | .cont e => fun _ _ Γ ks F F' es env ew σ H v hT => by cases hT
theorem exs_all (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K)
    (hCR : CallR cx K oc D) (hCE : CallEx cx K oc D) (hFM : ∀ i args, Mo (K.fs i args)) (hκ : K.κ < 2 ^ 40) :
    ∀ cs : List ParSpec.Nd, ∀ n ∈ cs, NodeOK cx K oc D n ∧ NodeEx cx K oc D n
  | [] => fun _ h => by simp at h
  | c :: cs => fun n hn => by
    rcases List.mem_cons.1 hn with h | h
    · rw [h]; exact ⟨node_all cx K oc D hRs hW hX hCR c, ex_all cx K oc D hRs hW hX hCR hCE hFM hκ c⟩
    · exact exs_all cx K oc D hRs hW hX hCR hCE hFM hκ cs n h
end

end NanoMain
