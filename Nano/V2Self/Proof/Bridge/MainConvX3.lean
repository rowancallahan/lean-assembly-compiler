/- Nano/V2Self/Proof/Bridge/MainConvX3: the cap half — prims (a full buffer's push reports `cap`) and calls. -/
import Nano.V2Self.Proof.Bridge.MainConvX2

namespace NanoMain
open Templates

/-- a prim whose arguments stop with `cap` stops with `cap` -/
theorem prim_args_exc {K : SC} {fsX : Nat → SemDX} {pn : Nat} {as : List ParSpec.Nd} {ew : Env} {H : Hp}
    (h13 : ¬ (pn = 1 ∨ pn = 3)) (h5 : pn ≠ 5) (h : ExC (svLF K fsX as ew) H) : ExC (svF K fsX (.prim pn as) ew) H := by
  simp only [svF, if_neg h13, if_neg h5]
  split
  · exact exc_bind_of h (fun sp => rfl)
  · split
    · exact exc_bind_of h (fun sp => rfl)
    · exact exc_bind_of h (fun sp => rfl)

/-- a push on a full buffer reports `cap` -/
theorem bpushFF_cap {hb κ : Nat} {H : Hp} {a : UInt64} {l : List UInt64} (h : BufAt hb κ H a l) (hl : κ ≤ l.length)
    (v : UInt64) (sp : Nat) : bpushFF hb a v sp H = .error .cap := by
  have hi := bufInfo_at h
  obtain ⟨-, -, -, -, h5, h6, -⟩ := h
  have k1 : (UInt64.ofNat κ).toNat = κ := toNat_ofNat_lt (by omega)
  have k2 : (UInt64.ofNat l.length).toNat = l.length := toNat_ofNat_lt (by omega)
  simp only [bpushFF, hi, k1, k2]
  rw [if_neg (by omega)]

theorem exc_prim (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (hX : CtxR cx K) (hFM : ∀ i args, Mo (K.fs i args)) (p : Nat) (as : List ParSpec.Nd)
    (hN : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeEx cx K oc D n ∧ NodeExC cx K fsX oc D n) : NodeExC cx K fsX oc D (.prim p as) := by
  intro hC hK2 Γ ks F F' es env ew σ H hT hc hE hA h8 hhb hr hev
  cases hT with
  | prim tl hpk hnil =>
    rename_i ps
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨⟨x1, x2⟩, hl, ⟨yF, yE⟩, hfn, -⟩ := hc
    obtain ⟨-, hk⟩ := evL_ok hC tl env hE.ty
    obtain ⟨-, hfc, hfb⟩ := fin_some hfn
    simp only [ev, bind, Except.bind] at hev
    cases el : evL cx as env with
    | error e =>
      rw [el] at hev; cases hev
      have LC := lst_exc cx K fsX hf oc D hC hK2 hW hFM as hN tl hl hE hA h8 hhb hr el
      rcases kinds_cases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals first
        | exact prim_args_exc (by decide) (by decide) LC
        | (have := hnil (by decide); subst this; simp [evL] at el)
    | ok va =>
      rcases kinds_cases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [el] at hev; exfalso
        have e : va = [] := by have := hk va el; simpa [kOf] using this
        subst e
        simp [prim, pure, Except.pure] at hev
      · rw [el] at hev; exfalso
        obtain ⟨x, rfl⟩ := kOf_w (hk va el)
        simp [prim, pure, Except.pure] at hev
      · rw [el] at hev; exfalso
        have e : va = [] := by have := hk va el; simpa [kOf] using this
        subst e
        simp [prim, pure, Except.pure] at hev
      · rw [el] at hev
        simp only [svF, show ¬ (4 = 1 ∨ 4 = 3) by decide, show (4 : Nat) ≠ 5 by decide, show ¬ (4 = 2 ∨ 4 = 6) by decide,
          show (4 : Nat) ≠ 8 by decide, if_false]
        have hNO : ∀ n ∈ as, NodeOK cx K oc D n := fun n h => (hN n h).1
        have hNE : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeEx cx K oc D n := fun n h => ⟨(hN n h).1, (hN n h).2.1⟩
        have LE := lst_ex cx K oc D hC hK2 hW hFM as hNE tl hl hE hA h8 hhb hr el
        have kv := hk va el
        refine exc_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) (exc_seq (T := fun r1 sp' H' => match r1.1 with
          | [a, b] => (primF2F K 4 a b (sp' - 16) H').map fun x => ([x.1], x.2) | _ => .error .stuck) 0 Prod.snd
          (svLF_ex K fsX hf LE) (svLF_mo' K fsX hf hFM as ew) fun sp r1 _ h1 => ?_)
        have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        rw [el] at evl'; cases evl'
        simp only [List.nil_append] at hesA; subst hesA
        have ln := hR1.len
        obtain ⟨l, x, rfl⟩ := kOf_bw kv
        obtain ⟨a, xw, hu⟩ := len2 (show r1.1.length = 2 by simp at ln; omega)
        obtain ⟨e0, e1, rfl⟩ := len2 (show x2.length = 2 by simp at ln; omega)
        obtain ⟨G, hG⟩ := hok 0 e0 rfl
        simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG
        simp at hG
        have hd : OwnSpec.dest (some (OwnSpec.dsP 4)) 0 = 1 := by simp [OwnSpec.dest, OwnSpec.dsP]
        obtain ⟨hσ, -, -⟩ := own0 hR1 hE1 hS1 hM1 hfc hd (e0 := e0) (l := l) (a := a) rfl rfl (by rw [hu]; rfl) hG
        have hge : K.κ ≤ l.length := by
          rcases Nat.lt_or_ge l.length cx.κ with h | h
          · exfalso; simp [prim, push, h, pure, Except.pure] at hev
          · rw [hX.κ]; exact h
        exact ⟨0, fun sp' _ _ => by
          simp (config := { decide := true }) only [hu, primF2F, if_false]
          rw [bpushFF_cap (bufAt_of hA1 hσ) hge]; rfl⟩
      · rw [el] at hev; exfalso
        have e : va = [] := by have := hk va el; simpa [kOf] using this
        subst e
        simp [prim, pure, Except.pure] at hev
      · rw [el] at hev; exfalso
        obtain ⟨l, rfl⟩ := kOf_b (hk va el)
        simp [prim, pure, Except.pure] at hev
      · rw [el] at hev; exfalso
        obtain ⟨l, x, rfl⟩ := kOf_bw (hk va el)
        simp [prim, pure, Except.pure] at hev
      · rw [el] at hev; exfalso
        obtain ⟨l, x, y, rfl⟩ := kOf_bww (hk va el)
        simp [prim, pure, Except.pure] at hev
      · rw [el] at hev
        simp only [svF, show ¬ (9 = 1 ∨ 9 = 3) by decide, show (9 : Nat) ≠ 5 by decide, show ¬ (9 = 2 ∨ 9 = 6) by decide,
          show (9 : Nat) ≠ 8 by decide, if_false]
        have hNO : ∀ n ∈ as, NodeOK cx K oc D n := fun n h => (hN n h).1
        have hNE : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeEx cx K oc D n := fun n h => ⟨(hN n h).1, (hN n h).2.1⟩
        have LE := lst_ex cx K oc D hC hK2 hW hFM as hNE tl hl hE hA h8 hhb hr el
        have kv := hk va el
        refine exc_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) (exc_seq (T := fun r1 sp' H' => match r1.1 with
          | [a, b] => (primF2F K 9 a b (sp' - 16) H').map fun x => ([x.1], x.2) | _ => .error .stuck) 0 Prod.snd
          (svLF_ex K fsX hf LE) (svLF_mo' K fsX hf hFM as ew) fun sp r1 _ h1 => ?_)
        have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
        obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
          lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
        rw [el] at evl'; cases evl'
        simp only [List.nil_append] at hesA; subst hesA
        have ln := hR1.len
        obtain ⟨l, x, rfl⟩ := kOf_bw kv
        obtain ⟨a, xw, hu⟩ := len2 (show r1.1.length = 2 by simp at ln; omega)
        obtain ⟨e0, e1, rfl⟩ := len2 (show x2.length = 2 by simp at ln; omega)
        obtain ⟨G, hG⟩ := hok 0 e0 rfl
        simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG
        simp at hG
        have hd : OwnSpec.dest (some (OwnSpec.dsP 9)) 0 = 1 := by simp [OwnSpec.dest, OwnSpec.dsP]
        obtain ⟨hσ, -, -⟩ := own0 hR1 hE1 hS1 hM1 hfc hd (e0 := e0) (l := l) (a := a) rfl rfl (by rw [hu]; rfl) hG
        have hge : K.κ ≤ l.length := by
          rcases Nat.lt_or_ge l.length cx.κ with h | h
          · exfalso; simp [prim, push, h, pure, Except.pure] at hev
          · rw [hX.κ]; exact h
        exact ⟨0, fun sp' _ _ => by
          simp (config := { decide := true }) only [hu, primF2F, if_false]
          rw [bpushFF_cap (bufAt_of hA1 hσ) hge]; rfl⟩

/-- a def's cap contract: on related arguments, if `Sem`'s meaning stops with `cap`, so does E's kinded def -/
def DefExC (hb κ : Nat) (Pk : List Kd) (P : List Nat) (f : List W → Except Stop (List W)) (g : SemDX) : Prop :=
  ∀ σ args ws H, AHeap hb κ H σ → H.top % 8 = 0 → hb ≤ H.top → kOf args = Pk → ArgsR σ P args ws →
    f args = .error .cap → ExC (g ws) H

def CallExC (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) : Prop :=
  ∀ (i : Nat) P R, oc.ps[i]? = some P → oc.rs[i]? = some R → ∃ f, cx.defs[i]? = some f ∧
    ∀ sg, D[i]? = some sg → DefExC K.hb K.κ sg.1 P f (fsX i)

theorem exc_call (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx)
    (D : List Sig) (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args)) (hCC : CallExC cx K fsX oc D) (i : Nat)
    (as : List ParSpec.Nd) (hN : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeEx cx K oc D n ∧ NodeExC cx K fsX oc D n) :
    NodeExC cx K fsX oc D (.call i as) := by
  intro hC hK2 Γ ks F F' es env ew σ H hT hc hE hA h8 hhb hr hev
  cases hT with
  | call tl hd =>
    simp only [OwnSpec.chk] at hc
    split at hc
    · rename_i P R hP hRr
      obtain ⟨⟨x1, x2⟩, hl, h⟩ := Option.bind_eq_some_iff.1 hc
      obtain ⟨⟨yF, yE⟩, hfn, -⟩ := Option.map_eq_some_iff.1 h
      simp only [ev, bind, Except.bind] at hev
      simp only [svF]
      cases el : evL cx as env with
      | error e =>
        rw [el] at hev; cases hev
        exact exc_bind_of (lst_exc cx K fsX hf oc D hC hK2 hW hFM as hN tl hl hE hA h8 hhb hr el) (fun sp => rfl)
      | ok va =>
      rw [el] at hev
      obtain ⟨f, hfd, hDC⟩ := hCC i P R hP hRr
      rw [hfd] at hev
      simp only at hev
      cases ef : f va with
      | ok res => rw [ef] at hev; cases hev
      | error e =>
      rw [ef] at hev; cases hev
      have hNO : ∀ n ∈ as, NodeOK cx K oc D n := fun n h => (hN n h).1
      have hNE : ∀ n ∈ as, NodeOK cx K oc D n ∧ NodeEx cx K oc D n := fun n h => ⟨(hN n h).1, (hN n h).2.1⟩
      have LE := lst_ex cx K oc D hC hK2 hW hFM as hNE tl hl hE hA h8 hhb hr el
      refine exc_of_eq (fun sp => rfl) (exc_seq (T := fun (r1 : List UInt64 × Hp) sp' H' => fsX i r1.1 sp' H')
        (8 * K.npwOf i) Prod.snd (svLF_ex K fsX hf LE) (svLF_mo' K fsX hf hFM as ew) fun sp r1 _ h1 => ?_)
      have h1' : svL K as ew sp H = some (r1.1, r1.2) := by rw [← svLF_eq K fsX hf, h1]; rfl
      obtain ⟨σ1, v', esN, hesA, evl', hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hNO tl hl hE hA h8 hhb hr h1'
      rw [el] at evl'; cases evl'
      simp only [List.nil_append] at hesA; subst hesA
      have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
      obtain ⟨hlP, hfc, hfb⟩ := fin_some hfn
      simp only at hlP hfc hfb
      obtain ⟨hArgs, -, -⟩ := fin_args hR1 hE1 hr1 hS1 hM1 hfc hfb hlP (fun i e he => by simpa using hok i e he)
      exact hDC _ hd σ1 va r1.1 r1.2 hA1 h81 hb1 ((evL_ok hC tl env hE.ty).2 va el) hArgs ef
    · cases hc

mutual
/-- **value mode, every node**: `ev` stopping with `cap` ⇒ E's kinded semantics reports `cap` given enough room -/
theorem exc_all (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K) (hCR : CallR cx K oc D) (hCE : CallEx cx K oc D)
    (hCC : CallExC cx K fsX oc D) (hFM : ∀ i args, Mo (K.fs i args)) (hκ : K.κ < 2 ^ 40) :
    ∀ e : ParSpec.Nd, NodeExC cx K fsX oc D e
  | .const c => exc_const cx K fsX oc D c
  | .loc s w => exc_loc cx K fsX oc D s w
  | .bin op a b => exc_bin cx K fsX hf oc D hW hFM op a b (node_all cx K oc D hRs hW hX hCR a)
      (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ a) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ a) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ b)
  | .ite c a b t e => exc_ite cx K fsX hf oc D hW hFM c a b t e (node_all cx K oc D hRs hW hX hCR a)
      (node_all cx K oc D hRs hW hX hCR b) (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ a)
      (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ b) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ a) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ b) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ t)
      (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ e)
  | .letE s w v b => exc_let cx K fsX hf oc D hW hFM s w v b (node_all cx K oc D hRs hW hX hCR v)
      (ex_all cx K oc D hRs hW hX hCR hCE hFM hκ v) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ v) (exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ b)
  | .pair cs => exc_pair cx K fsX hf oc D hW hFM cs (excs_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ cs)
  | .call i as => exc_call cx K fsX hf oc D hW hFM hCC i as (excs_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ as)
  | .prim p as => exc_prim cx K fsX hf oc D hW hX hFM p as (excs_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ as)
  | .loop z s => fun _ _ Γ ks F F' es env ew σ H _ hc => by simp [OwnSpec.chk] at hc
  | .cont e => fun _ _ Γ ks F F' es env ew σ H hT => by cases hT
theorem excs_all (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hRs : RsOK oc D) (hW : RsW oc) (hX : CtxR cx K) (hCR : CallR cx K oc D) (hCE : CallEx cx K oc D)
    (hCC : CallExC cx K fsX oc D) (hFM : ∀ i args, Mo (K.fs i args)) (hκ : K.κ < 2 ^ 40) :
    ∀ cs : List ParSpec.Nd, ∀ n ∈ cs, NodeOK cx K oc D n ∧ NodeEx cx K oc D n ∧ NodeExC cx K fsX oc D n
  | [] => fun _ h => by simp at h
  | c :: cs => fun n hn => by
    rcases List.mem_cons.1 hn with h | h
    · rw [h]; exact ⟨node_all cx K oc D hRs hW hX hCR c, ex_all cx K oc D hRs hW hX hCR hCE hFM hκ c, exc_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ c⟩
    · exact excs_all cx K fsX hf oc D hRs hW hX hCR hCE hCC hFM hκ cs n h
end

end NanoMain
