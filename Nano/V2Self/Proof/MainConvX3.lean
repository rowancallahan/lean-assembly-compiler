/- Nano/V2Self/Proof/MainConvX3: the cap half — prims (a full buffer's push reports `cap`) and calls. -/
import Nano.V2Self.Proof.MainConvX2

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

end NanoMain
