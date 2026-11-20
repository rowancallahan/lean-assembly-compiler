/- The decoder `dec` and the encoder `enc` of `indProg` (`Compiler/Ind.lean`), once and for all. -/
import Compiler.IndStrOk

set_option linter.unusedVariables false
namespace Proven.Mach.Ind
open Proven.Mach

/-! ## the decoder -/

variable (P : Prog) (sh : Shape)

/-- a call of `dec` on the bytes of `v` runs within `K` bytes of stack -/
def DecOK (K : Nat) (v : C) : Prop :=
  ∀ (g : BEnv) (H : Heap) (I : List (BitVec 8)) (c : Nat) (W : List (BitVec 64)) (h : Nat),
    H[0]? = some I → I.length < 2 ^ 60 → At I c (v.enc sh) → HI W h → g 4 = BitVec.ofNat 64 c →
    g 5 = BitVec.ofNat 64 h → h + 4 * (v.enc sh).length ≤ W.length →
    ∃ E' W' h', CExec P K (decFn sh).body ⟨callEnv g [], H, [W]⟩ ⟨E', H, [W']⟩ ∧
      W'.length = W.length ∧ Agree W W' h ∧ HI W' h' ∧ h ≤ h' ∧ h' ≤ h + 4 * (v.enc sh).length ∧
      E' 5 = BitVec.ofNat 64 h' ∧ E' 4 = BitVec.ofNat 64 (c + (v.enc sh).length) ∧
      (∀ i, i < 8 → i ≠ 4 → i ≠ 5 → E' i = g i) ∧ Rp W' h' ((decFn sh).ret.denote E') v

variable {P sh}

theorem dcall_ok (hP1 : ∃ hf : 1 < P.length, P[1] = decFn sh) {K K' : Nat} (hK : 64 + K' ≤ K) {v : C}
    (ok : DecOK P sh K' v) {d : Nat} (hd : 8 ≤ d) {env : BEnv} {H : Heap} {I : List (BitVec 8)} {c : Nat}
    {W : List (BitVec 64)} {h : Nat} (hH : H[0]? = some I) (hI : I.length < 2 ^ 60) (hA : At I c (v.enc sh))
    (hi : HI W h) (h4 : env 4 = BitVec.ofNat 64 c) (h5 : env 5 = BitVec.ofNat 64 h)
    (cap : h + 4 * (v.enc sh).length ≤ W.length) :
    ∃ E' W' h', CExec P K (.call d 1 []) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
      W'.length = W.length ∧ Agree W W' h ∧ HI W' h' ∧ h ≤ h' ∧ h' ≤ h + 4 * (v.enc sh).length ∧
      E' 5 = BitVec.ofNat 64 h' ∧ E' 4 = BitVec.ofNat 64 (c + (v.enc sh).length) ∧
      (∀ i, i ≠ 4 → i ≠ 5 → i ≠ d → E' i = env i) ∧ Rp W' h' (E' d) v := by
  obtain ⟨hf, hP⟩ := hP1
  obtain ⟨E'', W', h', hx, l1, a1, i1, b1, b2, e5, e4, gl, rv⟩ := ok env H I c W h hH hI hA hi h4 h5 cap
  have hc := call_body (P := P) (f := 1) (K := K) (K' := K') hf (by rw [hP]; exact hK) (d := d)
    (args := []) (by rw [hP]; rfl) (σ := ⟨env, H, [W]⟩) (σ₁ := ⟨E'', H, [W']⟩) (by rw [hP]; exact hx)
  rw [hP] at hc
  refine ⟨_, W', h', hc, l1, a1, i1, b1, b2, ?_, ?_, fun i n4 n5 nd => ?_, ?_⟩
  · simp only; rw [set_ne' _ _ (by omega)]; simp only [retEnv, if_pos (show 5 < 8 by omega)]; exact e5
  · simp only; rw [set_ne' _ _ (by omega)]; simp only [retEnv, if_pos (show 4 < 8 by omega)]; exact e4
  · simp only; rw [set_ne' _ _ nd]; simp only [retEnv]; split
    · exact gl i (by omega) n4 n5
    · rfl
  · simp only; rw [set_eq']; exact rv

theorem dFlds_ok (hP1 : ∃ hf : 1 < P.length, P[1] = decFn sh) {K K' : Nat} (hK : 64 + K' ≤ K)
    (hst : sTag sh + 1 < 256) {x : BitVec 64} {l r : C} (okl : l.wf sh → DecOK P sh K' l)
    (okr : r.wf sh → DecOK P sh K' r) :
    ∀ (fs : List Fld) (env : BEnv) (H : Heap) (I : List (BitVec 8)) (q : Nat) (W : List (BitVec 64)) (h : Nat),
      H[0]? = some I → I.length < 2 ^ 60 → At I q (fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc)) → HI W h →
      env 4 = BitVec.ofNat 64 q → env 5 = BitVec.ofNat 64 h →
      h + 4 * (fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc)).length ≤ W.length →
      (Fld.l ∈ fs → l.wf sh) → (Fld.r ∈ fs → r.wf sh) → (Fld.sl ∈ fs → l.IsStr (sTag sh)) →
      (Fld.sr ∈ fs → r.IsStr (sTag sh)) → (Fld.b ∈ fs → x.toNat < 256) →
      (Fld.x ∈ fs ∨ Fld.b ∈ fs ∨ env 9 = x) → (Fld.l ∈ fs ∨ Fld.sl ∈ fs ∨ Rp W h (env 10) l) →
      (Fld.r ∈ fs ∨ Fld.sr ∈ fs ∨ Rp W h (env 11) r) →
      ∃ E' W' h', CExec P K (dFlds (sTag sh) fs) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
        W'.length = W.length ∧ Agree W W' h ∧ HI W' h' ∧ h ≤ h' ∧
        h' ≤ h + 4 * (fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc)).length ∧
        E' 5 = BitVec.ofNat 64 h' ∧
        E' 4 = BitVec.ofNat 64 (q + (fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc)).length) ∧
        (∀ i, i ∉ [4, 5, 9, 10, 11, 12, 13, 14] → E' i = env i) ∧ E' 9 = x ∧ Rp W' h' (E' 10) l ∧ Rp W' h' (E' 11) r
  | [], env, H, I, q, W, h, hH, hI, hA, hi, h4, h5, cap, wl, wr, wsl, wsr, wb, ix, il, ir => by
    simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero, Nat.add_zero, List.not_mem_nil, false_or] at *
    refine ⟨_, W, h, .base (asg_exec _ _ _), rfl, Agree.refl _ _, hi, Nat.le_refl _, Nat.le_refl _, ?_, ?_,
      fun i hi' => ?_, ?_, ?_, ?_⟩ <;> simp only [vE, BExp.denote]
    · rw [set_ne' _ _ (by omega)]; exact h5
    · rw [set_ne' _ _ (by omega)]; exact h4
    · rw [set_ne' _ _ (by simp at hi'; omega)]
    · rw [set_eq']; exact ix
    · rw [set_ne' _ _ (by omega)]; exact il
    · rw [set_ne' _ _ (by omega)]; exact ir
  | f :: fs, env, H, I, q, W, h, hH, hI, hA, hi, h4, h5, cap, wl, wr, wsl, wsr, wb, ix, il, ir => by
    simp only [List.flatMap_cons] at hA cap ⊢
    obtain ⟨hA1, hA2⟩ := hA.app
    -- one field, then the rest
    have step : ∃ E₁ W₁ h₁, CExec P K (dFld (sTag sh) f) ⟨env, H, [W]⟩ ⟨E₁, H, [W₁]⟩ ∧ W₁.length = W.length ∧
        Agree W W₁ h ∧ HI W₁ h₁ ∧ h ≤ h₁ ∧ h₁ ≤ h + 4 * (encF x (l.enc sh) (r.enc sh) l.senc r.senc f).length ∧
        E₁ 5 = BitVec.ofNat 64 h₁ ∧ E₁ 4 = BitVec.ofNat 64 (q + (encF x (l.enc sh) (r.enc sh) l.senc r.senc f).length) ∧
        (∀ i, i ∉ [4, 5, 9, 10, 11, 12, 13, 14] → E₁ i = env i) ∧
        (Fld.x ∈ fs ∨ Fld.b ∈ fs ∨ E₁ 9 = x) ∧ (Fld.l ∈ fs ∨ Fld.sl ∈ fs ∨ Rp W₁ h₁ (E₁ 10) l) ∧
          (Fld.r ∈ fs ∨ Fld.sr ∈ fs ∨ Rp W₁ h₁ (E₁ 11) r) := by
      cases f with
      | x =>
        have hL : (leN 8 x.toNat).length = 8 := leN_length 8 _
        have hq := hA1.lt (by simp [encF, hL])
        simp only [encF, hL] at hA1 hq ⊢
        obtain ⟨E₁, x₁, v₁, k₁⟩ := rdB_ok (leN 8 x.toNat) hL q I hA1 (by omega) 8 (by omega) env H [W] hH h4
        refine ⟨_, W, h, .base (.seq x₁ (asg_exec _ _ _)), rfl, Agree.refl _ _, hi, Nat.le_refl _, by omega, ?_, ?_,
          fun i hi' => ?_, ?_, ?_, ?_⟩
        · dsimp only; rw [set_ne' _ _ (by omega), k₁ 5 (by omega) (by omega)]; exact h5
        · dsimp only; rw [set_eq']; simp only [addE, kE, BExp.denote, Op.eval]; rw [k₁ 4 (by omega) (by omega), h4, BitVec.ofNat_add]
        · simp at hi'; dsimp only; rw [set_ne' _ _ (by omega), k₁ i (by omega) (by omega)]
        · right; right; dsimp only; rw [set_ne' _ _ (by omega), v₁]; simp only [Nat.sub_self, List.drop_zero, unle_leN]
          apply BitVec.eq_of_toNat_eq; simp; omega
        · rcases il with il | il | il
          · left; simpa using il
          · right; left; simpa using il
          · right; right; dsimp only; rw [set_ne' _ _ (by omega), k₁ 10 (by omega) (by omega)]; exact il
        · rcases ir with ir | ir | ir
          · left; simpa using ir
          · right; left; simpa using ir
          · right; right; dsimp only; rw [set_ne' _ _ (by omega), k₁ 11 (by omega) (by omega)]; exact ir
      | b =>
        have hx := wb (List.mem_cons_self ..)
        have hL : ((leN 8 x.toNat).take 1) = [UInt8.ofNat x.toNat] := by simp [leN, Nat.mod_eq_of_lt hx]
        simp only [encF, hL] at hA1 cap ⊢
        have hb := hA1.get 0 (by simp)
        simp only [Nat.add_zero, List.getElem_cons_zero] at hb
        have hix : ((vE 4).denote env).toNat = q := by
          simp only [vE, BExp.denote, h4]; exact toNat_h (by have := hA1.lt (by simp); omega)
        refine ⟨_, W, h, .base (.seq (load_exec hH hix hb) (asg_exec _ _ _)), rfl, Agree.refl _ _, hi, Nat.le_refl _,
          by simp, ?_, ?_, fun i hi' => ?_, ?_, ?_, ?_⟩
        · dsimp only; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; exact h5
        · dsimp only; rw [set_eq']; simp only [addE, kE, BExp.denote, Op.eval, List.length_singleton]
          rw [set_ne' _ _ (by omega), h4, BitVec.ofNat_add]
        · simp at hi'; dsimp only; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]
        · right; right; dsimp only; rw [set_ne' _ _ (by omega), set_eq', zb]
          apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt hx]
        · rcases il with il | il | il
          · left; simpa using il
          · right; left; simpa using il
          · right; right; dsimp only; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; exact il
        · rcases ir with ir | ir | ir
          · left; simpa using ir
          · right; left; simpa using ir
          · right; right; dsimp only; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; exact ir
      | l =>
        simp only [encF, List.length_append] at hA1 cap ⊢
        obtain ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, gl, rv⟩ := dcall_ok hP1 hK (okl (wl (by simp)))
          (d := 10) (by omega) hH hI hA1 hi h4 h5 (by omega)
        refine ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, fun i hi' => gl i (by simp at hi'; omega)
          (by simp at hi'; omega) (by simp at hi'; omega), ?_, .inr (.inr rv), ?_⟩
        · rcases ix with ix | ix | ix
          · left; simpa using ix
          · right; left; simpa using ix
          · right; right; rw [gl 9 (by omega) (by omega) (by omega)]; exact ix
        · rcases ir with ir | ir | ir
          · left; simpa using ir
          · right; left; simpa using ir
          · right; right; rw [gl 11 (by omega) (by omega) (by omega)]; exact ir.mono b1 a1
      | r =>
        simp only [encF, List.length_append] at hA1 cap ⊢
        obtain ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, gl, rv⟩ := dcall_ok hP1 hK (okr (wr (by simp)))
          (d := 11) (by omega) hH hI hA1 hi h4 h5 (by omega)
        refine ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, fun i hi' => gl i (by simp at hi'; omega)
          (by simp at hi'; omega) (by simp at hi'; omega), ?_, ?_, .inr (.inr rv)⟩
        · rcases ix with ix | ix | ix
          · left; simpa using ix
          · right; left; simpa using ix
          · right; right; rw [gl 9 (by omega) (by omega) (by omega)]; exact ix
        · rcases il with il | il | il
          · left; simpa using il
          · right; left; simpa using il
          · right; right; rw [gl 10 (by omega) (by omega) (by omega)]; exact il.mono b1 a1
      | sl =>
        obtain ⟨L, hlL, hse⟩ := IsStr.senc (wsl (by simp))
        simp only [encF, hse] at hA1 cap ⊢
        obtain ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, gl, rv⟩ := dStr_ok (P := P) (K := K) (sTag sh) 10
          (.inl rfl) hst L hH hI hA1 hi h4 h5 (by simp only [List.length_append] at cap ⊢; omega)
        refine ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, fun i hi' => gl i (by simp at hi' ⊢; omega), ?_,
          .inr (.inr (by rw [hlL]; exact rv)), ?_⟩
        · rcases ix with ix | ix | ix
          · left; simpa using ix
          · right; left; simpa using ix
          · right; right; rw [gl 9 (by simp)]; exact ix
        · rcases ir with ir | ir | ir
          · left; simpa using ir
          · right; left; simpa using ir
          · right; right; rw [gl 11 (by simp)]; exact ir.mono b1 a1
      | sr =>
        obtain ⟨L, hrL, hse⟩ := IsStr.senc (wsr (by simp))
        simp only [encF, hse] at hA1 cap ⊢
        obtain ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, gl, rv⟩ := dStr_ok (P := P) (K := K) (sTag sh) 11
          (.inr rfl) hst L hH hI hA1 hi h4 h5 (by simp only [List.length_append] at cap ⊢; omega)
        refine ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, fun i hi' => gl i (by simp at hi' ⊢; omega), ?_,
          ?_, .inr (.inr (by rw [hrL]; exact rv))⟩
        · rcases ix with ix | ix | ix
          · left; simpa using ix
          · right; left; simpa using ix
          · right; right; rw [gl 9 (by simp)]; exact ix
        · rcases il with il | il | il
          · left; simpa using il
          · right; left; simpa using il
          · right; right; rw [gl 10 (by simp)]; exact il.mono b1 a1
    obtain ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, gl, ix1, il1, ir1⟩ := step
    obtain ⟨E₂, W₂, h₂, x₂, l2, a2, i2, c1, c2, f5, f4, gl2, ix2, il2, ir2⟩ := dFlds_ok hP1 hK hst okl okr fs E₁ H I _ W₁ h₁
      hH hI hA2 i1 e4 e5 (by rw [l1]; simp only [List.length_append] at cap; omega)
      (fun m => wl (List.mem_cons_of_mem _ m)) (fun m => wr (List.mem_cons_of_mem _ m))
      (fun m => wsl (List.mem_cons_of_mem _ m)) (fun m => wsr (List.mem_cons_of_mem _ m))
      (fun m => wb (List.mem_cons_of_mem _ m)) ix1 il1 ir1
    refine ⟨E₂, W₂, h₂, .seq x₁ x₂, l2.trans l1, a1.trans a2 b1, i2, by omega, by simp only [List.length_append]; omega,
      f5, by rw [f4, List.length_append, Nat.add_assoc], fun i hi' => by rw [gl2 i hi', gl i hi'], ix2, il2, ir2⟩

theorem decOK_mono {K K' : Nat} {v : C} (h : DecOK P sh K v) (hk : K ≤ K') : DecOK P sh K' v := by
  intro g H I c W hh a1 a2 a3 a4 a5 a6 a7
  obtain ⟨E', W', h', hx, rest⟩ := h g H I c W hh a1 a2 a3 a4 a5 a6 a7
  exact ⟨E', W', h', hx.mono hk, rest⟩

theorem dDisp_skip {K : Nat} {t : Nat} (st : Nat) (ht : t < 256) :
    ∀ (ss : Shape) (i : Nat), t < i → i + ss.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 8 = BitVec.ofNat 64 t → CExec P K (dDisp st ss i) ⟨env, H, Wh⟩ ⟨env, H, Wh⟩
  | [], i, _, _, env, H, Wh, _ => by
    have := CExec.base (P := P) (k := K) (asg_exec 9 (vE 9) ⟨env, H, Wh⟩)
    simp [vE, BExp.denote, set_same] at this; exact this
  | fs :: ss, i, hi, hl, env, H, Wh, he => by
    simp only [List.length_cons] at hl
    have hn := CExec.base (P := P) (k := K) (asg_exec 9 (vE 9) ⟨env, H, Wh⟩)
    simp only [vE, BExp.denote, set_same] at hn
    exact .seq (.iteF (by show BExp.denote env (eqE 8 i) = 0; rw [eqE_den env 8 i t he ht (by omega), if_neg (by omega)]) hn)
      (dDisp_skip st ht ss (i + 1) (by omega) (by omega) env H Wh he)

theorem dDisp_ok {K : Nat} {t : Nat} (st : Nat) (ht : t < 256) {Q : BState → Prop} :
    ∀ (ss : Shape) (i : Nat), i ≤ t → i + ss.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 8 = BitVec.ofNat 64 t →
      (∀ fs, ss[t - i]? = some fs → ∃ σ', CExec P K (dFlds st fs) ⟨env, H, Wh⟩ σ' ∧ Q σ' ∧ σ'.env 8 = env 8) →
      (ss[t - i]? = none → Q ⟨env.set 9 (env 9), H, Wh⟩) →
      ∃ σ', CExec P K (dDisp st ss i) ⟨env, H, Wh⟩ σ' ∧ Q σ'
  | [], i, _, _, env, H, Wh, _, _, hn => ⟨_, .base (asg_exec _ _ _), hn rfl⟩
  | fs :: ss, i, hi, hl, env, H, Wh, he, hs, hn => by
    simp only [List.length_cons] at hl
    by_cases h : t = i
    · subst h
      obtain ⟨⟨E', H', Wh'⟩, hx, hq, h8⟩ := hs fs (by simp)
      exact ⟨_, .seq (.iteT (by rw [eqE_den env 8 t t he ht ht, if_pos rfl]; decide) hx)
        (dDisp_skip st ht ss (t + 1) (by omega) (by omega) E' H' Wh' (by simp only at h8; rw [h8, he])), hq⟩
    · have hnop := CExec.base (P := P) (k := K) (asg_exec 9 (vE 9) ⟨env, H, Wh⟩)
      simp only [vE, BExp.denote, set_same] at hnop
      obtain ⟨σ', hx, hq⟩ := dDisp_ok st ht ss (i + 1) (by omega) (by omega) env H Wh he
        (fun e' h' => hs e' (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
        (fun h' => hn (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
      exact ⟨σ', .seq (.iteF (by show BExp.denote env (eqE 8 i) = 0; rw [eqE_den env 8 i t he ht (by omega), if_neg h]) hnop) hx, hq⟩

theorem tag_byte {t : Nat} (ht : t < 256) : (UInt8.ofNat t).toBitVec.setWidth 64 = BitVec.ofNat 64 t := by
  rw [zb]; congr 1; simp [UInt8.toNat_ofNat]; omega

/-- **The decoder**: `dec` on the bytes of a well-formed `v` builds its cells -/
theorem dec_ok (hP1 : ∃ hf : 1 < P.length, P[1] = decFn sh) (hsh : sh.length < 255) :
    ∀ v, v.wf sh → DecOK P sh (64 * v.depth) v := by
  intro v
  induction v with
  | z => intro h; exact absurd h id
  | c t x l r ihl ihr =>
    intro hw g H I c W h hH hI hA hi h4 h5 cap
    obtain ⟨ht, hx0, hlw, hrw⟩ := hw
    simp only [C.enc] at hA cap
    obtain ⟨hb0, hA1⟩ := hA.cons
    have hcl := hA.lt (by simp)
    simp only [List.length_cons] at cap hcl
    have hfs : sh[t]? = some (sh.getD t []) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    have hlen : (C.enc sh (.c t x l r)).length =
        (List.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc) (sh.getD t [])).length + 1 := by
      simp [C.enc]
    generalize sh.getD t [] = fs at hx0 hlw hrw hA1 cap hcl hfs hlen
    let g1 := callEnv g []
    have hg1 : ∀ i, i < 8 → g1 i = g i := fun i hi' => by simp [g1, callEnv, hi']
    let e1 := ((((g1.set 8 ((UInt8.ofNat t).toBitVec.setWidth 64)).set 4 ((addE 4 1).denote
      (g1.set 8 ((UInt8.ofNat t).toBitVec.setWidth 64)))).set 9 0).set 10 0).set 11 0
    have i1 : BExec (.seq (.load 8 0 (vE 4)) (.seq (asg 4 (addE 4 1))
        (.seq (asg 9 (kE 0)) (.seq (asg 10 (kE 0)) (asg 11 (kE 0)))))) ⟨g1, H, [W]⟩ ⟨e1, H, [W]⟩ :=
      .seq (load_exec hH (by simp [vE, BExp.denote, hg1 4 (by omega), h4]; omega) hb0)
        (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) (asg_exec _ _ _))))
    have e1k : ∀ i, i < 8 → i ≠ 4 → e1 i = g i := fun i hi' h4' => by
      simp only [e1]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ h4',
        set_ne' _ _ (by omega), hg1 i hi']
    have e18 : e1 8 = BitVec.ofNat 64 t := by
      simp only [e1]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega),
        set_eq', tag_byte (by omega)]
    have e14 : e1 4 = BitVec.ofNat 64 (c + 1) := by
      simp only [e1]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_eq']
      exact addE_den' (by rw [set_ne' _ _ (by omega), hg1 4 (by omega)]; exact h4)
    have K1 : 64 * (C.c t x l r).depth = 64 + 64 * max l.depth r.depth := by simp only [C.depth]; omega
    obtain ⟨E₂, W₂, h₂, x₂, l2, a2, i2, b1, b2, f5, f4, gl2, ix2, il2, ir2⟩ := dFlds_ok hP1 (K := 64 * (C.c t x l r).depth)
      (K' := 64 * max l.depth r.depth) (by omega) (by unfold sTag; omega) (x := x) (l := l) (r := r)
      (fun w => decOK_mono (ihl w) (by omega)) (fun w => decOK_mono (ihr w) (by omega)) fs e1 H I (c + 1) W h hH hI hA1 hi
      e14 (by rw [e1k 5 (by omega) (by omega)]; exact h5) (by omega)
      hlw.1 hrw.1 hlw.2.1 hrw.2.1 (fun m => hx0.2 m)
      (by by_cases m : Fld.x ∈ fs
          · exact .inl m
          · by_cases mb : Fld.b ∈ fs
            · exact .inr (.inl mb)
            · right; right; simp [e1, set_eq', set_ne']; exact (hx0.1 m mb).symm)
      (by by_cases m : Fld.l ∈ fs
          · exact .inl m
          · by_cases ms : Fld.sl ∈ fs
            · exact .inr (.inl ms)
            · right; right; have : l = .z := hlw.2.2 m ms
              subst this; simp only [e1]; rw [set_ne' _ _ (by omega), set_eq']; exact .z)
      (by by_cases m : Fld.r ∈ fs
          · exact .inl m
          · by_cases ms : Fld.sr ∈ fs
            · exact .inr (.inl ms)
            · right; right; have : r = .z := hrw.2.2 m ms
              subst this; simp only [e1]; rw [set_eq']; exact .z)
    have hb4 : h₂ + 4 ≤ W₂.length := by rw [l2]; omega
    have hx := alloc_exec (H := H) (env := E₂) (vE 8) 9 10 11 12 (by omega) f5 hb4 i2.big
    obtain ⟨σd, xd, hq⟩ := dDisp_ok (P := P) (K := 64 * (C.c t x l r).depth) (sTag sh) (Q := fun σ => σ = ⟨E₂, H, [W₂]⟩)
      (show t < 256 by omega) sh 0 (Nat.zero_le _) (by omega) e1 H [W] e18
      (fun fs' h' => by rw [Nat.sub_zero, hfs] at h'; cases h'; exact ⟨_, x₂, rfl, gl2 8 (by simp)⟩)
      (fun h' => by rw [Nat.sub_zero, hfs] at h'; cases h')
    subst hq
    have e28 : E₂ 8 = BitVec.ofNat 64 t := by rw [gl2 8 (by simp), e18]
    refine ⟨_, _, h₂ + 4, .seq (.base i1) (.seq xd (.base hx)), by rw [put_length, l2],
      a2.trans (put_agree W₂ _ _ _ _ _) b1, HI_put i2 hb4 _ _ _ _, by omega, by omega, by rw [set_eq'],
      ?_, fun i hi' n4 n5 => ?_, ?_⟩
    · rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), f4]; congr 1; omega
    · rw [set_ne' _ _ n5, set_ne' _ _ (by omega), gl2 i (by simp; omega), e1k i hi' n4]
    · show Rp _ _ (BEnv.set _ _ _ 12) _
      rw [set_ne' _ _ (by omega), set_eq']
      simp only [vE, BExp.denote, e28]
      rw [ix2]; exact Rp_put (t := t) i2 (by omega) hb4 il2 ir2

/-! ## the encoder -/

theorem loads_execE {W : List (BitVec 64)} {h : Nat} {pv : BitVec 64} {v : C} (hi : HI W h) (rv : Rp W h pv v)
    {env : BEnv} {H : Heap} (hp : env 8 = pv) :
    ∃ pl pr, Rp W h pl v.lv ∧ Rp W h pr v.rv ∧ v.tag < 256 ∧
      BExec (loads 8 9 10 11 12) ⟨env, H, [W]⟩
        ⟨(((env.set 9 (BitVec.ofNat 64 v.tag)).set 10 v.xv).set 11 pl).set 12 pr, H, [W]⟩ := by
  obtain ⟨ht, e0, e1, ⟨pl, e2, rl⟩, ⟨pr, e3, rr⟩⟩ := rv.read hi.z0
  have hlt : pv.toNat < 2 ^ 60 := by
    rcases rv.lt with h1 | h1
    · have := hi.hle; have := hi.big; omega
    · subst h1; simp
  have d : ∀ (E : BEnv) (c : Nat), c < 4 → E 8 = pv → ((addE 8 c).denote E).toNat = pv.toNat + c := fun E c hc he => by
    simp only [addE, kE, BExp.denote, Op.eval, he, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨pl, pr, rl, rr, ht, .seq (load64_exec (by simp [vE, BExp.denote, hp]) e0)
    (.seq (load64_exec (d _ 1 (by omega) (by rw [set_ne' _ _ (by omega)]; exact hp)) e1)
    (.seq (load64_exec (d _ 2 (by omega) (by rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; exact hp)) e2)
    (load64_exec (d _ 3 (by omega) (by rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; exact hp)) e3)))⟩


variable (P sh) in
/-- a call of `enc` on `v` (at `pv`) runs within `K` bytes of stack -/
def EncOK (K : Nat) (v : C) : Prop :=
  ∀ (g : BEnv) (I O : List (BitVec 8)) (pv : BitVec 64) (W : List (BitVec 64)) (h j : Nat),
    O.length < 2 ^ 60 → HI W h → Rp W h pv v → g 6 = BitVec.ofNat 64 j → j + (v.enc sh).length ≤ O.length →
    ∃ E', CExec P K (encFn sh).body ⟨callEnv g [pv], [I, O], [W]⟩ ⟨E', [I, wr O j (v.enc sh)], [W]⟩ ∧
      E' 6 = BitVec.ofNat 64 (j + (v.enc sh).length) ∧ ∀ i, i < 8 → i ≠ 6 → E' i = g i

theorem encOK_mono {K K' : Nat} {v : C} (h : EncOK P sh K v) (hk : K ≤ K') : EncOK P sh K' v := by
  intro g I O pv W hh j a1 a2 a3 a4 a5
  obtain ⟨E', hx, rest⟩ := h g I O pv W hh j a1 a2 a3 a4 a5
  exact ⟨E', hx.mono hk, rest⟩

theorem ecall_ok (hP2 : ∃ hf : 2 < P.length, P[2] = encFn sh) {K K' : Nat} (hK : 72 + K' ≤ K) {v : C}
    (ok : EncOK P sh K' v) {pvar : Nat} {env : BEnv} {I O : List (BitVec 8)} {pv : BitVec 64}
    {W : List (BitVec 64)} {h j : Nat} (hO : O.length < 2 ^ 60) (hi : HI W h) (rv : Rp W h pv v)
    (hp : env pvar = pv) (h6 : env 6 = BitVec.ofNat 64 j) (cap : j + (v.enc sh).length ≤ O.length) :
    ∃ E', CExec P K (.call 13 2 [vE pvar]) ⟨env, [I, O], [W]⟩ ⟨E', [I, wr O j (v.enc sh)], [W]⟩ ∧
      E' 6 = BitVec.ofNat 64 (j + (v.enc sh).length) ∧ ∀ i, i ≠ 6 → i ≠ 13 → E' i = env i := by
  obtain ⟨hf, hP⟩ := hP2
  obtain ⟨E'', hx, e6, gl⟩ := ok env I O pv W h j hO hi rv h6 cap
  have hargs : [vE pvar].map (·.denote env) = [pv] := by simp [vE, BExp.denote, hp]
  have hc := call_body (P := P) (f := 2) (K := K) (K' := K') hf (by rw [hP]; exact hK) (d := 13)
    (args := [vE pvar]) (by rw [hP]; rfl) (σ := ⟨env, [I, O], [W]⟩) (σ₁ := ⟨E'', [I, wr O j (v.enc sh)], [W]⟩)
    (by rw [hP]; simp only [hargs]; exact hx)
  refine ⟨_, hc, ?_, fun i n6 n13 => ?_⟩
  · simp only; rw [set_ne' _ _ (by omega)]; simp only [retEnv, if_pos (show 6 < 8 by omega)]; exact e6
  · simp only; rw [set_ne' _ _ n13]; simp only [retEnv]; split
    · exact gl i (by omega) n6
    · rfl

theorem eFlds_ok (hP2 : ∃ hf : 2 < P.length, P[2] = encFn sh) {K K' : Nat} (hK : 72 + K' ≤ K)
    {x : BitVec 64} {l r : C} (okl : EncOK P sh K' l) (okr : EncOK P sh K' r) {I : List (BitVec 8)}
    {W : List (BitVec 64)} {h : Nat} (hi : HI W h) :
    ∀ (fs : List Fld) (env : BEnv) (O : List (BitVec 8)) (q : Nat), O.length < 2 ^ 60 →
      env 10 = x → Rp W h (env 11) l → Rp W h (env 12) r → env 6 = BitVec.ofNat 64 q →
      q + (fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc)).length ≤ O.length →
      ∃ E', CExec P K (eFlds fs) ⟨env, [I, O], [W]⟩
          ⟨E', [I, wr O q (fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc))], [W]⟩ ∧
        E' 6 = BitVec.ofNat 64 (q + (fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc)).length) ∧
        ∀ i, i ≠ 6 → i < 13 → E' i = env i
  | [], env, O, q, hO, h10, h11, h12, h6, cap => by
    have := asg_exec 10 (vE 10) ⟨env, [I, O], [W]⟩
    simp only [vE, BExp.denote, set_same] at this
    simp only [List.flatMap_nil, List.length_nil, Nat.add_zero]
    rw [wr_nil _ _ (by simp at cap; omega)]
    exact ⟨env, .base this, h6, fun _ _ _ => rfl⟩
  | f :: fs, env, O, q, hO, h10, h11, h12, h6, cap => by
    simp only [List.flatMap_cons, List.length_append] at cap ⊢
    have step : ∃ E₁, CExec P K (eFld f) ⟨env, [I, O], [W]⟩
        ⟨E₁, [I, wr O q (encF x (l.enc sh) (r.enc sh) l.senc r.senc f)], [W]⟩ ∧
        E₁ 6 = BitVec.ofNat 64 (q + (encF x (l.enc sh) (r.enc sh) l.senc r.senc f).length) ∧
        ∀ i, i ≠ 6 → i < 13 → E₁ i = env i := by
      cases f with
      | x =>
        have hL : (leN 8 x.toNat).length = 8 := leN_length 8 _
        simp only [encF, hL] at cap ⊢
        have hw := wrB_ok x q I O hO 8 (by omega) (by omega) env [W] h6 h10
        rw [List.take_of_length_le (by omega)] at hw
        refine ⟨_, .base (.seq hw (asg_exec _ _ _)), ?_, fun i n6 _ => set_ne' _ _ n6⟩
        rw [set_eq']; exact addE_den' h6
      | b =>
        have hL : ((leN 8 x.toNat).take 1).length = 1 := by simp [leN_length]
        simp only [encF, hL] at cap ⊢
        have hw := wrB_ok x q I O hO 1 (by omega) (by omega) env [W] h6 h10
        refine ⟨_, .base (.seq hw (asg_exec _ _ _)), ?_, fun i n6 _ => set_ne' _ _ n6⟩
        rw [set_eq']; exact addE_den' h6
      | l =>
        simp only [encF] at cap ⊢
        obtain ⟨E₁, x₁, e6, k₁⟩ := ecall_ok hP2 hK okl hO hi h11 rfl h6 (by omega)
        exact ⟨E₁, x₁, e6, fun i a b => k₁ i a (by omega)⟩
      | r =>
        simp only [encF] at cap ⊢
        obtain ⟨E₁, x₁, e6, k₁⟩ := ecall_ok hP2 hK okr hO hi h12 rfl h6 (by omega)
        exact ⟨E₁, x₁, e6, fun i a b => k₁ i a (by omega)⟩
      | sl =>
        simp only [encF] at cap ⊢
        obtain ⟨E₁, x₁, e6, k₁⟩ := eStr_ok (P := P) (K := K) 11 (.inl rfl) hi (I := I) l h11 h6 (by omega) hO
        exact ⟨E₁, x₁, e6, fun i a b => k₁ i a (by omega) (by omega) (by omega)⟩
      | sr =>
        simp only [encF] at cap ⊢
        obtain ⟨E₁, x₁, e6, k₁⟩ := eStr_ok (P := P) (K := K) 12 (.inr rfl) hi (I := I) r h12 h6 (by omega) hO
        exact ⟨E₁, x₁, e6, fun i a b => k₁ i a (by omega) (by omega) (by omega)⟩
    obtain ⟨E₁, x₁, e6, k₁⟩ := step
    have hl1 := wr_length O q (encF x (l.enc sh) (r.enc sh) l.senc r.senc f) (by omega)
    obtain ⟨E₂, x₂, f6, k₂⟩ := eFlds_ok hP2 hK (x := x) (I := I) okl okr hi fs E₁ _ _ (by rw [hl1]; exact hO)
      (by rw [k₁ 10 (by omega) (by omega)]; exact h10) (by rw [k₁ 11 (by omega) (by omega)]; exact h11)
      (by rw [k₁ 12 (by omega) (by omega)]; exact h12) e6 (by rw [hl1]; omega)
    rw [wr_app _ _ _ _ (by omega)] at x₂
    refine ⟨E₂, .seq x₁ x₂, by rw [f6, Nat.add_assoc], fun i n6 n13 => by rw [k₂ i n6 n13, k₁ i n6 n13]⟩

theorem eDisp_skip {K : Nat} {t : Nat} (ht : t < 256) :
    ∀ (ss : Shape) (i : Nat), t < i → i + ss.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 9 = BitVec.ofNat 64 t → CExec P K (eDisp ss i) ⟨env, H, Wh⟩ ⟨env, H, Wh⟩
  | [], i, _, _, env, H, Wh, _ => by
    have := CExec.base (P := P) (k := K) (asg_exec 10 (vE 10) ⟨env, H, Wh⟩)
    simp [vE, BExp.denote, set_same] at this; exact this
  | fs :: ss, i, hi, hl, env, H, Wh, he => by
    simp only [List.length_cons] at hl
    have hn := CExec.base (P := P) (k := K) (asg_exec 10 (vE 10) ⟨env, H, Wh⟩)
    simp only [vE, BExp.denote, set_same] at hn
    exact .seq (.iteF (by show BExp.denote env (eqE 9 i) = 0; rw [eqE_den env 9 i t he ht (by omega), if_neg (by omega)]) hn)
      (eDisp_skip ht ss (i + 1) (by omega) (by omega) env H Wh he)

theorem eDisp_ok {K : Nat} {t : Nat} (ht : t < 256) {Q : BState → Prop} :
    ∀ (ss : Shape) (i : Nat), i ≤ t → i + ss.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 9 = BitVec.ofNat 64 t →
      (∀ fs, ss[t - i]? = some fs → ∃ σ', CExec P K (eFlds fs) ⟨env, H, Wh⟩ σ' ∧ Q σ' ∧ σ'.env 9 = env 9) →
      (ss[t - i]? = none → Q ⟨env.set 10 (env 10), H, Wh⟩) →
      ∃ σ', CExec P K (eDisp ss i) ⟨env, H, Wh⟩ σ' ∧ Q σ'
  | [], i, _, _, env, H, Wh, _, _, hn => ⟨_, .base (asg_exec _ _ _), hn rfl⟩
  | fs :: ss, i, hi, hl, env, H, Wh, he, hs, hn => by
    simp only [List.length_cons] at hl
    by_cases h : t = i
    · subst h
      obtain ⟨⟨E', H', Wh'⟩, hx, hq, h9⟩ := hs fs (by simp)
      exact ⟨_, .seq (.iteT (by rw [eqE_den env 9 t t he ht ht, if_pos rfl]; decide) hx)
        (eDisp_skip ht ss (t + 1) (by omega) (by omega) E' H' Wh' (by simp only at h9; rw [h9, he])), hq⟩
    · have hnop := CExec.base (P := P) (k := K) (asg_exec 10 (vE 10) ⟨env, H, Wh⟩)
      simp only [vE, BExp.denote, set_same] at hnop
      obtain ⟨σ', hx, hq⟩ := eDisp_ok ht ss (i + 1) (by omega) (by omega) env H Wh he
        (fun e' h' => hs e' (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
        (fun h' => hn (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
      exact ⟨σ', .seq (.iteF (by show BExp.denote env (eqE 9 i) = 0; rw [eqE_den env 9 i t he ht (by omega), if_neg h]) hnop) hx, hq⟩

theorem tag8 {t : Nat} : (BitVec.ofNat 64 t).setWidth 8 = (UInt8.ofNat t).toBitVec := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ehead_exec {W : List (BitVec 64)} {h : Nat} {pv : BitVec 64} {v : C} (hi : HI W h) (rv : Rp W h pv v)
    {env : BEnv} {I O : List (BitVec 8)} {j : Nat} (hp : env 8 = pv) (h6 : env 6 = BitVec.ofNat 64 j)
    (hj : j < O.length) (hO : O.length < 2 ^ 60) :
    ∃ env' pl pr, BExec (.seq (loads 8 9 10 11 12) (.seq (.store 1 (vE 6) (vE 9)) (asg 6 (addE 6 1))))
      ⟨env, [I, O], [W]⟩ ⟨env', [I, wr O j [UInt8.ofNat v.tag]], [W]⟩ ∧ v.tag < 256 ∧
      env' 9 = BitVec.ofNat 64 v.tag ∧ env' 10 = v.xv ∧ env' 11 = pl ∧ env' 12 = pr ∧ Rp W h pl v.lv ∧
      Rp W h pr v.rv ∧ env' 6 = BitVec.ofNat 64 (j + 1) ∧ ∀ i, i ∉ [6, 9, 10, 11, 12] → env' i = env i := by
  obtain ⟨pl, pr, rl, rr, ht, hld⟩ := loads_execE hi rv hp (H := [I, O])
  let e4 := (((env.set 9 (BitVec.ofNat 64 v.tag)).set 10 v.xv).set 11 pl).set 12 pr
  have k4 : ∀ i, i ∉ [9, 10, 11, 12] → e4 i = env i := fun i hi' => by
    simp at hi'; simp only [e4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega),
      set_ne' _ _ (by omega)]
  have e46 : e4 6 = BitVec.ofNat 64 j := by rw [k4 6 (by simp)]; exact h6
  have hix : ((vE 6).denote e4).toNat = j := by simp only [vE, BExp.denote, e46]; exact toNat_h (by omega)
  have hst := BExec.store (b := 1) (i := vE 6) (e := vE 9) (σ := ⟨e4, [I, O], [W]⟩) (by simp) (by
    show ((vE 6).denote e4).toNat < O.length; rw [hix]; exact hj)
  have e49 : e4 9 = BitVec.ofNat 64 v.tag := by
    simp only [e4]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_ne' _ _ (by omega), set_eq']
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, hix] at hst
  rw [show (vE 9).denote e4 = BitVec.ofNat 64 v.tag from e49, tag8, wr_one _ _ _ hj] at hst
  refine ⟨_, pl, pr, .seq hld (.seq hst (asg_exec _ _ _)), ht, ?_, ?_, ?_, ?_, rl, rr, ?_, fun i hi' => ?_⟩
  all_goals simp only []
  · rw [set_ne' _ _ (by omega)]; exact e49
  · rw [set_ne' _ _ (by omega)]; simp [e4, set_ne', set_eq']
  · rw [set_ne' _ _ (by omega)]; simp [e4, set_ne', set_eq']
  · rw [set_ne' _ _ (by omega)]; simp [e4, set_eq']
  · rw [set_eq']; exact addE_den' e46
  · simp at hi'; rw [set_ne' _ _ (by omega), k4 i (by simp; omega)]

/-- **The encoder**: `enc` on a cell of `v` writes `v.enc sh` -/
theorem enc_ok (hP2 : ∃ hf : 2 < P.length, P[2] = encFn sh) (hsh : sh.length < 255) :
    ∀ v, EncOK P sh (72 * v.depth) v := by
  intro v
  induction v with
  | z =>
    intro g I O pv W h j hO hi rv h6 cap
    simp only [C.enc, List.length_cons, List.length_nil] at cap ⊢
    obtain ⟨e', pl, pr, hx, ht, e9, e10, -, -, -, -, e6, ke⟩ := ehead_exec (env := callEnv g [pv]) (I := I) (j := j) hi rv
      (by simp [callEnv]) (by simp [callEnv, h6]) (by omega) hO
    obtain ⟨σ', xd, hq⟩ := eDisp_ok (P := P) (K := 0) (Q := fun σ => σ = ⟨e', [I, wr O j [UInt8.ofNat 255]], [W]⟩)
      ht sh 0 (Nat.zero_le _) (by omega) e' _ _ e9 (fun fs h' => absurd h' (by
        simp only [C.tag]; rw [List.getElem?_eq_none (by omega)]; simp))
      (fun _ => by simp only [set_same]; rfl)
    subst hq
    refine ⟨_, .seq (.base hx) xd, e6, fun i hi' n6 => ?_⟩
    rw [ke i (by simp; omega)]; simp [callEnv, hi']
  | c t x l r ihl ihr =>
    intro g I O pv W h j hO hi rv h6 cap
    have hlen : (C.enc sh (.c t x l r)).length =
        (List.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc) (sh.getD t [])).length + 1 := by
      simp [C.enc]
    obtain ⟨e', pl, pr, hx, ht, e9, e10, e11, e12, rl, rr, e6, ke⟩ := ehead_exec (env := callEnv g [pv]) (I := I) (j := j) hi rv
      (by simp [callEnv]) (by simp [callEnv, h6]) (by omega) hO
    simp only [C.tag, C.xv, C.lv, C.rv] at ht e9 e10 rl rr hx
    have K1 : 72 * (C.c t x l r).depth = 72 + 72 * max l.depth r.depth := by simp only [C.depth]; omega
    have hw1 := wr_length O j [UInt8.ofNat t] (by simp; omega)
    obtain ⟨σ', xd, E', hq, f6, kf⟩ := eDisp_ok (P := P) (K := 72 * (C.c t x l r).depth)
      (Q := fun σ => ∃ E', σ = ⟨E', [I, wr O j (C.enc sh (.c t x l r))], [W]⟩ ∧
        E' 6 = BitVec.ofNat 64 (j + (C.enc sh (.c t x l r)).length) ∧ ∀ i, i ≠ 6 → i < 13 → E' i = e' i)
      ht sh 0 (Nat.zero_le _) (by omega) e' _ _ e9 (fun fs h' => by
        rw [Nat.sub_zero] at h'
        have hg : sh.getD t [] = fs := by simp [List.getD_eq_getElem?_getD, h']
        rw [hg] at hlen
        obtain ⟨E₂, x₂, f6, k₂⟩ := eFlds_ok hP2 (K := 72 * (C.c t x l r).depth) (K' := 72 * max l.depth r.depth)
          (by omega) (x := x) (I := I) (encOK_mono ihl (by omega)) (encOK_mono ihr (by omega)) hi fs e' _ (j + 1)
          (by rw [hw1]; exact hO) e10 (by rw [e11]; exact rl) (by rw [e12]; exact rr) e6 (by rw [hw1]; omega)
        have ea := wr_app O j [UInt8.ofNat t] (fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc)) (by simp only [List.length_cons, List.length_nil]; omega)
        simp only [List.length_cons, List.length_nil, Nat.zero_add] at ea
        rw [ea] at x₂
        have hce : C.enc sh (.c t x l r) = [UInt8.ofNat t] ++ fs.flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc) := by
          simp only [C.enc, hg, List.singleton_append]
        refine ⟨_, x₂, ⟨E₂, ?_, ?_, k₂⟩, k₂ 9 (by omega) (by omega)⟩
        · rw [hce]
        · rw [f6, hlen]; congr 1; omega)
      (fun h' => by
        rw [Nat.sub_zero] at h'
        have hg : sh.getD t [] = [] := by simp [List.getD_eq_getElem?_getD, h']
        have hce : C.enc sh (.c t x l r) = [UInt8.ofNat t] := by simp only [C.enc, hg, List.flatMap_nil]
        refine ⟨e', ?_, ?_, fun _ _ _ => rfl⟩
        · rw [hce, set_same]
        · rw [e6, hlen, hg]; rfl)
    subst hq
    refine ⟨_, .seq (.base hx) xd, f6, fun i hi' n6 => ?_⟩
    rw [kf i n6 (by omega), ke i (by simp; omega)]; simp [callEnv, hi']

end Proven.Mach.Ind
