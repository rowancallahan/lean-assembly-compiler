/- The decoder `dec` and the encoder `enc` of `indProg` (`Compiler/Ind.lean`), once and for all. -/
import Compiler.IndOk

set_option linter.unusedVariables false
namespace Proven.Mach.Ind
open Proven.Mach

theorem unle_lt : ∀ L : List UInt8, unle L < 256 ^ L.length
  | [] => by simp [unle]
  | b :: bs => by
    have := unle_lt bs; have := b.toNat_lt
    simp only [unle, List.length_cons, Nat.pow_succ]
    have : 256 * unle bs + 256 ≤ 256 ^ bs.length * 256 := by
      have := Nat.mul_le_mul_left 256 (show unle bs + 1 ≤ 256 ^ bs.length by omega); rw [Nat.mul_comm 256 (256 ^ _)] at this; omega
    omega

theorem zb (b : UInt8) : b.toBitVec.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem horner (u b : Nat) (hu : u < 2 ^ 56) (hb : b < 256) :
    Op.eval .shl (BitVec.ofNat 64 u) (BitVec.ofNat 64 8) + BitVec.ofNat 64 b = BitVec.ofNat 64 (b + 256 * u) := by
  apply BitVec.eq_of_toNat_eq
  simp [Op.eval, BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]
  congr 1; omega

theorem load_exec {v b : Nat} {i : BExp} {env : BEnv} {H : Heap} {W : WHeap} {I : List (BitVec 8)} {k : Nat}
    {x : BitVec 8} (hH : H[b]? = some I) (hk : (i.denote env).toNat = k) (hx : I[k]? = some x) :
    BExec (.load v b i) ⟨env, H, W⟩ ⟨env.set v (x.setWidth 64), H, W⟩ := by
  subst hk
  obtain ⟨hb, rfl⟩ := List.getElem?_eq_some_iff.1 hH
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  exact BExec.load hb hi

/-- the bytes `L` in `I` from `c` -/
def At (I : List (BitVec 8)) (c : Nat) (L : List UInt8) : Prop :=
  ∀ i, i < L.length → I[c + i]? = L[i]?.map (·.toBitVec)

theorem At.app {I : List (BitVec 8)} {c : Nat} {L₁ L₂ : List UInt8} (h : At I c (L₁ ++ L₂)) :
    At I c L₁ ∧ At I (c + L₁.length) L₂ :=
  ⟨fun i hi => by have := h i (by simp; omega); rwa [List.getElem?_append_left hi] at this,
   fun i hi => by
    have := h (L₁.length + i) (by simp; omega)
    rwa [List.getElem?_append_right (by omega), show L₁.length + i - L₁.length = i by omega, ← Nat.add_assoc] at this⟩

theorem At.cons {I : List (BitVec 8)} {c : Nat} {b : UInt8} {L : List UInt8} (h : At I c (b :: L)) :
    I[c]? = some b.toBitVec ∧ At I (c + 1) L :=
  ⟨by simpa using h 0 (by simp), fun i hi => by
    have := h (i + 1) (by simp; omega); rwa [show c + (i + 1) = c + 1 + i by omega] at this⟩

theorem At.get {I : List (BitVec 8)} {c : Nat} {L : List UInt8} (h : At I c L) (i : Nat) (hi : i < L.length) :
    I[c + i]? = some L[i].toBitVec := by rw [h i hi, List.getElem?_eq_getElem hi]; rfl

theorem rdB_ok (L : List UInt8) (hL : L.length = 8) (c : Nat) (I : List (BitVec 8)) (hI : At I c L)
    (hc : c + 8 < 2 ^ 60) : ∀ k, k ≤ 8 → ∀ (env : BEnv) (H : Heap) (W : WHeap), H[0]? = some I →
      env 4 = BitVec.ofNat 64 c →
      ∃ E', BExec (rdB k) ⟨env, H, W⟩ ⟨E', H, W⟩ ∧ E' 9 = BitVec.ofNat 64 (unle (L.drop (8 - k))) ∧
        ∀ i, i ≠ 9 → i ≠ 12 → E' i = env i
  | 0, _, env, H, W, hH, h4 => ⟨_, asg_exec _ _ _, by
      rw [set_eq', List.drop_eq_nil_of_le (by omega)]; simp [unle, kE, BExp.denote],
      fun i h9 _ => set_ne' _ _ h9⟩
  | k + 1, hk, env, H, W, hH, h4 => by
    obtain ⟨E₁, x₁, v₁, k₁⟩ := rdB_ok L hL c I hI hc k (by omega) env H W hH h4
    have hb := hI.get (7 - k) (by omega)
    have hix : ((addE 4 (7 - k)).denote E₁).toNat = c + (7 - k) :=
      addE_den (by rw [k₁ 4 (by omega) (by omega)]; exact h4) (by omega)
    refine ⟨_, .seq x₁ (.seq (load_exec hH hix hb) (asg_exec _ _ _)), ?_, fun i h9 h12 => ?_⟩
    · rw [set_eq']
      simp only [BExp.denote, vE, kE]
      rw [set_ne' _ _ (by omega), set_eq', v₁, zb]
      have hu := unle_lt (L.drop (8 - k))
      simp only [List.length_drop, hL] at hu
      have : 256 ^ (8 - (8 - k)) ≤ 2 ^ 56 := by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
      rw [show Op.add.eval (Op.shl.eval (BitVec.ofNat 64 (unle (List.drop (8 - k) L))) 8#64)
        (BitVec.ofNat 64 L[7 - k].toNat) = Op.shl.eval (BitVec.ofNat 64 (unle (List.drop (8 - k) L))) (BitVec.ofNat 64 8) +
        BitVec.ofNat 64 L[7 - k].toNat from rfl, horner (unle (List.drop (8 - k) L)) _ (Nat.lt_of_lt_of_le hu this) L[7 - k].toNat_lt]
      rw [show 8 - (k + 1) = 7 - k by omega, List.drop_eq_getElem_cons (i := 7 - k) (l := L) (by omega), show 7 - k + 1 = 8 - k by omega]
      rfl
    · show BEnv.set _ _ _ i = _; rw [set_ne' _ _ h9]; show BEnv.set _ _ _ i = _; rw [set_ne' _ _ h12, k₁ i h9 h12]

theorem At.lt {I : List (BitVec 8)} {c : Nat} {L : List UInt8} (h : At I c L) (hl : 0 < L.length) :
    c + L.length ≤ I.length := by
  obtain ⟨k, hk⟩ : ∃ k, L.length = k + 1 := ⟨L.length - 1, by omega⟩
  have := h k (by omega)
  rw [List.getElem?_eq_getElem (l := L) (by omega)] at this
  have := (List.getElem?_eq_some_iff.1 this).1; omega

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

theorem dcall_ok (hP1 : ∃ hf : 1 < P.length, P[1] = decFn sh) {K K' : Nat} (hK : 48 + K' ≤ K) {v : C}
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

theorem dFlds_ok (hP1 : ∃ hf : 1 < P.length, P[1] = decFn sh) {K K' : Nat} (hK : 48 + K' ≤ K)
    {x : BitVec 64} {l r : C} (okl : l.wf sh → DecOK P sh K' l) (okr : r.wf sh → DecOK P sh K' r) :
    ∀ (fs : List Fld) (env : BEnv) (H : Heap) (I : List (BitVec 8)) (q : Nat) (W : List (BitVec 64)) (h : Nat),
      H[0]? = some I → I.length < 2 ^ 60 → At I q (fs.flatMap (encF x (l.enc sh) (r.enc sh))) → HI W h →
      env 4 = BitVec.ofNat 64 q → env 5 = BitVec.ofNat 64 h →
      h + 4 * (fs.flatMap (encF x (l.enc sh) (r.enc sh))).length ≤ W.length →
      (Fld.l ∈ fs → l.wf sh) → (Fld.r ∈ fs → r.wf sh) →
      (Fld.x ∈ fs ∨ env 9 = x) → (Fld.l ∈ fs ∨ Rp W h (env 10) l) → (Fld.r ∈ fs ∨ Rp W h (env 11) r) →
      ∃ E' W' h', CExec P K (dFlds fs) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
        W'.length = W.length ∧ Agree W W' h ∧ HI W' h' ∧ h ≤ h' ∧
        h' ≤ h + 4 * (fs.flatMap (encF x (l.enc sh) (r.enc sh))).length ∧
        E' 5 = BitVec.ofNat 64 h' ∧ E' 4 = BitVec.ofNat 64 (q + (fs.flatMap (encF x (l.enc sh) (r.enc sh))).length) ∧
        (∀ i, i ∉ [4, 5, 9, 10, 11, 12] → E' i = env i) ∧ E' 9 = x ∧ Rp W' h' (E' 10) l ∧ Rp W' h' (E' 11) r
  | [], env, H, I, q, W, h, hH, hI, hA, hi, h4, h5, cap, wl, wr, ix, il, ir => by
    simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero, Nat.add_zero, List.not_mem_nil, false_or] at *
    refine ⟨_, W, h, .base (asg_exec _ _ _), rfl, Agree.refl _ _, hi, Nat.le_refl _, Nat.le_refl _, ?_, ?_,
      fun i hi' => ?_, ?_, ?_, ?_⟩ <;> simp only [vE, BExp.denote]
    · rw [set_ne' _ _ (by omega)]; exact h5
    · rw [set_ne' _ _ (by omega)]; exact h4
    · rw [set_ne' _ _ (by simp at hi'; omega)]
    · rw [set_eq']; exact ix
    · rw [set_ne' _ _ (by omega)]; exact il
    · rw [set_ne' _ _ (by omega)]; exact ir
  | f :: fs, env, H, I, q, W, h, hH, hI, hA, hi, h4, h5, cap, wl, wr, ix, il, ir => by
    simp only [List.flatMap_cons] at hA cap ⊢
    obtain ⟨hA1, hA2⟩ := hA.app
    -- one field, then the rest
    have step : ∃ E₁ W₁ h₁, CExec P K (dFld f) ⟨env, H, [W]⟩ ⟨E₁, H, [W₁]⟩ ∧ W₁.length = W.length ∧ Agree W W₁ h ∧
        HI W₁ h₁ ∧ h ≤ h₁ ∧ h₁ ≤ h + 4 * (encF x (l.enc sh) (r.enc sh) f).length ∧ E₁ 5 = BitVec.ofNat 64 h₁ ∧
        E₁ 4 = BitVec.ofNat 64 (q + (encF x (l.enc sh) (r.enc sh) f).length) ∧
        (∀ i, i ∉ [4, 5, 9, 10, 11, 12] → E₁ i = env i) ∧
        (Fld.x ∈ fs ∨ E₁ 9 = x) ∧ (Fld.l ∈ fs ∨ Rp W₁ h₁ (E₁ 10) l) ∧ (Fld.r ∈ fs ∨ Rp W₁ h₁ (E₁ 11) r) := by
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
        · right; dsimp only; rw [set_ne' _ _ (by omega), v₁]; simp only [Nat.sub_self, List.drop_zero, unle_leN]
          apply BitVec.eq_of_toNat_eq; simp; omega
        · rcases il with il | il
          · left; simpa using il
          · right; dsimp only; rw [set_ne' _ _ (by omega), k₁ 10 (by omega) (by omega)]; exact il
        · rcases ir with ir | ir
          · left; simpa using ir
          · right; dsimp only; rw [set_ne' _ _ (by omega), k₁ 11 (by omega) (by omega)]; exact ir
      | l =>
        simp only [encF, List.length_append] at hA1 cap ⊢
        obtain ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, gl, rv⟩ := dcall_ok hP1 hK (okl (wl (by simp)))
          (d := 10) (by omega) hH hI hA1 hi h4 h5 (by omega)
        refine ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, fun i hi' => gl i (by simp at hi'; omega)
          (by simp at hi'; omega) (by simp at hi'; omega), ?_, .inr rv, ?_⟩
        · rcases ix with ix | ix
          · left; simpa using ix
          · right; rw [gl 9 (by omega) (by omega) (by omega)]; exact ix
        · rcases ir with ir | ir
          · left; simpa using ir
          · right; rw [gl 11 (by omega) (by omega) (by omega)]; exact ir.mono b1 a1
      | r =>
        simp only [encF, List.length_append] at hA1 cap ⊢
        obtain ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, gl, rv⟩ := dcall_ok hP1 hK (okr (wr (by simp)))
          (d := 11) (by omega) hH hI hA1 hi h4 h5 (by omega)
        refine ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, fun i hi' => gl i (by simp at hi'; omega)
          (by simp at hi'; omega) (by simp at hi'; omega), ?_, ?_, .inr rv⟩
        · rcases ix with ix | ix
          · left; simpa using ix
          · right; rw [gl 9 (by omega) (by omega) (by omega)]; exact ix
        · rcases il with il | il
          · left; simpa using il
          · right; rw [gl 10 (by omega) (by omega) (by omega)]; exact il.mono b1 a1
    obtain ⟨E₁, W₁, h₁, x₁, l1, a1, i1, b1, b2, e5, e4, gl, ix1, il1, ir1⟩ := step
    obtain ⟨E₂, W₂, h₂, x₂, l2, a2, i2, c1, c2, f5, f4, gl2, ix2, il2, ir2⟩ := dFlds_ok hP1 hK okl okr fs E₁ H I _ W₁ h₁
      hH hI hA2 i1 e4 e5 (by rw [l1]; simp only [List.length_append] at cap; omega)
      (fun m => wl (List.mem_cons_of_mem _ m)) (fun m => wr (List.mem_cons_of_mem _ m)) ix1 il1 ir1
    refine ⟨E₂, W₂, h₂, .seq x₁ x₂, l2.trans l1, a1.trans a2 b1, i2, by omega, by simp only [List.length_append]; omega,
      f5, by rw [f4, List.length_append, Nat.add_assoc], fun i hi' => by rw [gl2 i hi', gl i hi'], ix2, il2, ir2⟩

theorem decOK_mono {K K' : Nat} {v : C} (h : DecOK P sh K v) (hk : K ≤ K') : DecOK P sh K' v := by
  intro g H I c W hh a1 a2 a3 a4 a5 a6 a7
  obtain ⟨E', W', h', hx, rest⟩ := h g H I c W hh a1 a2 a3 a4 a5 a6 a7
  exact ⟨E', W', h', hx.mono hk, rest⟩

theorem dDisp_ok {K : Nat} {t : Nat} (ht : t < 256) {Q : BState → Prop} :
    ∀ (ss : Shape) (i : Nat), i ≤ t → i + ss.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 8 = BitVec.ofNat 64 t →
      (∀ fs, ss[t - i]? = some fs → ∃ σ', CExec P K (dFlds fs) ⟨env, H, Wh⟩ σ' ∧ Q σ') →
      (ss[t - i]? = none → Q ⟨env.set 9 (env 9), H, Wh⟩) →
      ∃ σ', CExec P K (dDisp ss i) ⟨env, H, Wh⟩ σ' ∧ Q σ'
  | [], i, _, _, env, H, Wh, _, _, hn => ⟨_, .base (asg_exec _ _ _), hn rfl⟩
  | fs :: ss, i, hi, hl, env, H, Wh, he, hs, hn => by
    simp only [List.length_cons] at hl
    by_cases h : t = i
    · subst h
      obtain ⟨σ', hx, hq⟩ := hs fs (by simp)
      exact ⟨σ', .iteT (by rw [eqE_den env 8 t t he ht ht, if_pos rfl]; decide) hx, hq⟩
    · obtain ⟨σ', hx, hq⟩ := dDisp_ok ht ss (i + 1) (by omega) (by omega) env H Wh he
        (fun e' h' => hs e' (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
        (fun h' => hn (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
      exact ⟨σ', .iteF (by show BExp.denote env (eqE 8 i) = 0; rw [eqE_den env 8 i t he ht (by omega), if_neg h]) hx, hq⟩

theorem tag_byte {t : Nat} (ht : t < 256) : (UInt8.ofNat t).toBitVec.setWidth 64 = BitVec.ofNat 64 t := by
  rw [zb]; congr 1; simp [UInt8.toNat_ofNat]; omega

/-- **The decoder**: `dec` on the bytes of a well-formed `v` builds its cells -/
theorem dec_ok (hP1 : ∃ hf : 1 < P.length, P[1] = decFn sh) (hsh : sh.length < 255) :
    ∀ v, v.wf sh → DecOK P sh (48 * v.depth) v := by
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
    have hlen : (C.enc sh (.c t x l r)).length = (List.flatMap (encF x (l.enc sh) (r.enc sh)) (sh.getD t [])).length + 1 := by
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
    have K1 : 48 * (C.c t x l r).depth = 48 + 48 * max l.depth r.depth := by simp only [C.depth]; omega
    obtain ⟨E₂, W₂, h₂, x₂, l2, a2, i2, b1, b2, f5, f4, gl2, ix2, il2, ir2⟩ := dFlds_ok hP1 (K := 48 * (C.c t x l r).depth)
      (K' := 48 * max l.depth r.depth) (by omega) (x := x) (l := l) (r := r)
      (fun w => decOK_mono (ihl w) (by omega)) (fun w => decOK_mono (ihr w) (by omega)) fs e1 H I (c + 1) W h hH hI hA1 hi
      e14 (by rw [e1k 5 (by omega) (by omega)]; exact h5) (by omega)
      (fun m => by simpa [m] using hlw) (fun m => by simpa [m] using hrw)
      (by by_cases m : Fld.x ∈ fs
          · exact .inl m
          · right; simp [e1, set_eq', set_ne']; exact (hx0 m).symm)
      (by by_cases m : Fld.l ∈ fs
          · exact .inl m
          · right; have : l = .z := by simpa [m] using hlw
            subst this; simp only [e1]; rw [set_ne' _ _ (by omega), set_eq']; exact .z)
      (by by_cases m : Fld.r ∈ fs
          · exact .inl m
          · right; have : r = .z := by simpa [m] using hrw
            subst this; simp only [e1]; rw [set_eq']; exact .z)
    have hb4 : h₂ + 4 ≤ W₂.length := by rw [l2]; omega
    have hx := alloc_exec (H := H) (env := E₂) (vE 8) 9 10 11 12 (by omega) f5 hb4 i2.big
    obtain ⟨σd, xd, hq⟩ := dDisp_ok (P := P) (K := 48 * (C.c t x l r).depth) (Q := fun σ => σ = ⟨E₂, H, [W₂]⟩)
      (show t < 256 by omega) sh 0 (Nat.zero_le _) (by omega) e1 H [W] e18
      (fun fs' h' => by rw [Nat.sub_zero, hfs] at h'; cases h'; exact ⟨_, x₂, rfl⟩)
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

/-- `L` written into `O` at `j` -/
def wr (O : List (BitVec 8)) (j : Nat) (L : List UInt8) : List (BitVec 8) :=
  O.take j ++ L.map (·.toBitVec) ++ O.drop (j + L.length)

theorem wr_get (O : List (BitVec 8)) (j : Nat) (L : List UInt8) (hj : j + L.length ≤ O.length) (i : Nat) :
    (wr O j L)[i]? = if j ≤ i ∧ i < j + L.length then L[i - j]?.map (·.toBitVec) else O[i]? := by
  have hm : min j O.length = j := by omega
  simp only [wr, hm, List.getElem?_append, List.length_append, List.length_take, List.length_map, List.getElem?_take,
    List.getElem?_drop, List.getElem?_map]
  split <;> split <;> (try split) <;> (try split) <;> first | rfl | omega | (congr 1; omega) | skip

theorem wr_length (O : List (BitVec 8)) (j : Nat) (L : List UInt8) (hj : j + L.length ≤ O.length) :
    (wr O j L).length = O.length := by simp [wr]; omega

theorem wr_nil (O : List (BitVec 8)) (j : Nat) (hj : j ≤ O.length) : wr O j [] = O := by simp [wr]

theorem wr_app (O : List (BitVec 8)) (j : Nat) (L₁ L₂ : List UInt8) (hj : j + L₁.length + L₂.length ≤ O.length) :
    wr (wr O j L₁) (j + L₁.length) L₂ = wr O j (L₁ ++ L₂) := by
  apply List.ext_getElem?; intro i
  rw [wr_get _ _ _ (by rw [wr_length _ _ _ (by omega)]; omega), wr_get _ _ _ (by omega),
    wr_get _ _ _ (by simp; omega)]
  simp only [List.length_append, List.getElem?_append]
  repeat' split
  all_goals first | rfl | omega | (congr 1; omega) | rw [Nat.sub_add_eq]

theorem wr_one (O : List (BitVec 8)) (j : Nat) (b : UInt8) (hj : j < O.length) : O.set j b.toBitVec = wr O j [b] := by
  apply List.ext_getElem?; intro i
  rw [wr_get _ _ _ (by simp; omega), List.getElem?_set]
  repeat' split
  all_goals first | rfl | omega | (subst_vars; simp) | (simp at *; omega)

theorem leN_get : ∀ (k n i : Nat), i < k → (leN k n)[i]? = some (UInt8.ofNat (n / 256 ^ i % 256))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, n, 0, _ => by simp [leN]
  | k + 1, n, i + 1, h => by
    simp only [leN, List.getElem?_cons_succ]
    rw [leN_get k (n / 256) i (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ i)]

theorem byte_eq (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (Op.eval .lshr x (BitVec.ofNat 64 (8 * i))).setWidth 8 = (UInt8.ofNat (x.toNat / 256 ^ i % 256)).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp only [Op.eval, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, UInt8.toBitVec_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.pow_mul]
  simp

theorem set_same (env : BEnv) (v : Nat) : env.set v (env v) = env := by
  funext i; simp only [BEnv.set]; split <;> simp_all

theorem wrB_ok (x : BitVec 64) (q : Nat) (I O : List (BitVec 8)) (hO : O.length < 2 ^ 60) :
    ∀ k, k ≤ 8 → q + k ≤ O.length → ∀ (env : BEnv) (W : WHeap), env 6 = BitVec.ofNat 64 q → env 10 = x →
      BExec (wrB k) ⟨env, [I, O], W⟩ ⟨env, [I, wr O q ((leN 8 x.toNat).take k)], W⟩
  | 0, _, hq, env, W, h6, h10 => by
    have := asg_exec 10 (vE 10) ⟨env, [I, O], W⟩
    simp only [vE, BExp.denote, set_same] at this
    rw [List.take_zero, wr_nil _ _ (by omega)]; exact this
  | k + 1, hk, hq, env, W, h6, h10 => by
    have x₁ := wrB_ok x q I O hO k (by omega) (by omega) env W h6 h10
    have hL : (leN 8 x.toNat).length = 8 := leN_length 8 _
    have ht : ((leN 8 x.toNat).take k).length = k := by simp [hL]; omega
    have hw := wr_length O q ((leN 8 x.toNat).take k) (by rw [ht]; omega)
    have hix : ((addE 6 k).denote env).toNat = q + k := addE_den h6 (by omega)
    have := BExec.store (b := 1) (i := addE 6 k) (e := .bin .lshr (vE 10) (kE (8 * k)))
      (σ := ⟨env, [I, wr O q ((leN 8 x.toNat).take k)], W⟩) (by simp) (by
        show ((addE 6 k).denote env).toNat < (wr O q ((leN 8 x.toNat).take k)).length
        rw [hix, hw]; omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, hix] at this
    have hb : (BExp.bin .lshr (vE 10) (kE (8 * k))).denote env = Op.eval .lshr x (BitVec.ofNat 64 (8 * k)) := by
      simp [BExp.denote, vE, kE, h10]
    rw [hb, byte_eq x k (by omega), wr_one _ _ _ (by rw [hw]; omega)] at this
    have hg := leN_get 8 x.toNat k (by omega)
    have e := wr_app O q ((leN 8 x.toNat).take k) [UInt8.ofNat (x.toNat / 256 ^ k % 256)] (by simp [ht]; omega)
    rw [ht] at e; rw [e] at this
    rw [List.take_succ, hg]
    exact .seq x₁ this

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

theorem ecall_ok (hP2 : ∃ hf : 2 < P.length, P[2] = encFn sh) {K K' : Nat} (hK : 56 + K' ≤ K) {v : C}
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

theorem eFlds_ok (hP2 : ∃ hf : 2 < P.length, P[2] = encFn sh) {K K' : Nat} (hK : 56 + K' ≤ K)
    {x : BitVec 64} {l r : C} (okl : EncOK P sh K' l) (okr : EncOK P sh K' r) {I : List (BitVec 8)}
    {W : List (BitVec 64)} {h : Nat} (hi : HI W h) :
    ∀ (fs : List Fld) (env : BEnv) (O : List (BitVec 8)) (q : Nat), O.length < 2 ^ 60 →
      env 10 = x → Rp W h (env 11) l → Rp W h (env 12) r → env 6 = BitVec.ofNat 64 q →
      q + (fs.flatMap (encF x (l.enc sh) (r.enc sh))).length ≤ O.length →
      ∃ E', CExec P K (eFlds fs) ⟨env, [I, O], [W]⟩ ⟨E', [I, wr O q (fs.flatMap (encF x (l.enc sh) (r.enc sh)))], [W]⟩ ∧
        E' 6 = BitVec.ofNat 64 (q + (fs.flatMap (encF x (l.enc sh) (r.enc sh))).length) ∧
        ∀ i, i ≠ 6 → i ≠ 13 → E' i = env i
  | [], env, O, q, hO, h10, h11, h12, h6, cap => by
    have := asg_exec 10 (vE 10) ⟨env, [I, O], [W]⟩
    simp only [vE, BExp.denote, set_same] at this
    simp only [List.flatMap_nil, List.length_nil, Nat.add_zero]
    rw [wr_nil _ _ (by simp at cap; omega)]
    exact ⟨env, .base this, h6, fun _ _ _ => rfl⟩
  | f :: fs, env, O, q, hO, h10, h11, h12, h6, cap => by
    simp only [List.flatMap_cons, List.length_append] at cap ⊢
    have step : ∃ E₁, CExec P K (eFld f) ⟨env, [I, O], [W]⟩
        ⟨E₁, [I, wr O q (encF x (l.enc sh) (r.enc sh) f)], [W]⟩ ∧
        E₁ 6 = BitVec.ofNat 64 (q + (encF x (l.enc sh) (r.enc sh) f).length) ∧ ∀ i, i ≠ 6 → i ≠ 13 → E₁ i = env i := by
      cases f with
      | x =>
        have hL : (leN 8 x.toNat).length = 8 := leN_length 8 _
        simp only [encF, hL] at cap ⊢
        have hw := wrB_ok x q I O hO 8 (by omega) (by omega) env [W] h6 h10
        rw [List.take_of_length_le (by omega)] at hw
        refine ⟨_, .base (.seq hw (asg_exec _ _ _)), ?_, fun i n6 _ => set_ne' _ _ n6⟩
        rw [set_eq']; exact addE_den' h6
      | l =>
        simp only [encF] at cap ⊢
        exact ecall_ok hP2 hK okl hO hi h11 rfl h6 (by omega)
      | r =>
        simp only [encF] at cap ⊢
        exact ecall_ok hP2 hK okr hO hi h12 rfl h6 (by omega)
    obtain ⟨E₁, x₁, e6, k₁⟩ := step
    have hl1 := wr_length O q (encF x (l.enc sh) (r.enc sh) f) (by omega)
    obtain ⟨E₂, x₂, f6, k₂⟩ := eFlds_ok hP2 hK (x := x) (I := I) okl okr hi fs E₁ _ _ (by rw [hl1]; exact hO)
      (by rw [k₁ 10 (by omega) (by omega)]; exact h10) (by rw [k₁ 11 (by omega) (by omega)]; exact h11)
      (by rw [k₁ 12 (by omega) (by omega)]; exact h12) e6 (by rw [hl1]; omega)
    rw [wr_app _ _ _ _ (by omega)] at x₂
    refine ⟨E₂, .seq x₁ x₂, by rw [f6, Nat.add_assoc], fun i n6 n13 => by rw [k₂ i n6 n13, k₁ i n6 n13]⟩

theorem eDisp_ok {K : Nat} {t : Nat} (ht : t < 256) {Q : BState → Prop} :
    ∀ (ss : Shape) (i : Nat), i ≤ t → i + ss.length ≤ 255 → ∀ (env : BEnv) (H : Heap) (Wh : WHeap),
      env 9 = BitVec.ofNat 64 t →
      (∀ fs, ss[t - i]? = some fs → ∃ σ', CExec P K (eFlds fs) ⟨env, H, Wh⟩ σ' ∧ Q σ') →
      (ss[t - i]? = none → Q ⟨env.set 10 (env 10), H, Wh⟩) →
      ∃ σ', CExec P K (eDisp ss i) ⟨env, H, Wh⟩ σ' ∧ Q σ'
  | [], i, _, _, env, H, Wh, _, _, hn => ⟨_, .base (asg_exec _ _ _), hn rfl⟩
  | fs :: ss, i, hi, hl, env, H, Wh, he, hs, hn => by
    simp only [List.length_cons] at hl
    by_cases h : t = i
    · subst h
      obtain ⟨σ', hx, hq⟩ := hs fs (by simp)
      exact ⟨σ', .iteT (by rw [eqE_den env 9 t t he ht ht, if_pos rfl]; decide) hx, hq⟩
    · obtain ⟨σ', hx, hq⟩ := eDisp_ok ht ss (i + 1) (by omega) (by omega) env H Wh he
        (fun e' h' => hs e' (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
        (fun h' => hn (by rw [show t - i = (t - (i + 1)) + 1 by omega]; simpa using h'))
      exact ⟨σ', .iteF (by show BExp.denote env (eqE 9 i) = 0; rw [eqE_den env 9 i t he ht (by omega), if_neg h]) hx, hq⟩

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
    ∀ v, EncOK P sh (56 * v.depth) v := by
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
    have hlen : (C.enc sh (.c t x l r)).length = (List.flatMap (encF x (l.enc sh) (r.enc sh)) (sh.getD t [])).length + 1 := by
      simp [C.enc]
    obtain ⟨e', pl, pr, hx, ht, e9, e10, e11, e12, rl, rr, e6, ke⟩ := ehead_exec (env := callEnv g [pv]) (I := I) (j := j) hi rv
      (by simp [callEnv]) (by simp [callEnv, h6]) (by omega) hO
    simp only [C.tag, C.xv, C.lv, C.rv] at ht e9 e10 rl rr hx
    have K1 : 56 * (C.c t x l r).depth = 56 + 56 * max l.depth r.depth := by simp only [C.depth]; omega
    have hw1 := wr_length O j [UInt8.ofNat t] (by simp; omega)
    obtain ⟨σ', xd, E', hq, f6, kf⟩ := eDisp_ok (P := P) (K := 56 * (C.c t x l r).depth)
      (Q := fun σ => ∃ E', σ = ⟨E', [I, wr O j (C.enc sh (.c t x l r))], [W]⟩ ∧
        E' 6 = BitVec.ofNat 64 (j + (C.enc sh (.c t x l r)).length) ∧ ∀ i, i ≠ 6 → i ≠ 13 → E' i = e' i)
      ht sh 0 (Nat.zero_le _) (by omega) e' _ _ e9 (fun fs h' => by
        rw [Nat.sub_zero] at h'
        have hg : sh.getD t [] = fs := by simp [List.getD_eq_getElem?_getD, h']
        rw [hg] at hlen
        obtain ⟨E₂, x₂, f6, k₂⟩ := eFlds_ok hP2 (K := 56 * (C.c t x l r).depth) (K' := 56 * max l.depth r.depth)
          (by omega) (x := x) (I := I) (encOK_mono ihl (by omega)) (encOK_mono ihr (by omega)) hi fs e' _ (j + 1)
          (by rw [hw1]; exact hO) e10 (by rw [e11]; exact rl) (by rw [e12]; exact rr) e6 (by rw [hw1]; omega)
        have ea := wr_app O j [UInt8.ofNat t] (fs.flatMap (encF x (l.enc sh) (r.enc sh))) (by simp only [List.length_cons, List.length_nil]; omega)
        simp only [List.length_cons, List.length_nil, Nat.zero_add] at ea
        rw [ea] at x₂
        have hce : C.enc sh (.c t x l r) = [UInt8.ofNat t] ++ fs.flatMap (encF x (l.enc sh) (r.enc sh)) := by
          simp only [C.enc, hg, List.singleton_append]
        refine ⟨_, x₂, E₂, ?_, ?_, k₂⟩
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
