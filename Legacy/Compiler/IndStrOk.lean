/- Strings in the decoder and the encoder of `indProg` (`Compiler/Ind.lean`, `dStr` / `eStr`): a string's byte
format `C.senc` (length, 8 bytes little-endian, then the bytes) to and from its cells `C.str`, once and for all. -/
import Legacy.Compiler.IndBytes

set_option linter.unusedVariables false
namespace Proven.Mach.Ind
open Proven.Mach

/-! ## the cells of a string -/

theorem str_cell (st : Nat) (L : List UInt8) : ∃ t x l r, C.str st L = .c t x l r := by
  cases L <;> exact ⟨_, _, _, _, rfl⟩

theorem u8_word (b : UInt8) : UInt8.ofNat (BitVec.ofNat 64 b.toNat).toNat = b := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)]; exact UInt8.ofNat_toNat

@[simp] theorem str_sb (st : Nat) : ∀ L : List UInt8, (C.str st L).sb = L
  | [] => by simp [C.str, C.sb]
  | b :: L => by
    obtain ⟨t, x, l, r, e⟩ := str_cell st L
    rw [C.str, e, C.sb, ← e, str_sb st L, u8_word]

theorem str_nodes (st : Nat) : ∀ L : List UInt8, (C.str st L).nodes = L.length + 1 ∧ (C.str st L).depth = L.length + 1
  | [] => by simp [C.str, C.nodes, C.depth]
  | b :: L => by
    have := str_nodes st L
    simp only [C.str, C.nodes, C.depth, List.length_cons] at this ⊢; omega

theorem IsStr.senc {st : Nat} {v : C} (h : v.IsStr st) : ∃ L, v = C.str st L ∧ v.senc = leN 8 L.length ++ L := by
  obtain ⟨L, rfl⟩ := h; exact ⟨L, rfl, by simp [C.senc]⟩

/-! ## steps -/

theorem allocK_exec {env : BEnv} {H : Heap} {W : List (BitVec 64)} {h : Nat} (t ex el er : BExp) (d : Nat)
    (hd : d ≠ 5) (h5 : env 5 = BitVec.ofNat 64 h) (hb : h + 4 ≤ W.length) (hW : W.length < 2 ^ 60) :
    BExec (allocK t ex el er d) ⟨env, H, [W]⟩
      ⟨(env.set d (BitVec.ofNat 64 h)).set 5 (BitVec.ofNat 64 (h + 4)), H,
        [put W h (t.denote env) (ex.denote env) (el.denote env) (er.denote env)]⟩ := by
  refine .seq (stW_exec 0 t h5 (by omega) hW) (.seq (stW_exec 1 _ h5 (by simp; omega) (by simp; omega))
    (.seq (stW_exec 2 _ h5 (by simp; omega) (by simp; omega)) (.seq (stW_exec 3 _ h5 (by simp; omega) (by simp; omega))
    (.seq (asg_exec _ _ _) ?_))))
  have := asg_exec 5 (addE 5 4) ⟨env.set d ((vE 5).denote env), H, [put W h (t.denote env) (ex.denote env)
    (el.denote env) (er.denote env)]⟩
  simp only [vE, BExp.denote] at this ⊢
  rw [addE_den' (h := h) (by rw [set_ne' _ _ (by omega), h5])] at this
  simp only [put, Nat.add_zero, h5] at this ⊢
  exact this

theorem sub_den (q m : Nat) (h : q + 8 + m < 2 ^ 60) :
    Op.eval .sub (BitVec.ofNat 64 (q + 8 + m)) (Op.eval .add (BitVec.ofNat 64 q) (BitVec.ofNat 64 8)) =
      BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  simp only [Op.eval, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := q) (by omega), Nat.mod_eq_of_lt (a := 8) (by omega), Nat.mod_eq_of_lt (a := q + 8) (by omega),
    Nat.mod_eq_of_lt (a := q + 8 + m) (by omega)]
  omega

theorem Rp.z_ptr {W : List (BitVec 64)} {h : Nat} {p : BitVec 64} (hr : Rp W h p .z) : p = 0 := by
  cases hr; rfl

theorem Rp.c_ptr {W : List (BitVec 64)} {h : Nat} {p : BitVec 64} {t x l r} (hr : Rp W h p (.c t x l r)) :
    4 ≤ p.toNat := by
  cases hr with | c h1 => exact h1

/-! ## the decoder -/

variable {P : Prog}

/-- the loop of `dStr`: a cell per byte, from the last one back -/
theorem dLoop_ok {K : Nat} (st d : Nat) (hd : d ≠ 4 ∧ d ≠ 5 ∧ d ≠ 12 ∧ d ≠ 14) (hst : st + 1 < 256)
    (B : List UInt8) (q : Nat) {H : Heap} {I : List (BitVec 8)} (hH : H[0]? = some I) (hA : At I (q + 8) B)
    (hI : I.length < 2 ^ 60) (hq : q + 8 + B.length ≤ I.length) :
    ∀ m, m ≤ B.length → ∀ (env : BEnv) (W : List (BitVec 64)) (h : Nat), HI W h → env 4 = BitVec.ofNat 64 q →
      env 5 = BitVec.ofNat 64 h → env 14 = BitVec.ofNat 64 (q + 8 + m) →
      Rp W h (env d) (C.str st (B.drop m)) → h + 4 * m ≤ W.length →
      ∃ E' W', CExec P K (.loop (.bin .sub (vE 14) (addE 4 8)) (.base (.seq (asg 14 (.bin .sub (vE 14) (kE 1)))
          (.seq (.load 12 0 (vE 14)) (allocK (kE (st + 1)) (vE 12) (vE d) (kE 0) d))))) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧
        W'.length = W.length ∧ Agree W W' h ∧ HI W' (h + 4 * m) ∧ E' 5 = BitVec.ofNat 64 (h + 4 * m) ∧
        Rp W' (h + 4 * m) (E' d) (C.str st B) ∧ ∀ i, i ≠ 5 → i ≠ 12 → i ≠ 14 → i ≠ d → E' i = env i
  | 0, _, env, W, h, hi, h4, h5, h14, rv, cap => by
    refine ⟨env, W, .loopF ?_, rfl, Agree.refl _ _, by simpa using hi, by simpa using h5, by simpa using rv,
      fun _ _ _ _ _ => rfl⟩
    simp only [BExp.denote, vE, addE, kE, h14, h4, Nat.add_zero]
    have := sub_den q 0 (by omega); simpa using this
  | m + 1, hm, env, W, h, hi, h4, h5, h14, rv, cap => by
    have hc : (BExp.bin .sub (vE 14) (addE 4 8)).denote env ≠ 0 := by
      simp only [BExp.denote, vE, addE, kE, h14, h4]
      rw [show q + 8 + (m + 1) = q + 8 + (m + 1) from rfl, sub_den q (m + 1) (by omega)]
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    let e1 := env.set 14 ((BExp.bin .sub (vE 14) (kE 1)).denote env)
    have e114 : e1 14 = BitVec.ofNat 64 (q + 8 + m) := by
      simp only [e1, set_eq', BExp.denote, vE, kE, Op.eval, h14]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := q + 8 + (m + 1)) (by omega), Nat.mod_eq_of_lt (a := q + 8 + m) (by omega)]
      omega
    have hb := hA.get m (by omega)
    have hix : ((vE 14).denote e1).toNat = q + 8 + m := by
      simp only [vE, BExp.denote, e114]; exact toNat_h (by omega)
    have hld := load_exec (v := 12) (W := [W]) hH hix hb
    let e2 := e1.set 12 ((B[m]'(by omega)).toBitVec.setWidth 64)
    have hcap : h + 4 ≤ W.length := by omega
    have hal := allocK_exec (H := H) (env := e2) (kE (st + 1)) (vE 12) (vE d) (kE 0) d hd.2.1
      (by simp only [e2, e1]; rw [set_ne' _ _ (by omega), set_ne' _ _ (by omega)]; exact h5) hcap hi.big
    have rv2 : Rp (put W h (BitVec.ofNat 64 (st + 1)) (BitVec.ofNat 64 (B[m]'(by omega)).toNat) (env d) 0) (h + 4)
        (BitVec.ofNat 64 h) (C.str st (B.drop m)) := by
      rw [List.drop_eq_getElem_cons (by omega), C.str]
      exact Rp_put hi hst hcap rv .z
    have hden : (kE (st + 1)).denote e2 = BitVec.ofNat 64 (st + 1) ∧
        (vE 12).denote e2 = BitVec.ofNat 64 (B[m]'(by omega)).toNat ∧ (vE d).denote e2 = env d ∧
        (kE 0).denote e2 = 0 := by
      refine ⟨rfl, ?_, ?_, rfl⟩
      · simp only [vE, BExp.denote, e2, set_eq']; exact zb _
      · simp only [vE, BExp.denote, e2, e1]; rw [set_ne' _ _ hd.2.2.1, set_ne' _ _ hd.2.2.2]
    rw [hden.1, hden.2.1, hden.2.2.1, hden.2.2.2] at hal
    let e3 := (e2.set d (BitVec.ofNat 64 h)).set 5 (BitVec.ofNat 64 (h + 4))
    have k3 : ∀ i, i ≠ 5 → i ≠ 12 → i ≠ 14 → i ≠ d → e3 i = env i := fun i a b c dd => by
      simp only [e3, e2, e1]; rw [set_ne' _ _ a, set_ne' _ _ dd, set_ne' _ _ b, set_ne' _ _ c]
    have hi2 := HI_put hi hcap (BitVec.ofNat 64 (st + 1)) (BitVec.ofNat 64 (B[m]'(by omega)).toNat) (env d) 0
    obtain ⟨E', W', x', l', a', i', e5', rv', k'⟩ := dLoop_ok st d hd hst B q hH hA hI hq m (by omega) e3 _ (h + 4) hi2
      (by rw [k3 4 (by omega) (by omega) (by omega) hd.1.symm]; exact h4) (by simp only [e3, set_eq'])
      (by simp only [e3, e2]; rw [set_ne' _ _ (by omega), set_ne' _ _ (fun e => hd.2.2.2 e.symm), set_ne' _ _ (by omega)]
          exact e114)
      (by have : e3 d = BitVec.ofNat 64 h := by simp only [e3]; rw [set_ne' _ _ hd.2.1, set_eq']
          rw [this]; exact rv2) (by rw [put_length]; omega)
    refine ⟨E', W', .loopT hc (.base (.seq (asg_exec _ _ _) (.seq hld hal))) x', by rw [l', put_length],
      (put_agree W h _ _ _ _).trans a' (by omega), by rw [show h + 4 * (m + 1) = h + 4 + 4 * m by omega]; exact i',
      by rw [show h + 4 * (m + 1) = h + 4 + 4 * m by omega]; exact e5',
      by rw [show h + 4 * (m + 1) = h + 4 + 4 * m by omega]; exact rv', fun i a b c dd => by rw [k' i a b c dd, k3 i a b c dd]⟩

theorem unle_n (n : Nat) (hn : n < 2 ^ 60) : BitVec.ofNat 64 (unle ((leN 8 n).drop (8 - 8))) = BitVec.ofNat 64 n := by
  rw [Nat.sub_self, List.drop_zero, unle_leN, Nat.mod_eq_of_lt (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl]; omega)]

/-- **A string from the input**: `dStr` on `C.senc` of the string `B` builds its cells -/
theorem dStr_ok {K : Nat} (st d : Nat) (hd : d = 10 ∨ d = 11) (hst : st + 1 < 256) (B : List UInt8) {env : BEnv}
    {H : Heap} {I : List (BitVec 8)} {q : Nat} {W : List (BitVec 64)} {h : Nat} (hH : H[0]? = some I)
    (hI : I.length < 2 ^ 60) (hA : At I q (leN 8 B.length ++ B)) (hi : HI W h) (h4 : env 4 = BitVec.ofNat 64 q)
    (h5 : env 5 = BitVec.ofNat 64 h) (cap : h + 4 * (leN 8 B.length ++ B).length ≤ W.length) :
    ∃ E' W' h', CExec P K (dStr st d) ⟨env, H, [W]⟩ ⟨E', H, [W']⟩ ∧ W'.length = W.length ∧ Agree W W' h ∧
      HI W' h' ∧ h ≤ h' ∧ h' ≤ h + 4 * (leN 8 B.length ++ B).length ∧ E' 5 = BitVec.ofNat 64 h' ∧
      E' 4 = BitVec.ofNat 64 (q + (leN 8 B.length ++ B).length) ∧ (∀ i, i ∉ [4, 5, 12, 13, 14, d] → E' i = env i) ∧
      Rp W' h' (E' d) (C.str st B) := by
  have hL : (leN 8 B.length).length = 8 := leN_length 8 _
  simp only [List.length_append, hL] at cap ⊢
  have hq := hA.lt (by simp [hL]; omega)
  simp only [List.length_append, hL] at hq
  obtain ⟨hA8, hAB⟩ := hA.app
  rw [hL] at hAB
  have hW := hi.big; have hh := hi.hle
  let e1 := env.set 13 ((vE 9).denote env)
  obtain ⟨E₁, x₁, v₁, k₁⟩ := rdB_ok (leN 8 B.length) hL q I hA8 (by omega) 8 (Nat.le_refl _) e1 H [W] hH
    (by simp only [e1]; rw [set_ne' _ _ (by omega)]; exact h4)
  rw [unle_n _ (by omega)] at v₁
  let e5 := (((E₁.set 14 ((vE 9).denote E₁)).set 9 ((vE 13).denote (E₁.set 14 ((vE 9).denote E₁)))).set 13
    ((vE 14).denote ((E₁.set 14 ((vE 9).denote E₁)).set 9 ((vE 13).denote (E₁.set 14 ((vE 9).denote E₁)))))).set 14
    ((BExp.bin .add (addE 4 8) (vE 13)).denote (((E₁.set 14 ((vE 9).denote E₁)).set 9
      ((vE 13).denote (E₁.set 14 ((vE 9).denote E₁)))).set 13 ((vE 14).denote ((E₁.set 14 ((vE 9).denote E₁)).set 9
      ((vE 13).denote (E₁.set 14 ((vE 9).denote E₁)))))))
  have x5 : BExec (.seq (asg 14 (vE 9)) (.seq (asg 9 (vE 13)) (.seq (asg 13 (vE 14))
      (asg 14 (.bin .add (addE 4 8) (vE 13)))))) ⟨E₁, H, [W]⟩ ⟨e5, H, [W]⟩ :=
    .seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) (asg_exec _ _ _)))
  have k1 : ∀ i, i ≠ 9 → i ≠ 12 → i ≠ 13 → E₁ i = env i := fun i a b c => by
    rw [k₁ i a b]; simp only [e1]; rw [set_ne' _ _ c]
  have k14 := k1 4 (by omega) (by omega) (by omega)
  have k113 := k₁ 13 (by omega) (by omega)
  have e5_4 : e5 4 = BitVec.ofNat 64 q := by simp [e5, BEnv.set, vE, BExp.denote, k14, h4]
  have e5_13 : e5 13 = BitVec.ofNat 64 B.length := by simp [e5, BEnv.set, vE, BExp.denote, v₁]
  have e5_9 : e5 9 = env 9 := by simp [e5, BEnv.set, vE, BExp.denote, k113, e1]
  have e5_14 : e5 14 = BitVec.ofNat 64 (q + 8 + B.length) := by
    simp [e5, BEnv.set, vE, BExp.denote, addE, kE, Op.eval, k14, h4, v₁]
    rw [BitVec.ofNat_add, BitVec.ofNat_add]
  have e5k : ∀ i, i ≠ 9 → i ≠ 12 → i ≠ 13 → i ≠ 14 → e5 i = env i := fun i a b c dd => by
    simp only [e5]; rw [set_ne' _ _ dd, set_ne' _ _ c, set_ne' _ _ a, set_ne' _ _ dd, k1 i a b c]
  have hd' : d ≠ 4 ∧ d ≠ 5 ∧ d ≠ 12 ∧ d ≠ 14 := by omega
  have e5_5 : e5 5 = BitVec.ofNat 64 h := by rw [e5k 5 (by omega) (by omega) (by omega) (by omega)]; exact h5
  have xa := allocK_exec (H := H) (env := e5) (kE st) (kE 0) (kE 0) (kE 0) d hd'.2.1 e5_5 (by omega) hW
  rw [show (kE st).denote e5 = BitVec.ofNat 64 st from rfl, show (kE 0).denote e5 = BitVec.ofNat 64 0 from rfl] at xa
  let e6 := (e5.set d (BitVec.ofNat 64 h)).set 5 (BitVec.ofNat 64 (h + 4))
  have hi6 := HI_put hi (show h + 4 ≤ W.length by omega) (BitVec.ofNat 64 st) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 0)
  have rv6 : Rp (put W h (BitVec.ofNat 64 st) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)) (h + 4) (e6 d)
      (C.str st (B.drop B.length)) := by
    rw [List.drop_length]
    have : e6 d = BitVec.ofNat 64 h := by simp only [e6]; rw [set_ne' _ _ hd'.2.1, set_eq']
    rw [this]; exact Rp_put hi (by omega) (by omega) .z .z
  have e6k : ∀ i, i ≠ 5 → i ≠ d → e6 i = e5 i := fun i a b => by simp only [e6]; rw [set_ne' _ _ a, set_ne' _ _ b]
  obtain ⟨E₇, W₇, x₇, l₇, a₇, i₇, f₇, r₇, k₇⟩ := dLoop_ok (P := P) (K := K) st d hd' hst B q hH hAB hI (by omega)
    B.length (Nat.le_refl _) e6 _ (h + 4) hi6 (by rw [e6k 4 (by omega) (by omega)]; exact e5_4) (by simp only [e6, set_eq'])
    (by rw [e6k 14 (by omega) (by omega)]; exact e5_14) rv6 (by rw [put_length]; omega)
  have e7_4 : E₇ 4 = BitVec.ofNat 64 q := by
    rw [k₇ 4 (by omega) (by omega) (by omega) (by omega), e6k 4 (by omega) (by omega)]; exact e5_4
  have e7_13 : E₇ 13 = BitVec.ofNat 64 B.length := by
    rw [k₇ 13 (by omega) (by omega) (by omega) (by omega), e6k 13 (by omega) (by omega)]; exact e5_13
  refine ⟨_, W₇, h + 4 + 4 * B.length, .seq (.base (.seq (asg_exec _ _ _) (.seq x₁ (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _)
      (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) xa)))))))
    (.seq x₇ (.base (asg_exec _ _ _))), by rw [l₇, put_length], (put_agree W h _ _ _ _).trans a₇ (by omega), i₇,
    by omega, by omega, ?_, ?_, fun i hi' => ?_, ?_⟩
  · rw [set_ne' _ _ (by omega)]; exact f₇
  · rw [set_eq']; simp only [BExp.denote, addE, kE, vE, Op.eval, e7_4, e7_13]
    rw [show q + (8 + B.length) = q + 8 + B.length by omega, BitVec.ofNat_add, BitVec.ofNat_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi'
    obtain ⟨n4, n5, n12, n13, n14, nd⟩ := hi'
    dsimp only; rw [set_ne' _ _ n4, k₇ i n5 n12 n14 nd, e6k i n5 nd]
    by_cases n9 : i = 9
    · subst n9; exact e5_9
    · exact e5k i n9 n12 n13 n14
  · rw [set_ne' _ _ (by omega)]; exact r₇

/-! ## the encoder -/

theorem x8 (x : BitVec 64) : x.setWidth 8 = (UInt8.ofNat x.toNat).toBitVec := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ptr2 {W : List (BitVec 64)} {h : Nat} (hi : HI W h) {p : BitVec 64} {v : C} (rv : Rp W h p v) (c : Nat)
    (hc : c < 4) {env : BEnv} (he : env 14 = p) : ((addE 14 c).denote env).toNat = p.toNat + c := by
  have := rv.lt4 hi.h4; have := hi.hle; have := hi.big
  simp only [addE, kE, BExp.denote, Op.eval, he, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

@[simp] theorem sb_z : C.sb .z = [] := by simp [C.sb]
@[simp] theorem sb_cz (t : Nat) (x : BitVec 64) (r : C) : C.sb (.c t x .z r) = [] := by simp [C.sb]
@[simp] theorem sb_cc (t : Nat) (x : BitVec 64) (r : C) (t' : Nat) (x' : BitVec 64) (l' r' : C) :
    C.sb (.c t x (.c t' x' l' r') r) = UInt8.ofNat x.toNat :: C.sb (.c t' x' l' r') := by simp [C.sb]

/-- the count loop of `eCnt` -/
theorem cnt_ok {K : Nat} {W : List (BitVec 64)} {h : Nat} (hi : HI W h) {H : Heap} :
    ∀ (v : C) (pv pl : BitVec 64) (env : BEnv) (c : Nat), Rp W h pv v → W[pv.toNat + 2]? = some pl →
      env 14 = pv → env 13 = pl → env 15 = BitVec.ofNat 64 c →
      ∃ E', CExec P K (.loop (vE 13) (.base (.seq (asg 15 (addE 15 1)) (.seq (asg 14 (vE 13))
          (.load64 13 0 (addE 14 2)))))) ⟨env, H, [W]⟩ ⟨E', H, [W]⟩ ∧
        E' 15 = BitVec.ofNat 64 (c + v.sb.length) ∧ ∀ i, i ≠ 13 → i ≠ 14 → i ≠ 15 → E' i = env i := by
  intro v
  induction v with
  | z =>
    intro pv pl env c rv e2 h14 h13 h15
    have := rv.z_ptr; subst this
    have : pl = 0 := by have := hi.z0.2.2.1; simp at e2; rw [e2] at this; cases this; rfl
    subst this
    exact ⟨env, .loopF (by simp [vE, BExp.denote, h13]), by simpa using h15, fun _ _ _ _ => rfl⟩
  | c t x l r ihl _ =>
    intro pv pl env c rv e2 h14 h13 h15
    obtain ⟨-, -, -, ⟨pl', f2, rl⟩, -⟩ := rv.read hi.z0
    simp only [C.lv] at rl
    rw [f2] at e2; cases e2
    · cases l with
      | z =>
        have := rl.z_ptr; subst this
        exact ⟨env, .loopF (by simp [vE, BExp.denote, h13]), by simpa using h15, fun _ _ _ _ => rfl⟩
      | c t' x' l' r' =>
        have h4 := rl.c_ptr
        obtain ⟨-, -, -, ⟨pll, g2, -⟩, -⟩ := rl.read hi.z0
        let e1 := (env.set 15 ((addE 15 1).denote env)).set 14 ((vE 13).denote (env.set 15 ((addE 15 1).denote env)))
        have e114 : e1 14 = pl := by simp [e1, BEnv.set, vE, BExp.denote, h13]
        have hld := load64_exec (v := 13) (H := H) (env := e1) (ptr2 hi rl 2 (by omega) e114) g2
        obtain ⟨E', x', f15, k'⟩ := ihl pl pll (e1.set 13 pll) (c + 1) rl g2 (by simp [BEnv.set, e114])
          (by simp [BEnv.set]) (by simp [e1, BEnv.set, addE, kE, vE, BExp.denote, Op.eval, h15, BitVec.ofNat_add])
        refine ⟨E', .loopT (by simp [vE, BExp.denote, h13]; intro e; rw [e] at h4; simp at h4)
          (.base (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) hld))) x', ?_, fun i a b cc => ?_⟩
        · rw [f15, sb_cc]; simp only [List.length_cons]; congr 1; omega
        · rw [k' i a b cc]; simp [e1, BEnv.set, a, b, cc]

/-- the byte loop `eBytes` -/
theorem bytes_ok {K : Nat} {W : List (BitVec 64)} {h : Nat} (hi : HI W h) {I : List (BitVec 8)} :
    ∀ (v : C) (pv pl : BitVec 64) (env : BEnv) (O : List (BitVec 8)) (q : Nat), Rp W h pv v →
      W[pv.toNat + 2]? = some pl → env 14 = pv → env 15 = pl → env 6 = BitVec.ofNat 64 q →
      q + v.sb.length ≤ O.length → O.length < 2 ^ 60 →
      ∃ E', CExec P K eBytes ⟨env, [I, O], [W]⟩ ⟨E', [I, wr O q v.sb], [W]⟩ ∧
        E' 6 = BitVec.ofNat 64 (q + v.sb.length) ∧ ∀ i, i ≠ 6 → i ≠ 13 → i ≠ 14 → i ≠ 15 → E' i = env i := by
  intro v
  induction v with
  | z =>
    intro pv pl env O q rv e2 h14 h15 h6 cap hO
    have := rv.z_ptr; subst this
    have : pl = 0 := by have := hi.z0.2.2.1; simp at e2; rw [e2] at this; cases this; rfl
    subst this
    exact ⟨env, by rw [sb_z, wr_nil _ _ (by simp at cap; omega)]; exact .loopF (by simp [vE, BExp.denote, h15]),
      by simpa using h6, fun _ _ _ _ _ => rfl⟩
  | c t x l r ihl _ =>
    intro pv pl env O q rv e2 h14 h15 h6 cap hO
    obtain ⟨-, -, f1, ⟨pl', f2, rl⟩, -⟩ := rv.read hi.z0
    simp only [C.lv, C.xv] at rl f1
    rw [f2] at e2; cases e2
    · cases l with
      | z =>
        have := rl.z_ptr; subst this
        exact ⟨env, by rw [sb_cz, wr_nil _ _ (by simp at cap; omega)]; exact .loopF (by simp [vE, BExp.denote, h15]),
          by simpa using h6, fun _ _ _ _ _ => rfl⟩
      | c t' x' l' r' =>
        have h4 := rl.c_ptr
        obtain ⟨-, -, -, ⟨pll, g2, -⟩, -⟩ := rl.read hi.z0
        rw [sb_cc] at cap ⊢
        simp only [List.length_cons] at cap ⊢
        have hl1 := load64_exec (v := 13) (H := [I, O]) (env := env) (ptr2 hi rv 1 (by omega) h14) f1
        have hq : ((vE 6).denote (env.set 13 x)).toNat = q := by
          simp only [vE, BExp.denote]; rw [set_ne' _ _ (by omega), h6]; exact toNat_h (by omega)
        have hst := BExec.store (b := 1) (i := vE 6) (e := vE 13) (σ := ⟨env.set 13 x, [I, O], [W]⟩) (by simp) (by
          show ((vE 6).denote (env.set 13 x)).toNat < O.length; rw [hq]; omega)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero, hq] at hst
        rw [show (vE 13).denote (env.set 13 x) = x by simp [vE, BExp.denote, set_eq'], x8,
          wr_one _ _ _ (by omega)] at hst
        let e2 := ((env.set 13 x).set 6 ((addE 6 1).denote (env.set 13 x))).set 14
          ((vE 15).denote ((env.set 13 x).set 6 ((addE 6 1).denote (env.set 13 x))))
        have e214 : e2 14 = pl := by simp [e2, BEnv.set, vE, BExp.denote, h15]
        have hl2 := load64_exec (v := 15) (H := [I, wr O q [UInt8.ofNat x.toNat]]) (env := e2)
          (ptr2 hi rl 2 (by omega) e214) g2
        have hw1 := wr_length O q [UInt8.ofNat x.toNat] (by simp; omega)
        obtain ⟨E', xr, f6, k'⟩ := ihl pl pll (e2.set 15 pll) (wr O q [UInt8.ofNat x.toNat]) (q + 1) rl g2
          (by simp [BEnv.set, e214]) (by simp [BEnv.set])
          (by simp [e2, BEnv.set, addE, kE, vE, BExp.denote, Op.eval, h6, BitVec.ofNat_add]) (by rw [hw1]; omega)
          (by rw [hw1]; exact hO)
        have ea := wr_app O q [UInt8.ofNat x.toNat] (C.c t' x' l' r').sb (by simp; omega)
        simp only [List.length_singleton, List.singleton_append] at ea
        rw [ea] at xr
        refine ⟨E', .loopT (by simp [vE, BExp.denote, h15]; intro e; rw [e] at h4; simp at h4)
          (.base (.seq hl1 (.seq hst (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) hl2))))) xr, ?_, fun i a b c d => ?_⟩
        · rw [f6]; congr 1; omega
        · rw [k' i a b c d]; simp [e2, BEnv.set, a, b, c, d]

theorem leN8_n (n : Nat) (hn : n < 2 ^ 60) : (leN 8 (BitVec.ofNat 64 n).toNat).take 8 = leN 8 n := by
  rw [List.take_of_length_le (by simp [leN_length]), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- **A string to the output**: `eStr` on the cells of `v` writes `C.senc v` -/
theorem eStr_ok {K : Nat} (p : Nat) (hp : p = 11 ∨ p = 12) {W : List (BitVec 64)} {h : Nat} (hi : HI W h)
    {I O : List (BitVec 8)} (v : C) {env : BEnv} {q : Nat} (rv : Rp W h (env p) v) (h6 : env 6 = BitVec.ofNat 64 q)
    (cap : q + v.senc.length ≤ O.length) (hO : O.length < 2 ^ 60) :
    ∃ E', CExec P K (eStr p) ⟨env, [I, O], [W]⟩ ⟨E', [I, wr O q v.senc], [W]⟩ ∧
      E' 6 = BitVec.ofNat 64 (q + v.senc.length) ∧ ∀ i, i ≠ 6 → i ≠ 13 → i ≠ 14 → i ≠ 15 → E' i = env i := by
  have hL : (leN 8 v.sb.length).length = 8 := leN_length 8 _
  simp only [C.senc, List.length_append, hL] at cap ⊢
  obtain ⟨-, -, -, ⟨pl, f2, -⟩, -⟩ := rv.read hi.z0
  -- the count
  let e1 := ((env.set 15 ((kE 0).denote env)).set 14 ((vE p).denote (env.set 15 ((kE 0).denote env))))
  have e114 : e1 14 = env p := by simp [e1, BEnv.set, vE, BExp.denote]; omega
  have hl1 := load64_exec (v := 13) (H := [I, O]) (env := e1) (ptr2 hi rv 2 (by omega) e114) f2
  obtain ⟨E₁, x₁, c15, k₁⟩ := cnt_ok (P := P) (K := K) hi (H := [I, O]) v (env p) pl (e1.set 13 pl) 0 rv f2
    (by simp [BEnv.set, e114]) (by simp [BEnv.set]) (by simp [e1, BEnv.set, kE, BExp.denote])
  rw [Nat.zero_add] at c15
  have k1 : ∀ i, i ≠ 13 → i ≠ 14 → i ≠ 15 → E₁ i = env i := fun i a b c => by
    rw [k₁ i a b c]; simp [e1, BEnv.set, a, b, c]
  -- the length
  let e2 := (E₁.set 14 ((vE 10).denote E₁)).set 10 ((vE 15).denote (E₁.set 14 ((vE 10).denote E₁)))
  have hn : v.sb.length < 2 ^ 60 := by omega
  have hw := wrB_ok (BitVec.ofNat 64 v.sb.length) q I O hO 8 (Nat.le_refl _) (by omega) e2 [W]
    (by simp [e2, BEnv.set]; rw [k1 6 (by omega) (by omega) (by omega)]; exact h6)
    (by simp [e2, BEnv.set, vE, BExp.denote, c15])
  rw [leN8_n _ hn] at hw
  let e3 := (((e2.set 6 ((addE 6 8).denote e2)).set 10 ((vE 14).denote (e2.set 6 ((addE 6 8).denote e2)))).set 14
    ((vE p).denote ((e2.set 6 ((addE 6 8).denote e2)).set 10 ((vE 14).denote (e2.set 6 ((addE 6 8).denote e2))))))
  have e314 : e3 14 = env p := by
    have := k1 p (by omega) (by omega) (by omega)
    simp [e3, e2, BEnv.set, vE, BExp.denote]
    rcases hp with rfl | rfl <;> simpa using this
  have hw1 := wr_length O q (leN 8 v.sb.length) (by rw [hL]; omega)
  have hl3 := load64_exec (v := 15) (H := [I, wr O q (leN 8 v.sb.length)]) (env := e3) (ptr2 hi rv 2 (by omega) e314) f2
  obtain ⟨E₄, x₄, f6, k₄⟩ := bytes_ok (P := P) (K := K) hi (I := I) v (env p) pl (e3.set 15 pl) _ (q + 8) rv f2
    (by simp [BEnv.set, e314]) (by simp [BEnv.set])
    (by simp [e3, e2, BEnv.set, addE, kE, vE, BExp.denote, Op.eval]; rw [k1 6 (by omega) (by omega) (by omega), h6,
      BitVec.ofNat_add]) (by rw [hw1]; omega) (by rw [hw1]; exact hO)
  have ea := wr_app O q (leN 8 v.sb.length) v.sb (by rw [hL]; omega)
  rw [hL] at ea; rw [ea] at x₄
  refine ⟨E₄, .seq (.seq (.base (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) hl1))) x₁)
    (.seq (.base (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _) (.seq hw (.seq (asg_exec _ _ _) (.seq (asg_exec _ _ _)
      (.seq (asg_exec _ _ _) hl3))))))) x₄), by rw [f6, Nat.add_assoc], fun i a b c d => ?_⟩
  rw [k₄ i a b c d]
  by_cases i10 : i = 10
  · subst i10; simp [e3, e2, BEnv.set, vE, BExp.denote]; exact k1 10 (by omega) (by omega) (by omega)
  · simp [e3, e2, BEnv.set, a, b, c, d, i10]; exact k1 i b c d

end Proven.Mach.Ind
