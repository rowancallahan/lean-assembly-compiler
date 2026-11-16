/- Bytes in the input block and words read from them, for the decoder and encoder of `indProg` (`Compiler/IndDec.lean`). -/
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

/-! ## writing bytes -/

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

end Proven.Mach.Ind
