/- `StepAt` lemmas, group C (see JArmStep.lean): code 1, the `li` atom. -/
import Nano.Run.JArmStep
import Nano.Run.JArmInst
import Nano.Run.NatT.Li
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-! ## small facts -/

private theorem c_mul_ne {a b : UInt64} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro e; apply h; rw [e, UInt64.zero_mul]
  · intro e; apply h; rw [e, UInt64.mul_zero]

private theorem c_mul_one {a b : UInt64} (h : (a * b == 1) = true) : a ≠ 0 ∧ b ≠ 0 := by
  apply c_mul_ne
  intro e
  rw [e] at h
  exact absurd h (by decide)

private theorem c_m26 {l : List J} {m : Nat} {k a b x : UInt64} (h : m26 l m k a b x ≠ 0) :
    kd l m = k ∧ fA l m = a ∧ fB l m = b ∧ fC l m = x := by
  unfold m26 at h
  by_cases hk : (kd l m == k) = true
  · rw [if_pos hk] at h
    obtain ⟨h1, h3⟩ := c_mul_ne h
    obtain ⟨h1, h2⟩ := c_mul_ne h1
    refine ⟨eq_of_beq hk, ?_, ?_, ?_⟩
    · unfold eqb at h1; by_cases e : (fA l m == a) = true
      · exact eq_of_beq e
      · rw [if_neg e] at h1; exact absurd rfl h1
    · unfold eqb at h2; by_cases e : (fB l m == b) = true
      · exact eq_of_beq e
      · rw [if_neg e] at h2; exact absurd rfl h2
    · unfold eqb at h3; by_cases e : (fC l m == x) = true
      · exact eq_of_beq e
      · rw [if_neg e] at h3; exact absurd rfl h3
  · rw [if_neg hk] at h; exact absurd rfl h

private theorem c_toU_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a.toUInt64 = b.toUInt64) : a = b := by
  have := congrArg UInt64.toNat h
  rwa [ArmRA.toU_toNat ha, ArmRA.toU_toNat hb] at this

private theorem c_toU_self (v : UInt64) : v.toNat.toUInt64 = v :=
  ArmRA.u64 (ArmRA.toU_toNat (UInt64.toNat_lt v))

/-- the view determines an `addi` -/
private theorem c_view_addi {l : List J} (hJ : ∀ j ∈ l, JOK j) {m d n c : Nat} (hk : kd l m = 1)
    (hA : fA l m = d.toUInt64) (hB : fB l m = n.toUInt64) (hC : fC l m = c.toUInt64)
    (hd : d < 32) (hn : n < 32) (hc : c < 2048) : l[m]? = some (.addi d n (c : Int)) := by
  cases hg : l[m]? with
  | none => rw [kd, hg] at hk; exact absurd hk (by decide)
  | some j =>
    have hj : JOK j := hJ j (List.mem_of_getElem? hg)
    rw [kd, hg] at hk; rw [fA, hg] at hA; rw [fB, hg] at hB; rw [fC, hg] at hC
    have hk' : jk j = 1 := hk
    cases j <;> try (simp only [jk] at hk'; exact absurd hk' (by decide))
    rename_i d' n' imm
    have g : d' < 32 ∧ n' < 32 ∧ -2048 ≤ imm ∧ imm < 2048 := hj.1
    have e1 : d' = d := c_toU_inj (by omega) (by omega) hA
    have e2 : n' = n := c_toU_inj (by omega) (by omega) hB
    have e3 : (iu imm).toNat = c := by
      have hC' : iu imm = c.toUInt64 := hC
      rw [hC', ArmRA.toU_toNat (by omega)]
    rw [iu_toNat] at e3
    have e4 : imm = (c : Int) := by omega
    rw [e1, e2, e4]

/-- the view determines an `slli _ _ 8` -/
private theorem c_view_slli {l : List J} (hJ : ∀ j ∈ l, JOK j) {m d n : Nat} (hk : kd l m = 2)
    (hA : fA l m = d.toUInt64) (hB : fB l m = n.toUInt64) (hC : fC l m = 8)
    (hd : d < 32) (hn : n < 32) : l[m]? = some (.slli d n 8) := by
  cases hg : l[m]? with
  | none => rw [kd, hg] at hk; exact absurd hk (by decide)
  | some j =>
    have hj : JOK j := hJ j (List.mem_of_getElem? hg)
    rw [kd, hg] at hk; rw [fA, hg] at hA; rw [fB, hg] at hB; rw [fC, hg] at hC
    have hk' : jk j = 2 := hk
    cases j <;> try (simp only [jk] at hk'; exact absurd hk' (by decide))
    rename_i d' n' sh
    have g : d' < 32 ∧ n' < 32 ∧ sh < 64 := hj.1
    have e1 : d' = d := c_toU_inj (by omega) (by omega) hA
    have e2 : n' = n := c_toU_inj (by omega) (by omega) hB
    have hC' : sh.toUInt64 = (8 : Nat).toUInt64 := hC
    have e3 : sh = 8 := c_toU_inj (by omega) (by omega) hC'
    rw [e1, e2, e3]

private theorem c_drop_cons {l : List J} {m : Nat} {x : J} (h : l[m]? = some x) : l.drop m = x :: l.drop (m + 1) := by
  obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.drop_eq_getElem_cons hm

private theorem c_mkAtom {l : List J} {d n : Nat} {imm : Int} (h : l[0]? = some (.addi d n imm)) :
    mkAtom 1 l = some (.li d (liV 8 l 1 0)) := by
  cases l with
  | nil => simp at h
  | cons i r =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; rfl

/-! ## the byte sequence, front to back -/

/-- `k` pairs `slli d d 8; addi d d byte`, bytes from the top of `s` -/
private def liF (d : Nat) : Nat → Nat → List J
  | 0, _ => []
  | k + 1, s => .slli d d 8 :: .addi d d ((s / 2 ^ 56 % 256 : Nat) : Int) :: liF d k (s * 256 % 2 ^ 64)

private theorem c_byte_a (v j : Nat) (hv : v < 2 ^ 64) (hj : j < 8) :
    (v * 2 ^ (8 * j) % 2 ^ 64) / 2 ^ 56 % 256 = v / 2 ^ (56 - 8 * j) % 256 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceMul, Nat.reduceSub, Nat.reducePow] <;> omega

private theorem c_byte_b (v j : Nat) (hj : j < 8) :
    (v * 2 ^ (8 * j) % 2 ^ 64) * 256 % 2 ^ 64 = v * 2 ^ (8 * (j + 1)) % 2 ^ 64 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow] <;> omega

private theorem c_liF_liB (d v : Nat) (hv : v < 2 ^ 64) : ∀ (k j : Nat), j + k ≤ 8 →
    liB d v j ++ liF d k (v * 2 ^ (8 * j) % 2 ^ 64) = liB d v (j + k)
  | 0, j, _ => by simp [liF]
  | k + 1, j, h => by
    have ih := c_liF_liB d v hv k (j + 1) (by omega)
    rw [show j + (k + 1) = j + 1 + k by omega, ← ih, liF, c_byte_a v j hv (by omega), c_byte_b v j (by omega)]
    simp only [liB, liJ, List.append_assoc, List.cons_append, List.nil_append]

private theorem c_liF8 (d : Nat) (v : UInt64) : liF d 8 v.toNat = liB d v.toNat 8 := by
  have h := c_liF_liB d v.toNat (UInt64.toNat_lt v) 8 0 (by omega)
  have hv := UInt64.toNat_lt v
  have e : v.toNat * 2 ^ (8 * 0) % 2 ^ 64 = v.toNat := by omega
  rw [e] at h
  simpa [liB] using h

/-! ## the translator's accessors at `q + m`, as the view of `Cj.drop q` -/

private theorem c_s1 (p : Nat) (hp : p < 2 ^ 62) : p.toUInt64 + 1 = (p + 1).toUInt64 := tU_succ (by omega)

private theorem c_s2 (p : Nat) (hp : p < 2 ^ 62) : p.toUInt64 + 2 = (p + 2).toUInt64 := by
  apply ArmRA.u64
  rw [UInt64.toNat_add, ArmRA.toU_toNat (by omega), ArmRA.toU_toNat (by omega)]
  show (p + 2) % 2 ^ 64 = p + 2
  omega

private theorem c_e30 (v : UInt64) : e30 v = s30 v := rfl

private theorem c_byte (s : UInt64) : (s >>> 56) &&& e_6 = (s.toNat / 2 ^ 56 % 256).toUInt64 := by
  have hs := UInt64.toNat_lt s
  apply ArmRA.u64
  rw [ArmRA.toU_toNat (by omega)]
  simp only [show e_6 = 255 from rfl]
  wnorm

private theorem c_shl (s : UInt64) : (s <<< 8).toNat = s.toNat * 256 % 2 ^ 64 := by
  wnorm

private theorem c_take1 {l r : List J} {x : J} (h : l = x :: r) : l.take 1 = [x] := by rw [h]; rfl
private theorem c_take17 {l r t : List J} {x : J} (h : l = x :: r) (hp : r.take 16 = t) : l.take 17 = x :: t := by
  rw [h, List.take_succ_cons, hp]

section
variable {Cj : List J} (hJ : ∀ j ∈ Cj, JOK j) (hl : Cj.length < 2 ^ 18)
include hJ hl

private theorem c_a20 (q m : Nat) (h : q + m < 2 ^ 62) :
    e20 (Cj.map encG) (bsize (Cj.map encG)) (q + m).toUInt64 = kd (Cj.drop q) m := by
  rw [acc20 jArmBits hJ hl (q + m) (by omega), kd_drop]
private theorem c_a21 (q m : Nat) (h : q + m < 2 ^ 62) : e21 (Cj.map encG) (q + m).toUInt64 = fA (Cj.drop q) m := by
  rw [acc21 jArmBits hJ hl (q + m) (by omega), fA_drop]
private theorem c_a22 (q m : Nat) (h : q + m < 2 ^ 62) : e22 (Cj.map encG) (q + m).toUInt64 = fB (Cj.drop q) m := by
  rw [acc22 jArmBits hJ hl (q + m) (by omega), fB_drop]
private theorem c_a23 (q m : Nat) (h : q + m < 2 ^ 62) : e23 (Cj.map encG) (q + m).toUInt64 = fC (Cj.drop q) m := by
  rw [acc23 jArmBits hJ hl (q + m) (by omega), fC_drop]

private theorem c_e26 (q m : Nat) (h : q + m < 2 ^ 62) (k a b x : UInt64) :
    e26 (Cj.map encG) (bsize (Cj.map encG)) (q + m).toUInt64 k a b x = m26 (Cj.drop q) m k a b x := by
  simp only [e26, m26, e60_eq, c_a20 hJ hl q m h, c_a21 hJ hl q m h, c_a22 hJ hl q m h, c_a23 hJ hl q m h]

/-- `e31` (the value scan) is the spec's `liV` -/
private theorem c_e31 (q : Nat) : ∀ (k m : Nat) (a : UInt64), q + m + 2 * k < 2 ^ 62 →
    e31 k (Cj.map encG) (bsize (Cj.map encG)) (q + m).toUInt64 a = liV k (Cj.drop q) m a
  | 0, _, _, _ => rfl
  | k + 1, m, a, h => by
    have s1 : (q + m).toUInt64 + 1 = (q + (m + 1)).toUInt64 := c_s1 (q + m) (by omega)
    have s2 : (q + m).toUInt64 + 2 = (q + (m + 2)).toUInt64 := c_s2 (q + m) (by omega)
    have ih := fun a => c_e31 q k (m + 2) a (by omega)
    simp only [e31, liV, s1, s2, c_a20 hJ hl q m (by omega), c_a20 hJ hl q (m + 1) (by omega),
      c_a23 hJ hl q (m + 1) (by omega), c_e30, ih]

/-- `e33` (the shape check) gives the pairs -/
private theorem c_e33 (q d : Nat) (hd : d < 32) : ∀ (k m : Nat) (s : UInt64), q + m + 2 * k < 2 ^ 62 →
    e33 k (Cj.map encG) (bsize (Cj.map encG)) (q + m).toUInt64 d.toUInt64 s ≠ 0 →
    ((Cj.drop q).drop m).take (2 * k) = liF d k s.toNat
  | 0, _, _, _, _ => by simp [liF]
  | k + 1, m, s, h, h33 => by
    have s1 : (q + m).toUInt64 + 1 = (q + (m + 1)).toUInt64 := c_s1 (q + m) (by omega)
    have s2 : (q + m).toUInt64 + 2 = (q + (m + 2)).toUInt64 := c_s2 (q + m) (by omega)
    simp only [e33, s1, s2, c_e26 hJ hl q m (by omega), c_e26 hJ hl q (m + 1) (by omega)] at h33
    have hJ' : ∀ j ∈ Cj.drop q, JOK j := fun j hj => hJ j (List.mem_of_mem_drop hj)
    split at h33
    · rename_i hc
      obtain ⟨c1, c2⟩ := c_mul_one hc
      obtain ⟨k1, a1, b1, x1⟩ := c_m26 c1
      obtain ⟨k2, a2, b2, x2⟩ := c_m26 c2
      rw [c_byte] at x2
      have hs := UInt64.toNat_lt s
      have g1 := c_view_slli hJ' k1 a1 b1 x1 hd hd
      have g2 := c_view_addi hJ' k2 a2 b2 x2 hd hd (by omega)
      have ih := c_e33 q d hd k (m + 2) (s <<< 8) (by omega) h33
      rw [c_shl] at ih
      rw [c_drop_cons g1, c_drop_cons g2, show 2 * (k + 1) = 2 * k + 1 + 1 by omega, List.take_succ_cons,
        List.take_succ_cons, ih, liF]
    · exact absurd rfl h33

/-- the atom, for a destination `d` among t0 / t1 / t2 -/
private theorem c_core (q : Nat) (hq : q < Cj.length) (d : Nat) (hd : d = 5 ∨ d = 6 ∨ d = 7)
    (hA : fA (Cj.drop q) 0 = d.toUInt64)
    (h34 : e34 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 d.toUInt64
      (e32 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64) ≠ 0) :
    ∃ T : NTm, mkAtom 1 (Cj.drop q) = some T ∧ (Cj.drop q).take T.j.length = T.j ∧ T.ok = true ∧
      T.kills 5 = false ∧ T.kills 6 = false ∧ T.alen ≤ 4 ∧
      e36 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 1 = T.j.length.toUInt64 ∧
      (∀ p ∈ T.tg q, p < 2 ^ 62 ∧ e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 1 = p.toUInt64) ∧
      ∀ (z o : Buf),
        e40 (Cj.map encG) (bsize (Cj.map encG)) z o q.toUInt64 1 = o ++ (T.a (zpi z) q o.length).map Nat.toUInt64 := by
  have hJ' : ∀ j ∈ Cj.drop q, JOK j := fun j hj => hJ j (List.mem_of_mem_drop hj)
  have hd32 : d < 32 := by omega
  have h32 : e32 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 = liV 8 (Cj.drop q) 1 0 := by
    unfold e32
    rw [c_s1 q (by omega)]
    exact c_e31 hJ hl q 8 1 0 (by omega)
  have a0 : e21 (Cj.map encG) q.toUInt64 = fA (Cj.drop q) 0 := c_a21 hJ hl q 0 (by omega)
  have e0 : ∀ k a b x, e26 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 k a b x = m26 (Cj.drop q) 0 k a b x :=
    c_e26 hJ hl q 0 (by omega)
  rw [h32] at h34
  -- the J list
  have hlist : ∃ n imm, (Cj.drop q)[0]? = some (.addi d n imm) ∧
      (Cj.drop q).take (liT d (liV 8 (Cj.drop q) 1 0)).length = liT d (liV 8 (Cj.drop q) 1 0) := by
    unfold e34 at h34
    by_cases hv : liV 8 (Cj.drop q) 1 0 < 2048
    · rw [if_pos hv, e0] at h34
      obtain ⟨k1, a1, b1, x1⟩ := c_m26 h34
      have hv' : (liV 8 (Cj.drop q) 1 0).toNat < 2048 := UInt64.lt_iff_toNat_lt.1 hv
      rw [← c_toU_self (liV 8 (Cj.drop q) 1 0)] at x1
      have g := c_view_addi hJ' (n := 0) k1 a1 b1 x1 hd32 (by omega) hv'
      refine ⟨_, _, g, ?_⟩
      have hc := c_drop_cons g
      rw [List.drop_zero] at hc
      rw [liT, if_pos hv']
      exact c_take1 hc
    · rw [if_neg hv] at h34
      obtain ⟨c1, c2⟩ := c_mul_ne h34
      rw [e0] at c1
      obtain ⟨k1, a1, b1, x1⟩ := c_m26 c1
      have hv' : ¬ (liV 8 (Cj.drop q) 1 0).toNat < 2048 := fun h => hv (UInt64.lt_iff_toNat_lt.2 h)
      have g := c_view_addi hJ' (n := 0) (c := 0) k1 a1 b1 x1 hd32 (by omega) (by omega)
      refine ⟨_, _, g, ?_⟩
      have hc := c_drop_cons g
      rw [List.drop_zero] at hc
      rw [c_s1 q (by omega)] at c2
      have hp := c_e33 hJ hl q d hd32 8 1 _ (by omega) c2
      rw [c_liF8] at hp
      rw [liT_len_big d _ hv', liT, if_neg hv']
      exact c_take17 hc hp
  obtain ⟨n, imm, g, htake⟩ := hlist
  refine ⟨.li d (liV 8 (Cj.drop q) 1 0), c_mkAtom g, htake, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rcases hd with rfl | rfl | rfl <;> rfl
  · exact (liL_length _ (UInt64.toNat_lt _)).2
  · unfold e36
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    rw [h32]
    show _ = (liT d (liV 8 (Cj.drop q) 1 0)).length.toUInt64
    by_cases hv : liV 8 (Cj.drop q) 1 0 < 2048
    · rw [if_pos hv, liT_len_small d _ (UInt64.lt_iff_toNat_lt.1 hv)]; rfl
    · rw [if_neg hv, liT_len_big d _ (fun h => hv (UInt64.lt_iff_toNat_lt.2 h))]; rfl
  · intro p hp
    simp [NTm.tg] at hp
  · intro z o
    have hreg : e42 d.toUInt64 = (armReg d).toUInt64 :=
      jArmBits.l4_reg d (by rcases hd with rfl | rfl | rfl <;> rfl)
    have hr32 : armReg d < 32 := by rcases hd with rfl | rfl | rfl <;> decide
    unfold e40
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    rw [a0, hA, hreg, h32]
    exact jArmBits.l4_li o (armReg d) _ hr32

end

/-- **the `li` atom** (code 1) -/
theorem stepAt_1 : StepAt 1 := by
  intro Cj hJ hl q hq _ h37
  have a0 : e21 (Cj.map encG) q.toUInt64 = fA (Cj.drop q) 0 := c_a21 hJ hl q 0 (by omega)
  unfold e37 at h37
  simp only [show ((1 : UInt64) == 1) = true from rfl, if_true] at h37
  rw [a0] at h37
  by_cases h5 : (fA (Cj.drop q) 0 == 5) = true
  · rw [if_pos h5] at h37
    have hA : fA (Cj.drop q) 0 = (5 : Nat).toUInt64 := eq_of_beq h5
    rw [hA] at h37
    exact c_core hJ hl q hq 5 (by omega) hA h37
  · rw [if_neg h5] at h37
    by_cases h6 : (fA (Cj.drop q) 0 == 6) = true
    · rw [if_pos h6] at h37
      have hA : fA (Cj.drop q) 0 = (6 : Nat).toUInt64 := eq_of_beq h6
      rw [hA] at h37
      exact c_core hJ hl q hq 6 (by omega) hA h37
    · rw [if_neg h6] at h37
      by_cases h7 : (fA (Cj.drop q) 0 == 7) = true
      · rw [if_pos h7] at h37
        have hA : fA (Cj.drop q) 0 = (7 : Nat).toUInt64 := eq_of_beq h7
        rw [hA] at h37
        exact c_core hJ hl q hq 7 (by omega) hA h37
      · rw [if_neg h7] at h37
        exact absurd rfl h37

end JT
