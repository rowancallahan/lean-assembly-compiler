/- `StepAt` lemmas, group B (see JArmStep.lean). -/
import Nano.Run.JArmStep
import Nano.Run.JArmInst
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-! ## helpers (private) -/

private theorem bIuN (z : Int) : (iu z).toNat = (z % 2 ^ 64).toNat := by
  unfold iu
  simp
  omega

private theorem bIuInj {z : Int} {k : Nat} (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) (hk : k < 2 ^ 63)
    (h : iu z = k.toUInt64) : z = k := by
  have e := congrArg UInt64.toNat h
  rw [bIuN, ArmRA.toU_toNat (by omega)] at e
  omega

private theorem bTUInj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a.toUInt64 = b.toUInt64) : a = b := by
  have e := congrArg UInt64.toNat h
  rw [ArmRA.toU_toNat ha, ArmRA.toU_toNat hb] at e
  exact e

/-- `g - (h + 1)` as the two's complement of the integer difference -/
private theorem bSub1 (g : UInt64) (n : Nat) :
    g - (n.toUInt64 + 1) = iu ((g.toNat : Int) - ((n : Int) + 1)) := by
  apply ArmRA.u64
  unfold iu
  rw [UInt64.toNat_sub, UInt64.toNat_add]
  simp
  omega

private theorem bSub0 (g : UInt64) (n : Nat) : g - n.toUInt64 = iu ((g.toNat : Int) - (n : Int)) := by
  apply ArmRA.u64
  unfold iu
  rw [UInt64.toNat_sub]
  simp
  omega

/-- the jump target: `e66` of the raw sum is `NTm.jt` -/
private theorem bE66 (n : Nat) (off : Int) (hn : n < 2 ^ 61) (h1 : -2 ^ 61 ≤ off) (h2 : off < 2 ^ 61) :
    e66 (n.toUInt64 + iu off) = (NTm.jt n off).toUInt64 ∧ NTm.jt n off < 2 ^ 62 := by
  have key : (n.toUInt64 + iu off).toNat = (((n : Int) + off) % 2 ^ 64).toNat := by
    rw [UInt64.toNat_add, ArmRA.toU_toNat (by omega), bIuN]
    omega
  unfold NTm.jt
  refine ⟨?_, by omega⟩
  unfold e66 e14
  by_cases hneg : (n : Int) + off < 0
  · have hlt : (9223372036854775807 : UInt64) < n.toUInt64 + iu off := by
      rw [UInt64.lt_iff_toNat_lt, key]
      show 9223372036854775807 < _
      omega
    rw [if_pos hlt]
    have : ((n : Int) + off).toNat = 0 := by omega
    rw [this]
    rfl
  · have hlt : ¬ (9223372036854775807 : UInt64) < n.toUInt64 + iu off := by
      rw [UInt64.lt_iff_toNat_lt, key]
      show ¬ 9223372036854775807 < _
      omega
    rw [if_neg hlt]
    apply ArmRA.u64
    show (n.toUInt64 + iu off).toNat = _
    rw [key, ArmRA.toU_toNat (by omega)]
    omega

private theorem bJtS (q : Nat) (off : Int) : NTm.jt q (1 + off) = NTm.jt (q + 1) off := by
  unfold NTm.jt
  congr 1
  omega

private theorem bE39 (r : Nat) (hr : r < 32) : e39 r.toUInt64 = if NTm.mr r = true then 1 else 0 := by
  have hb : (r.toUInt64 == 0) = decide (r = 0) := ArmRA.beq_u 0 (by omega) (by omega)
  unfold e39 NTm.mr
  rw [hb, jArmBits.l4_mapped r hr]
  by_cases h0 : r = 0 <;> cases hm : mapped r <;> simp [h0]

private theorem bMr {r : Nat} (h : NTm.mr r = true) : mapped r = true := by
  unfold NTm.mr at h
  simp at h
  exact h.1

private theorem bReg {r : Nat} (h : NTm.mr r = true) : e42 r.toUInt64 = (armReg r).toUInt64 :=
  jArmBits.l4_reg r (bMr h)

private theorem bMul2 {a b : Bool} (h : (if a = true then (1 : UInt64) else 0) * (if b = true then 1 else 0) ≠ 0) :
    a = true ∧ b = true := by
  revert a b; decide

private theorem bMul3 {a b c : Bool}
    (h : (if a = true then (1 : UInt64) else 0) * (if b = true then 1 else 0) * (if c = true then 1 else 0) ≠ 0) :
    a = true ∧ b = true ∧ c = true := by
  revert a b c; decide

private theorem bMul1 {a : Bool} (h : (if a = true then (1 : UInt64) else 0) ≠ 0) : a = true := by
  revert a; decide

private theorem bp2 (o : Buf) (a b : UInt64) : bpush (bpush o a) b = o ++ [a, b] := by
  show (o ++ [a]) ++ [b] = _
  rw [List.append_assoc]; rfl

private theorem bp3 (o : Buf) (a b c : UInt64) : bpush (bpush (bpush o a) b) c = o ++ [a, b, c] := by
  show ((o ++ [a]) ++ [b]) ++ [c] = _
  rw [List.append_assoc, List.append_assoc]; rfl

/-! ### words -/

private theorem bSubs (a b : Nat) (ha : a < 32) (hb : b < 32) :
    e51 3942645760 16 a.toUInt64 b.toUInt64 = (subsR a b).toUInt64 :=
  jArmBits.l4_e51 3942645760 16 a b (by omega) (by omega) (by omega) (by omega) ha hb

private theorem bBc (c : Nat) (hc : c < 16) (g : UInt64) (o : Buf) :
    e53 (1409286144 + c).toUInt64 (g - (bsize o + 1)) = (bc c ((g.toNat : Int) - ((o.length : Int) + 1))).toUInt64 := by
  show e53 _ (g - (o.length.toUInt64 + 1)) = _
  rw [bSub1, jArmBits.l4_e53 _ _ (by omega) (by omega)]
  unfold bc
  congr 1
  omega

private theorem bCbz (r : Nat) (hr : r < 32) (g : UInt64) (o : Buf) :
    e53 3019898880 (g - bsize o) ||| r.toUInt64 = (cbz r ((g.toNat : Int) - (o.length : Int))).toUInt64 := by
  show e53 _ (g - o.length.toUInt64) ||| _ = _
  rw [bSub0]
  exact jArmBits.l4_cb 3019898880 r _ (by omega) (by omega) hr

private theorem bCbnz (r : Nat) (hr : r < 32) (g : UInt64) (o : Buf) :
    e53 3036676096 (g - bsize o) ||| r.toUInt64 = (cbnz r ((g.toNat : Int) - (o.length : Int))).toUInt64 := by
  show e53 _ (g - o.length.toUInt64) ||| _ = _
  rw [bSub0]
  exact jArmBits.l4_cb 3036676096 r _ (by omega) (by omega) hr

/-! ### the instructions at `q`, `q + 1` -/

private theorem bSu0 {Cj : List J} (hJ : ∀ j ∈ Cj, JOK j) (hl : Cj.length < 2 ^ 18) (q : Nat) (hq : q < Cj.length) :
    ∃ j0, Cj.drop q = j0 :: Cj.drop (q + 1) ∧ JOK j0 ∧
      e21 (Cj.map encG) q.toUInt64 = jA j0 ∧ e22 (Cj.map encG) q.toUInt64 = jB j0 ∧
      e23 (Cj.map encG) q.toUInt64 = jC j0 ∧ e24 (Cj.map encG) q.toUInt64 = jop j0 := by
  refine ⟨Cj[q], List.drop_eq_getElem_cons hq, hJ _ (List.getElem_mem hq), ?_, ?_, ?_, ?_⟩
  · rw [acc21 jArmBits hJ hl q (by omega)]; unfold fA; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc22 jArmBits hJ hl q (by omega)]; unfold fB; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc23 jArmBits hJ hl q (by omega)]; unfold fC; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc24 jArmBits hJ hl q (by omega)]; unfold fO; rw [List.getElem?_eq_getElem hq]; rfl

private theorem bSu1 {Cj : List J} (hJ : ∀ j ∈ Cj, JOK j) (hl : Cj.length < 2 ^ 18) (q : Nat) {j1 : J} {r : List J}
    (hr : Cj.drop (q + 1) = j1 :: r) :
    JOK j1 ∧ e21 (Cj.map encG) (q.toUInt64 + 1) = jA j1 ∧ e22 (Cj.map encG) (q.toUInt64 + 1) = jB j1 ∧
      e23 (Cj.map encG) (q.toUInt64 + 1) = jC j1 ∧ e24 (Cj.map encG) (q.toUInt64 + 1) = jop j1 := by
  have hq : q + 1 < Cj.length := by
    have := congrArg List.length hr
    rw [List.length_drop, List.length_cons] at this
    omega
  have hg : Cj[q + 1] = j1 := by
    have := List.drop_eq_getElem_cons hq
    rw [hr] at this
    exact (List.cons.inj this).1.symm
  rw [tU_succ (by omega)]
  subst hg
  refine ⟨hJ _ (List.getElem_mem hq), ?_, ?_, ?_, ?_⟩
  · rw [acc21 jArmBits hJ hl _ (by omega)]; unfold fA; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc22 jArmBits hJ hl _ (by omega)]; unfold fB; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc23 jArmBits hJ hl _ (by omega)]; unfold fC; rw [List.getElem?_eq_getElem hq]; rfl
  · rw [acc24 jArmBits hJ hl _ (by omega)]; unfold fO; rw [List.getElem?_eq_getElem hq]; rfl

/-- the head has the wrong kind for the code in `h` -/
local macro "bNo" h:ident : tactic =>
  `(tactic| (simp [candC, kd, jk, m29, m26, m28] at $h:ident <;> (repeat' split at $h:ident) <;>
      exact absurd $h (by decide)))

/-! ### inversion of `candC` (on abstract field values) -/

private theorem bCbeq11 {a m b : UInt64}
    (h : (if a == 2 then (if m == 1 then (if b == 0 then (11 : UInt64) else 10) else (if b == 0 then 13 else 0))
      else (if b == 0 then 13 else 0)) = 11) : a = 2 ∧ m = 1 ∧ b = 0 := by
  by_cases ha : a = 2 <;> by_cases hm : m = 1 <;> by_cases hb : b = 0 <;> simp_all

private theorem bCbeq10 {a m b : UInt64}
    (h : (if a == 2 then (if m == 1 then (if b == 0 then (11 : UInt64) else 10) else (if b == 0 then 13 else 0))
      else (if b == 0 then 13 else 0)) = 10) : a = 2 ∧ m = 1 := by
  by_cases ha : a = 2 <;> by_cases hm : m = 1 <;> by_cases hb : b = 0 <;> simp_all

private theorem bCbeq13 {a m b : UInt64}
    (h : (if a == 2 then (if m == 1 then (if b == 0 then (11 : UInt64) else 10) else (if b == 0 then 13 else 0))
      else (if b == 0 then 13 else 0)) = 13) : b = 0 := by
  by_cases ha : a = 2 <;> by_cases hm : m = 1 <;> by_cases hb : b = 0 <;> simp_all

private theorem bC8 {a m : UInt64} (h : (if a == 2 then (if m == 1 then (8 : UInt64) else 12) else 12) = 8) :
    a = 2 ∧ m = 1 := by
  by_cases ha : a = 2 <;> by_cases hm : m = 1 <;> simp_all

private theorem bC9 {a m : UInt64} (h : (if a == 2 then (if m == 1 then (9 : UInt64) else 0) else 0) = 9) :
    a = 2 ∧ m = 1 := by
  by_cases ha : a = 2 <;> by_cases hm : m = 1 <;> simp_all

private theorem bC14 {b : UInt64} (h : (if b == 0 then (14 : UInt64) else 0) = 14) : b = 0 := by
  by_cases hb : b = 0 <;> simp_all

private theorem bC6 {c0 c1 P : UInt64}
    (h : (if c0 == 0 then (if c1 == 8 then (if P == 1 then (6 : UInt64) else 4) else 4)
      else if c0 == 8 then (if c1 == 0 then (if P == 1 then 7 else 4) else 4) else 4) = 6) :
    c0 = 0 ∧ c1 = 8 ∧ P = 1 := by
  by_cases h0 : c0 = 0 <;> by_cases h8 : c0 = 8 <;> by_cases h1 : c1 = 8 <;> by_cases h2 : c1 = 0 <;>
    by_cases hP : P = 1 <;> simp_all

private theorem bC7 {c0 c1 P : UInt64}
    (h : (if c0 == 0 then (if c1 == 8 then (if P == 1 then (6 : UInt64) else 4) else 4)
      else if c0 == 8 then (if c1 == 0 then (if P == 1 then 7 else 4) else 4) else 4) = 7) :
    c0 = 8 ∧ c1 = 0 ∧ P = 1 := by
  by_cases h0 : c0 = 0 <;> by_cases h8 : c0 = 8 <;> by_cases h1 : c1 = 8 <;> by_cases h2 : c1 = 0 <;>
    by_cases hP : P = 1 <;> simp_all

private theorem bC15 {o c1 P : UInt64}
    (h : (if o == 1 then (if c1 == 0 then (if P == 1 then (15 : UInt64) else 3) else 3) else 3) = 15) :
    o = 1 ∧ c1 = 0 ∧ P = 1 := by
  by_cases h0 : o = 1 <;> by_cases h1 : c1 = 0 <;> by_cases hP : P = 1 <;> simp_all

private theorem bC18 {P : UInt64} (h : (if P == 1 then (18 : UInt64) else 16) = 18) : P = 1 := by
  by_cases hP : P = 1 <;> simp_all

private theorem bC19 {c0 c1 P : UInt64}
    (h : (if c0 == 3 then (if c1 == 3 then (if P == 1 then (19 : UInt64) else 0) else 0) else 0) = 19) :
    c0 = 3 ∧ c1 = 3 ∧ P = 1 := by
  by_cases h0 : c0 = 3 <;> by_cases h1 : c1 = 3 <;> by_cases hP : P = 1 <;> simp_all

private theorem bEqb1 {a b : UInt64} (h : eqb a b = 1) : a = b := by
  unfold eqb at h
  by_cases hab : a = b
  · exact hab
  · simp [hab] at h

private theorem bEqbL {a b v : UInt64} (h : eqb a b * v = 1) : a = b ∧ v = 1 := by
  unfold eqb at h
  by_cases hab : a = b
  · simp [hab] at h; exact ⟨hab, h⟩
  · simp [hab] at h

private theorem bEqbR {a b v : UInt64} (h : v * eqb a b = 1) : v = 1 ∧ a = b := by
  unfold eqb at h
  by_cases hab : a = b
  · simp [hab] at h; exact ⟨h, hab⟩
  · simp [hab] at h

private theorem bNebR {a b v : UInt64} (h : v * neb a b = 1) : v = 1 ∧ a ≠ b := by
  unfold neb at h
  by_cases hab : a = b
  · simp [hab] at h
  · simp [hab] at h; exact ⟨h, hab⟩

/-- instruction 1 is `jal 0 _` -/
private theorem bM29 (j0 : J) (r : List J) (h : m29 (j0 :: r) = 1) :
    ∃ rd o r', r = .jal rd o :: r' ∧ rd.toUInt64 = 0 := by
  cases r with
  | nil => exact absurd (show (0 : UInt64) = 1 from h) (by decide)
  | cons j1 r' =>
    cases j1 with
    | jal rd o => exact ⟨rd, o, r', rfl, bEqb1 h⟩
    | _ => exact absurd (show (0 : UInt64) = 1 from h) (by decide)

/-- the target of a compare over `jal 0 o` at `q + 1` -/
private theorem bTg1 {Cj : List J} (hJ : ∀ j ∈ Cj, JOK j) (hl : Cj.length < 2 ^ 18) (q : Nat) (hq : q < Cj.length)
    {rd : Nat} {o : Int} {r : List J} (hr : Cj.drop (q + 1) = .jal rd o :: r) :
    e66 (q.toUInt64 + 1 + e23 (Cj.map encG) (q.toUInt64 + 1)) = (NTm.jt q (1 + o)).toUInt64 ∧
      NTm.jt q (1 + o) < 2 ^ 62 := by
  obtain ⟨⟨-, ho⟩, -, -, c1, -⟩ := bSu1 hJ hl q hr
  obtain ⟨h1, h2⟩ := ho rd o rfl
  have c1 : e23 (Cj.map encG) (q.toUInt64 + 1) = iu o := c1
  rw [c1, tU_succ (by omega), bJtS]
  exact bE66 (q + 1) o (by omega) (by omega) (by omega)

private theorem bLdp (t u n : Nat) (ht : t < 32) (hu : u < 32) (hn : n < 32) :
    e50 2839543808 t.toUInt64 n.toUInt64 u.toUInt64 = (ldp t u n).toUInt64 :=
  jArmBits.l4_e50 2839543808 t n u (by omega) (by omega) ht hn (by omega)

/-! ## 12: `bgeu` -/

theorem stepAt_12 : StepAt 12 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | bgeu x y off =>
    obtain ⟨⟨hx, hy, ho⟩, -⟩ := ok0
    have a0 : e21 (Cj.map encG) q.toUInt64 = x.toUInt64 := A0
    have b0 : e22 (Cj.map encG) q.toUInt64 = y.toUInt64 := B0
    have c0 : e23 (Cj.map encG) q.toUInt64 = iu off := C0
    have he' : e39 (e21 (Cj.map encG) q.toUInt64) * e39 (e22 (Cj.map encG) q.toUInt64) ≠ 0 := he
    rw [a0, b0, bE39 x hx, bE39 y hy] at he'
    obtain ⟨mx, my⟩ := bMul2 he'
    obtain ⟨t1, t2⟩ := bE66 q off (by omega) (by omega) (by omega)
    have hE : e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 12 = (NTm.jt q off).toUInt64 := by
      show e66 (q.toUInt64 + e23 (Cj.map encG) q.toUInt64) = _
      rw [c0]; exact t1
    refine ⟨.bgeu x y off, rfl, rfl, ?_, rfl, rfl, (by show 2 ≤ 4; omega), rfl, ?_, ?_⟩
    · show (NTm.mr x && NTm.mr y) = true
      rw [mx, my]; rfl
    · intro p hp
      have hp' : p = NTm.jt q off := List.mem_singleton.1 hp
      subst hp'
      exact ⟨t2, hE⟩
    · intro z o
      have w2 : e53 1409286146 (e59 z (NTm.jt q off).toUInt64 - (bsize o + 1))
          = (bc 2 ((zpi z (NTm.jt q off) : Int) - ((o.length : Int) + 1))).toUInt64 := bBc 2 (by omega) _ o
      show bpush (bpush o (e51 3942645760 16 (e42 (e21 (Cj.map encG) q.toUInt64)) (e42 (e22 (Cj.map encG) q.toUInt64))))
          (e53 1409286146 (e59 z (e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 12) - (bsize o + 1)))
        = o ++ [(subsR (armReg x) (armReg y)).toUInt64,
            (bc 2 ((zpi z (NTm.jt q off) : Int) - ((o.length : Int) + 1))).toUInt64]
      rw [a0, b0, bReg mx, bReg my, hE, bSubs _ _ (ArmRA.armReg_lt x) (ArmRA.armReg_lt y), w2, bp2]
  | _ => bNo hc

/-! ## 13: `beqz` -/

theorem stepAt_13 : StepAt 13 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | beq x y off =>
    obtain ⟨⟨hx, hy, ho⟩, -⟩ := ok0
    have a0 : e21 (Cj.map encG) q.toUInt64 = x.toUInt64 := A0
    have c0 : e23 (Cj.map encG) q.toUInt64 = iu off := C0
    have hy0 : y.toUInt64 = 0 := bCbeq13 (a := iu off) (m := m29 (.beq x y off :: r)) hc
    have hy0 : y = 0 := bTUInj (b := 0) (by omega) (by omega) hy0
    subst hy0
    have he' : e39 (e21 (Cj.map encG) q.toUInt64) ≠ 0 := he
    rw [a0, bE39 x hx] at he'
    have mx := bMul1 he'
    obtain ⟨t1, t2⟩ := bE66 q off (by omega) (by omega) (by omega)
    have hE : e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 13 = (NTm.jt q off).toUInt64 := by
      show e66 (q.toUInt64 + e23 (Cj.map encG) q.toUInt64) = _
      rw [c0]; exact t1
    refine ⟨.beqz x off, rfl, rfl, mx, rfl, rfl, (by show 1 ≤ 4; omega), rfl, ?_, ?_⟩
    · intro p hp
      have hp' : p = NTm.jt q off := List.mem_singleton.1 hp
      subst hp'
      exact ⟨t2, hE⟩
    · intro z o
      have w2 : e53 3019898880 (e59 z (NTm.jt q off).toUInt64 - bsize o) ||| (armReg x).toUInt64
          = (cbz (armReg x) ((zpi z (NTm.jt q off) : Int) - (o.length : Int))).toUInt64 :=
        bCbz _ (ArmRA.armReg_lt x) _ o
      show bpush o (e53 3019898880 (e59 z (e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 13) - bsize o)
            ||| e42 (e21 (Cj.map encG) q.toUInt64))
        = o ++ [(cbz (armReg x) ((zpi z (NTm.jt q off) : Int) - (o.length : Int))).toUInt64]
      rw [a0, bReg mx, hE, w2]; rfl
  | _ => bNo hc

/-! ## 14: `bnez` -/

theorem stepAt_14 : StepAt 14 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | bne x y off =>
    obtain ⟨⟨hx, hy, ho⟩, -⟩ := ok0
    have a0 : e21 (Cj.map encG) q.toUInt64 = x.toUInt64 := A0
    have c0 : e23 (Cj.map encG) q.toUInt64 = iu off := C0
    have hy0 : y.toUInt64 = 0 := bC14 hc
    have hy0 : y = 0 := bTUInj (b := 0) (by omega) (by omega) hy0
    subst hy0
    have he' : e39 (e21 (Cj.map encG) q.toUInt64) ≠ 0 := he
    rw [a0, bE39 x hx] at he'
    have mx := bMul1 he'
    obtain ⟨t1, t2⟩ := bE66 q off (by omega) (by omega) (by omega)
    have hE : e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 14 = (NTm.jt q off).toUInt64 := by
      show e66 (q.toUInt64 + e23 (Cj.map encG) q.toUInt64) = _
      rw [c0]; exact t1
    refine ⟨.bnez x off, rfl, rfl, mx, rfl, rfl, (by show 1 ≤ 4; omega), rfl, ?_, ?_⟩
    · intro p hp
      have hp' : p = NTm.jt q off := List.mem_singleton.1 hp
      subst hp'
      exact ⟨t2, hE⟩
    · intro z o
      have w2 : e53 3036676096 (e59 z (NTm.jt q off).toUInt64 - bsize o) ||| (armReg x).toUInt64
          = (cbnz (armReg x) ((zpi z (NTm.jt q off) : Int) - (o.length : Int))).toUInt64 :=
        bCbnz _ (ArmRA.armReg_lt x) _ o
      show bpush o (e53 3036676096 (e59 z (e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 14) - bsize o)
            ||| e42 (e21 (Cj.map encG) q.toUInt64))
        = o ++ [(cbnz (armReg x) ((zpi z (NTm.jt q off) : Int) - (o.length : Int))).toUInt64]
      rw [a0, bReg mx, hE, w2]; rfl
  | _ => bNo hc

/-! ## 8: `cj .geu` -/

theorem stepAt_8 : StepAt 8 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | bgeu x y off =>
    obtain ⟨⟨hx, hy, ho⟩, -⟩ := ok0
    have a0 : e21 (Cj.map encG) q.toUInt64 = x.toUInt64 := A0
    have b0 : e22 (Cj.map encG) q.toUInt64 = y.toUInt64 := B0
    obtain ⟨ha, hm⟩ := bC8 (a := iu off) (m := m29 (.bgeu x y off :: r)) hc
    have ho2 : off = 2 := by
      have := bIuInj (k := 2) (by omega) (by omega) (by omega) ha
      omega
    subst ho2
    obtain ⟨rd, o, r', rfl, hrd⟩ := bM29 _ _ hm
    obtain ⟨⟨hrd32, -⟩, -⟩ := bSu1 hJ hl q hr
    have hrd32 : rd < 32 := hrd32
    have hrd0 : rd = 0 := bTUInj (b := 0) (by omega) (by omega) hrd
    subst hrd0
    have he' : e39 (e21 (Cj.map encG) q.toUInt64) * e39 (e22 (Cj.map encG) q.toUInt64) ≠ 0 := he
    rw [a0, b0, bE39 x hx, bE39 y hy] at he'
    obtain ⟨mx, my⟩ := bMul2 he'
    obtain ⟨t1, t2⟩ := bTg1 hJ hl q hq hr
    have hE : e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 8 = (NTm.jt q (1 + o)).toUInt64 := t1
    refine ⟨.cj .geu x y o, rfl, rfl, ?_, rfl, rfl, (by show 2 ≤ 4; omega), rfl, ?_, ?_⟩
    · show (NTm.mr x && NTm.mr y) = true
      rw [mx, my]; rfl
    · intro p hp
      have hp' : p = NTm.jt q (1 + o) := List.mem_singleton.1 hp
      subst hp'
      exact ⟨t2, hE⟩
    · intro z o'
      have w2 : e53 1409286147 (e59 z (NTm.jt q (1 + o)).toUInt64 - (bsize o' + 1))
          = (bc 3 ((zpi z (NTm.jt q (1 + o)) : Int) - ((o'.length : Int) + 1))).toUInt64 := bBc 3 (by omega) _ o'
      show bpush (bpush o' (e51 3942645760 16 (e42 (e21 (Cj.map encG) q.toUInt64)) (e42 (e22 (Cj.map encG) q.toUInt64))))
          (e53 1409286147 (e59 z (e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 8) - (bsize o' + 1)))
        = o' ++ [(subsR (armReg x) (armReg y)).toUInt64,
            (bc 3 ((zpi z (NTm.jt q (1 + o)) : Int) - ((o'.length : Int) + 1))).toUInt64]
      rw [a0, b0, bReg mx, bReg my, hE, bSubs _ _ (ArmRA.armReg_lt x) (ArmRA.armReg_lt y), w2, bp2]
  | _ => bNo hc

/-! ## 9: `cj .ltu` -/

theorem stepAt_9 : StepAt 9 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | bltu x y off =>
    obtain ⟨⟨hx, hy, ho⟩, -⟩ := ok0
    have a0 : e21 (Cj.map encG) q.toUInt64 = x.toUInt64 := A0
    have b0 : e22 (Cj.map encG) q.toUInt64 = y.toUInt64 := B0
    obtain ⟨ha, hm⟩ := bC9 (a := iu off) (m := m29 (.bltu x y off :: r)) hc
    have ho2 : off = 2 := by
      have := bIuInj (k := 2) (by omega) (by omega) (by omega) ha
      omega
    subst ho2
    obtain ⟨rd, o, r', rfl, hrd⟩ := bM29 _ _ hm
    obtain ⟨⟨hrd32, -⟩, -⟩ := bSu1 hJ hl q hr
    have hrd32 : rd < 32 := hrd32
    have hrd0 : rd = 0 := bTUInj (b := 0) (by omega) (by omega) hrd
    subst hrd0
    have he' : e39 (e21 (Cj.map encG) q.toUInt64) * e39 (e22 (Cj.map encG) q.toUInt64) ≠ 0 := he
    rw [a0, b0, bE39 x hx, bE39 y hy] at he'
    obtain ⟨mx, my⟩ := bMul2 he'
    obtain ⟨t1, t2⟩ := bTg1 hJ hl q hq hr
    have hE : e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 9 = (NTm.jt q (1 + o)).toUInt64 := t1
    refine ⟨.cj .ltu x y o, rfl, rfl, ?_, rfl, rfl, (by show 2 ≤ 4; omega), rfl, ?_, ?_⟩
    · show (NTm.mr x && NTm.mr y) = true
      rw [mx, my]; rfl
    · intro p hp
      have hp' : p = NTm.jt q (1 + o) := List.mem_singleton.1 hp
      subst hp'
      exact ⟨t2, hE⟩
    · intro z o'
      have w2 : e53 1409286146 (e59 z (NTm.jt q (1 + o)).toUInt64 - (bsize o' + 1))
          = (bc 2 ((zpi z (NTm.jt q (1 + o)) : Int) - ((o'.length : Int) + 1))).toUInt64 := bBc 2 (by omega) _ o'
      show bpush (bpush o' (e51 3942645760 16 (e42 (e21 (Cj.map encG) q.toUInt64)) (e42 (e22 (Cj.map encG) q.toUInt64))))
          (e53 1409286146 (e59 z (e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 9) - (bsize o' + 1)))
        = o' ++ [(subsR (armReg x) (armReg y)).toUInt64,
            (bc 2 ((zpi z (NTm.jt q (1 + o)) : Int) - ((o'.length : Int) + 1))).toUInt64]
      rw [a0, b0, bReg mx, bReg my, hE, bSubs _ _ (ArmRA.armReg_lt x) (ArmRA.armReg_lt y), w2, bp2]
  | _ => bNo hc

/-! ## 10: `cj .eq` -/

theorem stepAt_10 : StepAt 10 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | beq x y off =>
    obtain ⟨⟨hx, hy, ho⟩, -⟩ := ok0
    have a0 : e21 (Cj.map encG) q.toUInt64 = x.toUInt64 := A0
    have b0 : e22 (Cj.map encG) q.toUInt64 = y.toUInt64 := B0
    obtain ⟨ha, hm⟩ := bCbeq10 (a := iu off) (m := m29 (.beq x y off :: r)) (b := y.toUInt64) hc
    have ho2 : off = 2 := by
      have := bIuInj (k := 2) (by omega) (by omega) (by omega) ha
      omega
    subst ho2
    obtain ⟨rd, o, r', rfl, hrd⟩ := bM29 _ _ hm
    obtain ⟨⟨hrd32, -⟩, -⟩ := bSu1 hJ hl q hr
    have hrd32 : rd < 32 := hrd32
    have hrd0 : rd = 0 := bTUInj (b := 0) (by omega) (by omega) hrd
    subst hrd0
    have he' : e39 (e21 (Cj.map encG) q.toUInt64) * e39 (e22 (Cj.map encG) q.toUInt64) ≠ 0 := he
    rw [a0, b0, bE39 x hx, bE39 y hy] at he'
    obtain ⟨mx, my⟩ := bMul2 he'
    obtain ⟨t1, t2⟩ := bTg1 hJ hl q hq hr
    have hE : e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 10 = (NTm.jt q (1 + o)).toUInt64 := t1
    refine ⟨.cj .eq x y o, rfl, rfl, ?_, rfl, rfl, (by show 2 ≤ 4; omega), rfl, ?_, ?_⟩
    · show (NTm.mr x && NTm.mr y) = true
      rw [mx, my]; rfl
    · intro p hp
      have hp' : p = NTm.jt q (1 + o) := List.mem_singleton.1 hp
      subst hp'
      exact ⟨t2, hE⟩
    · intro z o'
      have w2 : e53 1409286145 (e59 z (NTm.jt q (1 + o)).toUInt64 - (bsize o' + 1))
          = (bc 1 ((zpi z (NTm.jt q (1 + o)) : Int) - ((o'.length : Int) + 1))).toUInt64 := bBc 1 (by omega) _ o'
      show bpush (bpush o' (e51 3942645760 16 (e42 (e21 (Cj.map encG) q.toUInt64)) (e42 (e22 (Cj.map encG) q.toUInt64))))
          (e53 1409286145 (e59 z (e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 10) - (bsize o' + 1)))
        = o' ++ [(subsR (armReg x) (armReg y)).toUInt64,
            (bc 1 ((zpi z (NTm.jt q (1 + o)) : Int) - ((o'.length : Int) + 1))).toUInt64]
      rw [a0, b0, bReg mx, bReg my, hE, bSubs _ _ (ArmRA.armReg_lt x) (ArmRA.armReg_lt y), w2, bp2]
  | _ => bNo hc

/-! ## 11: `lpz` -/

theorem stepAt_11 : StepAt 11 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | beq x y off =>
    obtain ⟨⟨hx, hy, ho⟩, -⟩ := ok0
    have a0 : e21 (Cj.map encG) q.toUInt64 = x.toUInt64 := A0
    obtain ⟨ha, hm, hy0⟩ := bCbeq11 (a := iu off) (m := m29 (.beq x y off :: r)) (b := y.toUInt64) hc
    have ho2 : off = 2 := by
      have := bIuInj (k := 2) (by omega) (by omega) (by omega) ha
      omega
    subst ho2
    have hy0 : y = 0 := bTUInj (b := 0) (by omega) (by omega) hy0
    subst hy0
    obtain ⟨rd, o, r', rfl, hrd⟩ := bM29 _ _ hm
    obtain ⟨⟨hrd32, -⟩, -⟩ := bSu1 hJ hl q hr
    have hrd32 : rd < 32 := hrd32
    have hrd0 : rd = 0 := bTUInj (b := 0) (by omega) (by omega) hrd
    subst hrd0
    have he' : e39 (e21 (Cj.map encG) q.toUInt64) ≠ 0 := he
    rw [a0, bE39 x hx] at he'
    have mx := bMul1 he'
    obtain ⟨t1, t2⟩ := bTg1 hJ hl q hq hr
    have hE : e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 11 = (NTm.jt q (1 + o)).toUInt64 := t1
    refine ⟨.lpz x o, rfl, rfl, mx, rfl, rfl, (by show 1 ≤ 4; omega), rfl, ?_, ?_⟩
    · intro p hp
      have hp' : p = NTm.jt q (1 + o) := List.mem_singleton.1 hp
      subst hp'
      exact ⟨t2, hE⟩
    · intro z o'
      have w2 : e53 3036676096 (e59 z (NTm.jt q (1 + o)).toUInt64 - bsize o') ||| (armReg x).toUInt64
          = (cbnz (armReg x) ((zpi z (NTm.jt q (1 + o)) : Int) - (o'.length : Int))).toUInt64 :=
        bCbnz _ (ArmRA.armReg_lt x) _ o'
      show bpush o' (e53 3036676096 (e59 z (e65 (Cj.map encG) (bsize (Cj.map encG)) q.toUInt64 11) - bsize o')
            ||| e42 (e21 (Cj.map encG) q.toUInt64))
        = o' ++ [(cbnz (armReg x) ((zpi z (NTm.jt q (1 + o)) : Int) - (o'.length : Int))).toUInt64]
      rw [a0, bReg mx, hE, w2]; rfl
  | _ => bNo hc

/-! ## 6: `ldp` -/

theorem stepAt_6 : StepAt 6 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | ld u n off0 =>
    cases r with
    | nil => bNo hc
    | cons j1 r' =>
      obtain ⟨ok1, A1, B1, C1, -⟩ := bSu1 hJ hl q hr
      cases j1 with
      | ld v n' off1 =>
        obtain ⟨⟨hu, hn, ho1, ho2⟩, -⟩ := ok0
        obtain ⟨⟨hv, hn', hp1, hp2⟩, -⟩ := ok1
        have a0 : e21 (Cj.map encG) q.toUInt64 = u.toUInt64 := A0
        have b0 : e22 (Cj.map encG) q.toUInt64 = n.toUInt64 := B0
        have a1 : e21 (Cj.map encG) (q.toUInt64 + 1) = v.toUInt64 := A1
        obtain ⟨h0, h1, hP⟩ := bC6 (c0 := iu off0) (c1 := iu off1)
          (P := eqb n.toUInt64 n'.toUInt64 * neb u.toUInt64 v.toUInt64 * neb u.toUInt64 n.toUInt64
            * neb v.toUInt64 n.toUInt64) hc
        obtain ⟨hP, hvn⟩ := bNebR hP
        obtain ⟨hP, hun⟩ := bNebR hP
        obtain ⟨hP, huv⟩ := bNebR hP
        have hnn : n = n' := bTUInj (by omega) (by omega) (bEqb1 hP)
        have e0 : off0 = 0 := by
          have := bIuInj (k := 0) (by omega) (by omega) (by omega) h0
          omega
        have e1 : off1 = 8 := by
          have := bIuInj (k := 8) (by omega) (by omega) (by omega) h1
          omega
        subst hnn e0 e1
        have huv : u ≠ v := fun h => huv (by rw [h])
        have hun : u ≠ n := fun h => hun (by rw [h])
        have hvn : v ≠ n := fun h => hvn (by rw [h])
        have he' : e39 (e21 (Cj.map encG) q.toUInt64) * e39 (e21 (Cj.map encG) (q.toUInt64 + 1))
            * e39 (e22 (Cj.map encG) q.toUInt64) ≠ 0 := he
        rw [a0, a1, b0, bE39 u hu, bE39 v hv, bE39 n hn] at he'
        obtain ⟨mu, mv, mn⟩ := bMul3 he'
        refine ⟨.ldp u v n false, rfl, rfl, ?_, rfl, rfl, (by show 1 ≤ 4; omega), rfl, ?_, ?_⟩
        · show (NTm.mr u && NTm.mr v && NTm.mr n && decide (u ≠ v ∧ u ≠ n ∧ v ≠ n)) = true
          rw [mu, mv, mn]
          exact decide_eq_true ⟨huv, hun, hvn⟩
        · intro p hp
          exact absurd hp List.not_mem_nil
        · intro z o
          show bpush o (e50 2839543808 (e42 (e21 (Cj.map encG) q.toUInt64)) (e42 (e22 (Cj.map encG) q.toUInt64))
          (e42 (e21 (Cj.map encG) (q.toUInt64 + 1))))
            = o ++ [(ldp (armReg u) (armReg v) (armReg n)).toUInt64]
          rw [a0, a1, b0, bReg mu, bReg mv, bReg mn,
            bLdp _ _ _ (ArmRA.armReg_lt _) (ArmRA.armReg_lt _) (ArmRA.armReg_lt _)]
          rfl
      | _ => bNo hc
  | _ => bNo hc

/-! ## 7: `ldp` (swapped) -/

theorem stepAt_7 : StepAt 7 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | ld u n off0 =>
    cases r with
    | nil => bNo hc
    | cons j1 r' =>
      obtain ⟨ok1, A1, B1, C1, -⟩ := bSu1 hJ hl q hr
      cases j1 with
      | ld v n' off1 =>
        obtain ⟨⟨hu, hn, ho1, ho2⟩, -⟩ := ok0
        obtain ⟨⟨hv, hn', hp1, hp2⟩, -⟩ := ok1
        have a0 : e21 (Cj.map encG) q.toUInt64 = u.toUInt64 := A0
        have b0 : e22 (Cj.map encG) q.toUInt64 = n.toUInt64 := B0
        have a1 : e21 (Cj.map encG) (q.toUInt64 + 1) = v.toUInt64 := A1
        obtain ⟨h0, h1, hP⟩ := bC7 (c0 := iu off0) (c1 := iu off1)
          (P := eqb n.toUInt64 n'.toUInt64 * neb u.toUInt64 v.toUInt64 * neb u.toUInt64 n.toUInt64
            * neb v.toUInt64 n.toUInt64) hc
        obtain ⟨hP, hvn⟩ := bNebR hP
        obtain ⟨hP, hun⟩ := bNebR hP
        obtain ⟨hP, huv⟩ := bNebR hP
        have hnn : n = n' := bTUInj (by omega) (by omega) (bEqb1 hP)
        have e0 : off0 = 8 := by
          have := bIuInj (k := 8) (by omega) (by omega) (by omega) h0
          omega
        have e1 : off1 = 0 := by
          have := bIuInj (k := 0) (by omega) (by omega) (by omega) h1
          omega
        subst hnn e0 e1
        have huv : u ≠ v := fun h => huv (by rw [h])
        have hun : u ≠ n := fun h => hun (by rw [h])
        have hvn : v ≠ n := fun h => hvn (by rw [h])
        have he' : e39 (e21 (Cj.map encG) q.toUInt64) * e39 (e21 (Cj.map encG) (q.toUInt64 + 1))
            * e39 (e22 (Cj.map encG) q.toUInt64) ≠ 0 := he
        rw [a0, a1, b0, bE39 u hu, bE39 v hv, bE39 n hn] at he'
        obtain ⟨mu, mv, mn⟩ := bMul3 he'
        refine ⟨.ldp v u n true, rfl, rfl, ?_, rfl, rfl, (by show 1 ≤ 4; omega), rfl, ?_, ?_⟩
        · show (NTm.mr v && NTm.mr u && NTm.mr n && decide (v ≠ u ∧ v ≠ n ∧ u ≠ n)) = true
          rw [mu, mv, mn]
          exact decide_eq_true ⟨fun h => huv h.symm, hvn, hun⟩
        · intro p hp
          exact absurd hp List.not_mem_nil
        · intro z o
          show bpush o (e50 2839543808 (e42 (e21 (Cj.map encG) (q.toUInt64 + 1))) (e42 (e22 (Cj.map encG) q.toUInt64))
          (e42 (e21 (Cj.map encG) q.toUInt64)))
            = o ++ [(ldp (armReg v) (armReg u) (armReg n)).toUInt64]
          rw [a0, a1, b0, bReg mu, bReg mv, bReg mn,
            bLdp _ _ _ (ArmRA.armReg_lt _) (ArmRA.armReg_lt _) (ArmRA.armReg_lt _)]
          rfl
      | _ => bNo hc
  | _ => bNo hc

/-! ## 15: `ldrbx` -/

theorem stepAt_15 : StepAt 15 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | alu op d n m =>
    cases r with
    | nil => bNo hc
    | cons j1 r' =>
      obtain ⟨ok1, A1, B1, C1, -⟩ := bSu1 hJ hl q hr
      cases j1 with
      | lbu d' n' off =>
        obtain ⟨⟨hd32, hn, hm, hop1, hop2⟩, -⟩ := ok0
        obtain ⟨⟨hd', hn', hp1, hp2⟩, -⟩ := ok1
        have a0 : e21 (Cj.map encG) q.toUInt64 = d.toUInt64 := A0
        have b0 : e22 (Cj.map encG) q.toUInt64 = n.toUInt64 := B0
        have c0 : e23 (Cj.map encG) q.toUInt64 = m.toUInt64 := C0
        obtain ⟨h0, h1, hP⟩ := bC15 (o := op.toUInt64) (c1 := iu off)
          (P := eqb d'.toUInt64 d.toUInt64 * eqb n'.toUInt64 d.toUInt64) hc
        obtain ⟨hP, hnd⟩ := bEqbR hP
        have e1 : d = d' := (bTUInj (by omega) (by omega) (bEqb1 hP)).symm
        have e2 : d = n' := (bTUInj (by omega) (by omega) hnd).symm
        have e3 : op = 1 := bTUInj (b := 1) (by omega) (by omega) h0
        have e4 : off = 0 := by
          have := bIuInj (k := 0) (by omega) (by omega) (by omega) h1
          omega
        subst e1 e2 e3 e4
        have he' : e39 (e21 (Cj.map encG) q.toUInt64) * e39 (e22 (Cj.map encG) q.toUInt64)
            * e39 (e23 (Cj.map encG) q.toUInt64) ≠ 0 := he
        rw [a0, b0, c0, bE39 _ hd32, bE39 n hn, bE39 m hm] at he'
        obtain ⟨md, mn, mm⟩ := bMul3 he'
        refine ⟨.ldrbx _ n m, rfl, rfl, ?_, rfl, rfl, (by show 1 ≤ 4; omega), rfl, ?_, ?_⟩
        · show (NTm.mr _ && NTm.mr n && NTm.mr m) = true
          rw [md, mn, mm]; rfl
        · intro p hp
          exact absurd hp List.not_mem_nil
        · intro z o
          show bpush o (e51 945842176 (e42 (e21 (Cj.map encG) q.toUInt64)) (e42 (e22 (Cj.map encG) q.toUInt64))
              (e42 (e23 (Cj.map encG) q.toUInt64)))
            = o ++ [(ldrbR (armReg _) (armReg n) (armReg m)).toUInt64]
          have w : e51 945842176 (armReg d).toUInt64 (armReg n).toUInt64 (armReg m).toUInt64
              = (ldrbR (armReg d) (armReg n) (armReg m)).toUInt64 :=
            jArmBits.l4_e51 945842176 _ _ _ (by omega) (by omega) (by omega) (ArmRA.armReg_lt _) (ArmRA.armReg_lt _)
              (ArmRA.armReg_lt _)
          rw [a0, b0, c0, bReg md, bReg mn, bReg mm, w]
          rfl
      | _ => bNo hc
  | _ => bNo hc

/-! ## 18: `bpushI` -/

theorem stepAt_18 : StepAt 18 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | slli d n sh =>
    cases r with
    | nil => bNo hc
    | cons j1 r' =>
      obtain ⟨ok1, -⟩ := bSu1 hJ hl q hr
      cases j1 with
      | alu op d' x' y' =>
        obtain ⟨⟨hd32, hn, hsh⟩, -⟩ := ok0
        obtain ⟨⟨hd', hx', hy', hop1, hop2⟩, -⟩ := ok1
        have hP := bC18 (P := eqb d.toUInt64 15 * eqb n.toUInt64 7 * eqb sh.toUInt64 3
          * (eqb d'.toUInt64 15 * eqb x'.toUInt64 15 * eqb y'.toUInt64 5 * eqb op.toUInt64 1)) hc
        simp only [UInt64.mul_assoc] at hP
        obtain ⟨h1, hP⟩ := bEqbL hP
        obtain ⟨h2, hP⟩ := bEqbL hP
        obtain ⟨h3, hP⟩ := bEqbL hP
        obtain ⟨h4, hP⟩ := bEqbL hP
        obtain ⟨h5, hP⟩ := bEqbL hP
        obtain ⟨h6, hP⟩ := bEqbL hP
        have h7 := bEqb1 hP
        have e1 : d = 15 := bTUInj (b := 15) (by omega) (by omega) h1
        have e2 : n = 7 := bTUInj (b := 7) (by omega) (by omega) h2
        have e3 : sh = 3 := bTUInj (b := 3) (by omega) (by omega) h3
        have e4 : d' = 15 := bTUInj (b := 15) (by omega) (by omega) h4
        have e5 : x' = 15 := bTUInj (b := 15) (by omega) (by omega) h5
        have e6 : y' = 5 := bTUInj (b := 5) (by omega) (by omega) h6
        have e7 : op = 1 := bTUInj (b := 1) (by omega) (by omega) h7
        subst e1 e2 e3 e4 e5 e6 e7
        refine ⟨.bpushI, rfl, rfl, rfl, rfl, rfl, (by show 1 ≤ 4; omega), rfl, ?_, ?_⟩
        · intro p hp
          exact absurd hp List.not_mem_nil
        · intro z o
          have w : e51 2332036096 15 5 7 = (addLsl3 (armReg 15) (armReg 5) (armReg 7)).toUInt64 :=
            jArmBits.l4_e51 2332036096 15 5 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          show bpush o (e51 2332036096 15 5 7) = o ++ [(addLsl3 (armReg 15) (armReg 5) (armReg 7)).toUInt64]
          rw [w]; rfl
      | _ => bNo hc
  | _ => bNo hc

/-! ## 19: `align8` -/

theorem stepAt_19 : StepAt 19 := by
  intro Cj hJ hl q hq hc he
  obtain ⟨j0, hd, ok0, A0, B0, C0, -⟩ := bSu0 hJ hl q hq
  rw [hd] at hc ⊢
  generalize hr : Cj.drop (q + 1) = r at hc ⊢
  cases j0 with
  | srli d n sh =>
    cases r with
    | nil => bNo hc
    | cons j1 r' =>
      obtain ⟨ok1, -⟩ := bSu1 hJ hl q hr
      cases j1 with
      | slli d' n' sh' =>
        obtain ⟨⟨hd32, hn, hsh⟩, -⟩ := ok0
        obtain ⟨⟨hd', hn', hsh'⟩, -⟩ := ok1
        have a0 : e21 (Cj.map encG) q.toUInt64 = d.toUInt64 := A0
        have b0 : e22 (Cj.map encG) q.toUInt64 = n.toUInt64 := B0
        obtain ⟨h0, h1, hP⟩ := bC19 (c0 := sh.toUInt64) (c1 := sh'.toUInt64)
          (P := eqb d'.toUInt64 d.toUInt64 * eqb n'.toUInt64 d.toUInt64) hc
        obtain ⟨hP, hnd⟩ := bEqbR hP
        have e1 : d = d' := (bTUInj (by omega) (by omega) (bEqb1 hP)).symm
        have e2 : d = n' := (bTUInj (by omega) (by omega) hnd).symm
        have e3 : sh = 3 := bTUInj (b := 3) (by omega) (by omega) h0
        have e4 : sh' = 3 := bTUInj (b := 3) (by omega) (by omega) h1
        subst e1 e2 e3 e4
        have he' : e39 (e21 (Cj.map encG) q.toUInt64) * e39 (e22 (Cj.map encG) q.toUInt64) ≠ 0 := he
        rw [a0, b0, bE39 d hd32, bE39 n hn] at he'
        obtain ⟨md, mn⟩ := bMul2 he'
        refine ⟨.align8 d n, rfl, rfl, ?_, rfl, rfl, (by show 3 ≤ 4; omega), rfl, ?_, ?_⟩
        · show (NTm.mr d && NTm.mr n) = true
          rw [md, mn]; rfl
        · intro p hp
          exact absurd hp List.not_mem_nil
        · intro z o
          have w1 : e52 3531603968 16 3 0 = (movz 16 3).toUInt64 :=
            jArmBits.l4_e52 3531603968 16 3 0 (by omega) (by omega) (by omega) (by omega) (by omega)
          have w2 : e51 2596283392 (armReg d).toUInt64 (armReg n).toUInt64 16
              = (rr 0x9AC02400 (armReg d) (armReg n) 16).toUInt64 :=
            jArmBits.l4_e51 2596283392 _ _ 16 (by omega) (by omega) (by omega) (ArmRA.armReg_lt _) (ArmRA.armReg_lt _)
              (by omega)
          have w3 : e51 2596282368 (armReg d).toUInt64 (armReg d).toUInt64 16
              = (rr 0x9AC02000 (armReg d) (armReg d) 16).toUInt64 :=
            jArmBits.l4_e51 2596282368 _ _ 16 (by omega) (by omega) (by omega) (ArmRA.armReg_lt _) (ArmRA.armReg_lt _)
              (by omega)
          show bpush (bpush (bpush o (e52 3531603968 16 3 0))
                (e51 2596283392 (e42 (e21 (Cj.map encG) q.toUInt64)) (e42 (e22 (Cj.map encG) q.toUInt64)) 16))
              (e51 2596282368 (e42 (e21 (Cj.map encG) q.toUInt64)) (e42 (e21 (Cj.map encG) q.toUInt64)) 16)
            = o ++ [(movz 16 3).toUInt64, (rr 0x9AC02400 (armReg d) (armReg n) 16).toUInt64,
                (rr 0x9AC02000 (armReg d) (armReg d) 16).toUInt64]
          rw [a0, b0, bReg md, bReg mn, w1, w2, w3, bp3]
      | _ => bNo hc
  | _ => bNo hc

end JT
