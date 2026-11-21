/- Exactness: the instruction lists of Proof/Expr.lean ARE the words Gen emits.  `encG` maps a template instruction to
the word C's own encoders (g1–g5, g10–g12) produce; each lemma says: Gen's emitter appends exactly `template.map encG`.
Together with Proof/Bridge.lean (C's encoders = nano-v2 `I.enc`, which Enc/Sim tie to Sail) this closes the gap between
the abstract-machine statements of Expr.lean and the generated code. -/
import Nano.Run.Expr
import Nano.Codegen.Gen
namespace CallProbe
open C

/-- an Int offset as C's two's-complement UInt64 -/
def iu (z : Int) : UInt64 := UInt64.ofNat (z % 2 ^ 64).toNat

def aluF (op : Nat) : UInt64 × UInt64 :=   -- (funct7, funct3) of g31's table
  if op = 1 then (0, 0) else if op = 2 then (32, 0) else if op = 3 then (1, 0) else if op = 4 then (0, 7)
  else if op = 5 then (0, 6) else if op = 6 then (0, 1) else if op = 7 then (0, 5) else (0, 4)

def encG : J → UInt64
  | .addi rd rs imm => g10 rd.toUInt64 rs.toUInt64 (iu imm)
  | .ld rd rs off => g11 rd.toUInt64 rs.toUInt64 (iu off)
  | .sd r2 r1 off => g12 r2.toUInt64 r1.toUInt64 (iu off)
  | .jal rd off => g5 rd.toUInt64 (iu (4 * off))
  | .bgeu a b off => g4 7 a.toUInt64 b.toUInt64 (iu (4 * off))
  | .beq a b off => g4 0 a.toUInt64 b.toUInt64 (iu (4 * off))
  | .bltu a b off => g4 6 a.toUInt64 b.toUInt64 (iu (4 * off))
  | .alu op rd a b => g1 (aluF op).1 (aluF op).2 rd.toUInt64 a.toUInt64 b.toUInt64
  | .slli rd rs sh => g2 g_19 1 rd.toUInt64 rs.toUInt64 sh.toUInt64
  | .lbu rd rs off => g2 g_3 4 rd.toUInt64 rs.toUInt64 (iu off)
  | .srli rd rs sh => g2 g_19 5 rd.toUInt64 rs.toUInt64 sh.toUInt64
  | .bne a b off => g4 1 a.toUInt64 b.toUInt64 (iu (4 * off))
  | .sb r2 r1 off => g3 0 r2.toUInt64 r1.toUInt64 (iu off)
  | .jalr rd rs => g2 g_103 0 rd.toUInt64 rs.toUInt64 0

theorem g31_exact (o : Buf) (p : Nat) (hp : 1 ≤ p) (hp8 : p ≤ 8) :
    g31 o p.toUInt64 = o ++ (binT p).map encG := by
  unfold g31 g30
  rcases (by omega : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [binT, encG, bpush, iu, aluF, g10, g11, g12, g1, g2, g3, g4, g_3, g_19, g_16, g_31, g_35, g_51, g_63, g_99, g_103, g_127, g_4095]

theorem iu_toNat (z : Int) : (iu z).toNat = (z % 2 ^ 64).toNat := by
  unfold iu; simp only [UInt64.toNat_ofNat']; omega

/-- C's jump offset `(b − a) <<< 2` (words a = h + 2 → stub word 1) is the template's `jal x0 (tgt − (q+2))`, tgt = 1 -/
theorem jal_off (q : Nat) (hq : q < 2 ^ 32) :
    ((1 : UInt64) - (UInt64.ofNat q + 2)) <<< 2 = iu (4 * (((1 : Nat) : Int) - ((q : Int) + 2))) := by
  apply UInt64.toNat.inj
  rw [iu_toNat]
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_sub, UInt64.toNat_add, Nat.shiftLeft_eq]
  omega

theorem g22_exact (o : Buf) (d : Nat) (hd : d < 32) (ho : o.length < 2 ^ 32) :
    g22 o d.toUInt64 = o ++ (pushA 1 o.length d).map encG := by
  unfold g22 g13
  have hh : bsize o = o.length.toUInt64 := rfl
  have := jal_off o.length ho
  have i0 : iu 0 = 0 := by decide
  have i8 : iu 8 = 8 := by decide
  have im8 : iu (-8) = g_0 - 8 := by decide
  have i16 : iu (4 * 2) = 8 := by decide
  simp [pushA, push, encG, bpush, hh, g10, g12, g4, g2, g3, g5, i0, i8, im8, this, g_908, g_0, g_31, g_35, g_99, g_127, g_4095, g_1023, g_255, g_1, g_111]

section prims
local macro "gsimp" : tactic => `(tactic| simp [encG, bpush, iu, g10, g11, g12, g1, g2, g3, g4, aluF, g_0, g_3, g_16, g_19, g_31, g_35, g_51, g_63, g_99, g_103, g_127, g_4095, g_15, g_1])

theorem g32_len (o : Buf) (u : UInt64) (ho : o.length < 2 ^ 32) : g32 o 1 u = o ++ (lenT 1 o.length).map encG := by
  unfold g32; simp only [lenT]; have := g22_exact o 29 (by decide) ho; simpa using this

theorem g32_len3 (o : Buf) (u : UInt64) (ho : o.length < 2 ^ 32) : g32 o 3 u = o ++ (lenT 1 o.length).map encG := by
  unfold g32; simp only [lenT]; have := g22_exact o 29 (by decide) ho; simpa using this

theorem g32_rd (o : Buf) (u : UInt64) : g32 o 2 u = o ++ rdT.map encG := by
  unfold g32; simp [rdT]; gsimp

theorem g32_bsize (o : Buf) (u : UInt64) : g32 o 6 u = o ++ bsizeT.map encG := by
  unfold g32; simp [bsizeT]; gsimp

theorem g32_bget (o : Buf) (u : UInt64) : g32 o 7 u = o ++ bgetT.map encG := by
  unfold g32 g30; simp [bgetT]; gsimp
end prims

/-! ### li (g23) -/
theorem iu_nat (n : Nat) (h : n < 2 ^ 64) : iu (n : Int) = UInt64.ofNat n := by
  unfold iu; congr 1; omega

theorem andm (n : Nat) : n &&& 255 = n % 256 := by
  have : (255:Nat) = 2^8-1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem sh8 (v : UInt64) (j : Nat) (m : UInt64) (hm : m.toNat = 8 * j) (hj : j < 8) :
    (v >>> m) &&& 255 = UInt64.ofNat ((v.toNat / 2 ^ (8 * j)) % 256) := by
  apply UInt64.toNat.inj
  have h8 : 8 * j % 64 = 8 * j := Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hm, h8]
  simp only [UInt64.toNat_ofNat']
  have h255 : (255 : UInt64).toNat = 255 := rfl
  rw [h255, andm, Nat.shiftRight_eq_div_pow]
  have : v.toNat / 2 ^ (8 * j) % 256 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]

theorem g23_small (o : Buf) (d : Nat) (v : UInt64) (hd : d < 32) (hv : v.toNat < 2048) :
    g23 o d.toUInt64 v = o ++ (liT d v).map encG := by
  have hv' : v < 2048 := by rw [UInt64.lt_iff_toNat_lt]; simpa using hv
  have : iu (v.toNat : Int) = v := by rw [iu_nat _ v.toNat_lt]; simp
  simp [g23, hv', liT, hv, encG, bpush, this]

theorem g23_big (o : Buf) (d : Nat) (v : UInt64) (hd : d < 32) (hv : ¬ v.toNat < 2048) :
    g23 o d.toUInt64 v = o ++ (liT d v).map encG := by
  have hv' : ¬ v < 2048 := by rw [UInt64.lt_iff_toNat_lt]; simpa using hv
  have b56 : (v >>> 56) &&& g_255 = UInt64.ofNat ((v.toNat / 72057594037927936) % 256) := by
    have := sh8 v 7 56 rfl (by omega); simpa [g_255] using this
  have b48 : (v >>> 48) &&& g_255 = UInt64.ofNat ((v.toNat / 281474976710656) % 256) := by
    have := sh8 v 6 48 rfl (by omega); simpa [g_255] using this
  have b40 : (v >>> 40) &&& g_255 = UInt64.ofNat ((v.toNat / 1099511627776) % 256) := by
    have := sh8 v 5 40 rfl (by omega); simpa [g_255] using this
  have b32 : (v >>> 32) &&& g_255 = UInt64.ofNat ((v.toNat / 4294967296) % 256) := by
    have := sh8 v 4 32 rfl (by omega); simpa [g_255] using this
  have b24 : (v >>> 24) &&& g_255 = UInt64.ofNat ((v.toNat / 16777216) % 256) := by
    have := sh8 v 3 24 rfl (by omega); simpa [g_255] using this
  have b16 : (v >>> 16) &&& g_255 = UInt64.ofNat ((v.toNat / 65536) % 256) := by
    have := sh8 v 2 16 rfl (by omega); simpa [g_255] using this
  have b8 : (v >>> 8) &&& g_255 = UInt64.ofNat ((v.toNat / 256) % 256) := by
    have := sh8 v 1 8 rfl (by omega); simpa [g_255] using this
  have b0 : (v >>> 0) &&& g_255 = UInt64.ofNat ((v.toNat / 1) % 256) := by
    have := sh8 v 0 0 rfl (by omega); simpa [g_255] using this
  have i0 : iu 0 = 0 := by decide
  have hb : ∀ n : Nat, n < 256 → iu (n : Int) = UInt64.ofNat n := fun n hn => iu_nat n (by omega)
  simp [g23, hv', liT, hv, liB, liJ, encG, bpush, i0, b56, b48, b40, b32, b24, b16, b8, b0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 1
  all_goals apply UInt64.toNat.inj
  all_goals rw [iu_toNat]
  all_goals simp only [UInt64.toNat_ofNat', UInt64.toNat_and, show g_255.toNat = 255 from rfl, andm]
  all_goals omega

/-! ### CONST, LOCAL -/
theorem g21_eq (o : Buf) : g21 o = g22 o 5 := rfl

theorem g23_exact (o : Buf) (d : Nat) (v : UInt64) (hd : d < 32) : g23 o d.toUInt64 v = o ++ (liT d v).map encG := by
  by_cases hv : v.toNat < 2048
  · exact g23_small o d v hd hv
  · exact g23_big o d v hd hv

theorem const_exact (o : Buf) (v : UInt64) (ho : o.length + 17 + 4 < 2 ^ 32) :
    g21 (g23 o 5 v) = o ++ (constT 1 o.length v).map encG := by
  have h1 : g23 o (5 : Nat).toUInt64 v = o ++ (liT 5 v).map encG := g23_exact o 5 v (by decide)
  have hl : (liT 5 v).length ≤ 17 := by
    by_cases hv : v.toNat < 2048
    · rw [liT_len_small _ _ hv]; omega
    · rw [liT_len_big _ _ hv]; omega
  rw [g21_eq]
  have e5 : (5 : UInt64) = (5 : Nat).toUInt64 := rfl
  rw [e5, h1, g22_exact _ 5 (by decide) (by simp; omega)]
  simp [constT]

theorem g24_off (p s : Nat) (hp : p < 251) (hs : s < 251) : g24 p.toUInt64 s.toUInt64 = iu (offOf p s) := by
  have hsz : UInt64.size = 18446744073709551616 := rfl
  unfold g24 offOf
  apply UInt64.toNat.inj
  rw [iu_toNat]
  by_cases h : s < p
  · have h' : s.toUInt64 < p.toUInt64 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
    simp [h, h', UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_sub, Nat.shiftLeft_eq, g_16, g_0, hsz]
    omega
  · have h' : ¬ s.toUInt64 < p.toUInt64 := by rw [UInt64.lt_iff_toNat_lt]; simp; omega
    simp [h, h', UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_sub, Nat.shiftLeft_eq, g_16, g_0, hsz]
    omega

theorem pushA_len (tgt q r : Nat) : (pushA tgt q r).length = 4 := rfl

theorem toU_add (a b : Nat) : (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]

theorem g25_exact (p : Nat) (hp : p < 251) : ∀ (n w s : Nat) (o : Buf), w ≤ n → s + w < 251 → o.length + 5 * w + 4 < 2 ^ 32 →
    g25 n p.toUInt64 s.toUInt64 w.toUInt64 o = o ++ (localT 1 p s o.length w).map encG
  | 0, w, s, o, hw, _, _ => by
      have : w = 0 := by omega
      subst this; simp [g25, localT]
  | n + 1, w, s, o, hw, hs, ho => by
    rcases w with _ | w
    · simp [g25, localT]
    · have hne : ¬ ((w + 1).toUInt64 == 0) = true := by
        simp [Nat.toUInt64, UInt64.ofNat_add]
        intro h; have := congrArg UInt64.toNat h; simp at this; omega
      have e1 : (w + 1).toUInt64 - 1 = w.toUInt64 := by simp [toU_add]
      have e2 : s.toUInt64 + 1 = (s + 1).toUInt64 := by simp [toU_add]
      have hv : g11 5 8 (g24 p.toUInt64 s.toUInt64) = encG (.ld 5 8 (offOf p s)) := by
        rw [g24_off p s hp (by omega)]; simp [encG]
      have hL : (o ++ [encG (.ld 5 8 (offOf p s))]).length < 2 ^ 32 := by simp; omega
      have hpush := g22_exact (o ++ [encG (.ld 5 8 (offOf p s))]) 5 (by decide) hL
      simp only [g25, hne, if_false, Bool.false_eq_true]
      rw [e1, e2, g21_eq]
      simp only [bpush, hv]
      have e5 : (5 : UInt64) = (5 : Nat).toUInt64 := rfl
      rw [e5, hpush]
      rw [g25_exact p hp n w (s + 1) _ (by omega) (by omega) (by simp [pushA_len]; omega)]
      simp [localT, pushA_len, List.append_assoc]

/-- the whole of LOCAL as emitted: g25 (fuel 256, as in g36) -/
theorem local_exact (p s w : Nat) (o : Buf) (hp : p < 251) (hw : w < 251) (hs : s + w < 251) (ho : o.length + 5 * w + 4 < 2 ^ 32) :
    g25 256 p.toUInt64 s.toUInt64 w.toUInt64 o = o ++ (localT 1 p s o.length w).map encG :=
  g25_exact p hp 256 w s o (by omega) hs ho

end CallProbe
