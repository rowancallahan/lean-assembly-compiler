/- Exactness for the call/IF templates of Proof/Call.lean and Proof/Templates.lean: what Gen emits (g29 epilogue copy, the
epilogue tail, the IF head, popSlot) is `template.map encG`.  Position-independent templates only. -/
import Nano.Run.ExprExact
import Nano.Run.Templates
import Nano.Run.CallA
namespace CallProbe
open C

/-- the copy loop from index j on (the tail of `copy p q q`) -/
def copyR (p q j : Nat) : Nat → List J
  | 0 => []
  | r + 1 => copyJ p q j ++ copyR p q (j + 1) r

theorem copy_eq_copyR (p q : Nat) : ∀ k, copy p q k = copyR p q 0 k := by
  have gen : ∀ k j, copy p q (j + k) = copy p q j ++ copyR p q j k := by
    intro k; induction k with
    | zero => intro j; simp [copyR]
    | succ k ih => intro j; rw [show j + (k + 1) = (j + 1) + k by omega, ih (j + 1)]; simp [copy, copyR, List.append_assoc]
  intro k; have := gen k 0; simp [copy] at this; exact this

theorem u_ld (q j : Nat) (hj : j < q) (hq : q < 251) :
    ((q.toUInt64 - 1 - j.toUInt64) <<< 3) = iu (8 * ((q - 1 - j : Nat) : Int)) := by
  apply UInt64.toNat.inj; rw [iu_toNat]
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_sub, UInt64.toNat_add, Nat.shiftLeft_eq, Nat.toUInt64]
  omega

theorem u_sd (p j : Nat) (hp : p < 251) (hj : j < 251) :
    (p.toUInt64 <<< 3) + g_16 - ((j + 1).toUInt64 <<< 3) = iu (8 * (p : Int) + 16 - 8 * ((j + 1 : Nat) : Int)) := by
  apply UInt64.toNat.inj; rw [iu_toNat]
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_sub, UInt64.toNat_add, Nat.shiftLeft_eq, g_16, Nat.toUInt64, UInt64.size]
  omega

def epiTail (p q : Nat) : List J := [.addi 31 8 (8 * (p : Int) + 16 - 8 * (q : Int)), .addi 8 15 0, .jalr 0 14]

theorem u_sd' (p j : Nat) (hp : p < 251) (hj : j < 251) :
    (UInt64.ofNat p <<< 3) + g_16 - ((UInt64.ofNat j + 1) <<< 3) = iu (8 * (p : Int) + 16 - 8 * ((j : Int) + 1)) := by
  have := u_sd p j hp hj
  simpa [Nat.toUInt64, UInt64.ofNat_add] using this

theorem u_tail' (p q : Nat) (hp : p < 251) (hq : q < 251) :
    (UInt64.ofNat p <<< 3) + g_16 - (UInt64.ofNat q <<< 3) = iu (8 * (p : Int) + 16 - 8 * (q : Int)) := by
  apply UInt64.toNat.inj; rw [iu_toNat]
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_sub, UInt64.toNat_add, Nat.shiftLeft_eq, g_16]; omega

theorem g29_exact (p q : Nat) (hp : p < 251) (hq : q < 251) : ∀ (n j : Nat) (o : Buf), j ≤ q → q - j + 1 ≤ n →
    g29 n p.toUInt64 q.toUInt64 j.toUInt64 o = o ++ (copyR p q j (q - j) ++ epiTail p q).map encG
  | 0, j, o, _, h => by omega
  | n + 1, j, o, hj, hn => by
    by_cases hlt : j < q
    · have hl : j.toUInt64 < q.toUInt64 := by rw [UInt64.lt_iff_toNat_lt]; simp [Nat.toUInt64]; omega
      simp only [g29, hl, if_true]
      have e : j.toUInt64 + 1 = (j + 1).toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
      rw [e, g29_exact p q hp hq n (j + 1) _ (by omega) (by omega)]
      rw [show q - j = (q - (j + 1)) + 1 by omega]
      simp [copyR, copyJ, encG, bpush, u_ld q j hlt hq]
      rw [u_sd' p j hp (by omega)]
    · have : j = q := by omega
      subst this
      simp [g29, copyR, epiTail, encG, bpush, g10, g2]
      rw [u_tail' p j hp hq]
      have i0 : iu 0 = 0 := by decide
      simp [i0]

/-- the whole epilogue as emitted by g37 (`g29 512 p q 0` after the two loads of ra/s0) -/
theorem epi_exact (o : Buf) (p q : Nat) (hp : p < 251) (hq : q < 251) :
    g29 512 p.toUInt64 q.toUInt64 0 (bpush (bpush o (g11 14 8 8)) (g11 15 8 0)) = o ++ (epi p q).map encG := by
  have h := g29_exact p q hp hq 512 0 (bpush (bpush o (g11 14 8 8)) (g11 15 8 0)) (by omega) (by omega)
  have e0 : (0 : Nat).toUInt64 = 0 := rfl
  rw [e0] at h
  rw [h, show epi p q = [.ld 14 8 8, .ld 15 8 0] ++ (copyR p q 0 q ++ epiTail p q) by
    simp [epi, epiTail, copy_eq_copyR]]
  have i8 : iu 8 = 8 := by decide
  have i0 : iu 0 = 0 := by decide
  simp [encG, bpush, i8, i0]

theorem u_neg (r : Nat) (hr : r < 251) : g_0 - (r.toUInt64 <<< 3) = iu (-8 * (r : Int)) := by
  apply UInt64.toNat.inj; rw [iu_toNat]
  have hsz : UInt64.size = 18446744073709551616 := rfl
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_sub, Nat.shiftLeft_eq, g_0, Nat.toUInt64, hsz]; omega

/-- the prologue as g38 emits it (`g22 (g22 o 1) 8`, `addi s0 t6 0`, `addi t6 t6 −8r`, `bgeu t6 t5 +8`, `jal` to the stub) -/
theorem pro_exact (o : Buf) (r : Nat) (hr : r < 251) (ho : o.length + 12 < 2 ^ 32) :
    bpush (bpush (bpush (bpush (g22 (g22 o 1) 8) (g10 8 31 0)) (g10 31 31 (g_0 - (r.toUInt64 <<< 3)))) (g4 7 31 30 8))
      (g13 0 (bsize (g22 (g22 o 1) 8) + 3) 1) = o ++ (proA 1 o.length r).map encG := by
  have e1 : g22 o 1 = o ++ (pushA 1 o.length 1).map encG := by
    have := g22_exact o 1 (by decide) (by omega); simpa using this
  have e2 : g22 (g22 o 1) 8 = (o ++ (pushA 1 o.length 1).map encG) ++ (pushA 1 (o.length + 4) 8).map encG := by
    rw [e1]
    have := g22_exact (o ++ (pushA 1 o.length 1).map encG) 8 (by decide) (by simp [pushA_len]; omega)
    simpa [pushA_len] using this
  have hh1 : bsize (g22 (g22 o 1) 8) = (o.length + 8).toUInt64 := by
    rw [e2]; simp [bsize, pushA_len]
  have ju := jal_off (o.length + 9) (by omega)
  have i0 : iu 0 = 0 := by decide
  have i4 : iu (4 * 2) = 8 := by decide
  have hx : (1 : UInt64) - ((o.length + 8).toUInt64 + 3) = 1 - (UInt64.ofNat (o.length + 9) + 2) := by
    have : (o.length + 8).toUInt64 + 3 = UInt64.ofNat (o.length + 9) + 2 := by
      simp only [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc]; congr 1
    rw [this]
  have jw : g13 0 ((o.length + 8).toUInt64 + 3) 1 = encG (.jal 0 (((1 : Nat) : Int) - (((o.length + 11 : Nat) : Int)))) := by
    have e : (4 : Int) * (((1 : Nat) : Int) - (((o.length + 11 : Nat) : Int))) = 4 * (((1 : Nat) : Int) - (((o.length + 9 : Nat) : Int) + 2)) := by omega
    simp only [g13, encG, e, ← ju, hx]; rfl
  rw [u_neg r hr, hh1, jw, e2]
  have i8 : iu 8 = 8 := by decide
  simp [proA, encG, bpush, i0, i8]

end CallProbe

namespace Templates
open CallProbe C

theorem popSlot_exact (o : Buf) (p k : Nat) (hp : p < 251) (hk : k < 251) :
    g26 256 p.toUInt64 k.toUInt64 1 o = o ++ (popSlot p k).map encG := by
  have e : k.toUInt64 + 1 - 1 = k.toUInt64 := by simp
  have g := g24_off p k hp hk
  have hoff : offOf p k = slotOff p k := by
    unfold offOf slotOff; split <;> rfl
  simp [g26, popSlot, encG, bpush, e, g, hoff, iu, g10, g11, g12]

/-- the first four words of the IF head: pop2, `beq`/`bltu t0, t1, +2`; word five (`jal ELSE`) is the placeholder 0, patched by g20 -/
def ifHead4 (c : J) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 16, c]

theorem ifHead_eq_exact (o : Buf) :
    bpush (bpush (g30 o 16) (g4 0 5 6 8)) 0 = o ++ (ifHead4 (.beq 5 6 2)).map encG ++ [0] := by
  have i8 : iu 16 = 16 := by decide
  have i0 : iu 0 = 0 := by decide
  have i8' : iu 8 = 8 := by decide
  have i4 : iu (4 * 2) = 8 := by decide
  simp [g30, ifHead4, encG, bpush, i8, i0, i8', i4]

theorem ifHead_lt_exact (o : Buf) :
    bpush (bpush (g30 o 16) (g4 6 5 6 8)) 0 = o ++ (ifHead4 (.bltu 5 6 2)).map encG ++ [0] := by
  have i8 : iu 16 = 16 := by decide
  have i0 : iu 0 = 0 := by decide
  have i8' : iu 8 = 8 := by decide
  have i4 : iu (4 * 2) = 8 := by decide
  simp [g30, ifHead4, encG, bpush, i8, i0, i8', i4]

end Templates
