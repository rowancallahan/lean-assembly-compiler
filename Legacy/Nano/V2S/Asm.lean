/- nano v2 source: the assembler `asm` (Nano/Asm.lean) as a byte machine (Testing/notes/NANO_V2_SRC.md).
Constructs: UInt64 `&&& ||| <<< >>>`, `==`, `≤`, `||` in conditions, `if`, `let`, calls, fuel recursion, `rd`, `len`,
`put`.  Bridge: `asmV_eq : asmV xs = asm xs` for every input of length < 2^32. -/
import Legacy.Nano.Asm
import Legacy.Nano.V2S.Prelude

namespace Nano.V2S

def ax0 (op a c : UInt64) : UInt64 :=
  if op == 3 || op == 4 then ((a &&& 1) <<< 7) ||| 3
  else if op == 0 || op == 1 || op == 5 || op == 6 || op == 8 then ((a &&& 1) <<< 7) ||| 0x13
  else if op == 11 then 0x23
  else if op == 16 then ((c &&& 1) <<< 7) ||| 0x23
  else if op == 14 || op == 24 || op == 32 || op == 40 then ((a &&& 1) <<< 7) ||| 0x33
  else if op == 7 then 0x63
  else if op == 48 then ((a &&& 1) <<< 7) ||| 0x67
  else 0x13

def ax1 (op a b c : UInt64) : UInt64 :=
  if op == 11 then ((c &&& 3) <<< 2) ||| (0x30 : UInt64) ||| ((b &&& 1) <<< 7)
  else if op == 16 then ((c >>> 1) &&& (15 : UInt64)) ||| ((b &&& 1) <<< 7)
  else if op == 7 then (0x76 : UInt64) ||| ((b &&& 1) <<< 7)
  else (a >>> 1) ||| ((op &&& 7) <<< 4) ||| ((b &&& 1) <<< 7)

def ax2 (op a b c : UInt64) : UInt64 :=
  if op == 3 || op == 8 then (b >>> 1) ||| ((c &&& 1) <<< 7)
  else if op == 11 || op == 16 then (b >>> 1) ||| ((a &&& 15) <<< 4)
  else (b >>> 1) ||| ((c &&& 15) <<< 4)

def ax3 (op a c : UInt64) : UInt64 :=
  if op == 3 || op == 8 then c >>> 1
  else if op == 0 then (c >>> 4) ||| (if c < 128 then 0 else 0xF0)
  else if op == 11 then ((c >>> 2) <<< 1) ||| (a >>> 4)
  else if op == 16 then a >>> 4
  else if op == 32 then (c >>> 4) ||| 0x40
  else if op == 40 then (c >>> 4) ||| 2
  else c >>> 4

/-- one record `[op, a, b, c]` at input position `i` per step -/
def asmL : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, _, _, o => o
  | n + 1, xs, i, o =>
    if i + 4 ≤ len xs then
      let op := rd xs i
      let a := rd xs (i + 1)
      let b := rd xs (i + 2)
      let c := rd xs (i + 3)
      asmL n xs (i + 4) (put (put (put (put o (ax0 op a c)) (ax1 op a b c)) (ax2 op a b c)) (ax3 op a c))
    else o

/-- **the assembler, nano v2 source** -/
def asmV (xs : List UInt8) : List UInt8 := asmL xs.length xs 0 []

/-! ## bridge -/

theorem beq8 (x : UInt8) (n : Nat) (h : n < 256) :
    (x.toUInt64 == (OfNat.ofNat n : UInt64)) = (x == (OfNat.ofNat n : UInt8)) := by
  have e : (OfNat.ofNat n : UInt64) = (OfNat.ofNat n : UInt8).toUInt64 := by
    apply UInt64.toNat_inj.mp; rw [UInt8.toNat_toUInt64]; show (UInt64.ofNat n).toNat = (UInt8.ofNat n).toNat
    simp; omega
  rw [e]
  by_cases hx : x = OfNat.ofNat n
  · rw [hx]; simp
  · have : x.toUInt64 ≠ (OfNat.ofNat n : UInt8).toUInt64 := fun q => hx (UInt8.toUInt64_inj.mp q)
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact ⟨fun q => absurd q this, fun q => absurd q hx⟩
theorem shr8 (x : UInt8) (k : Nat) (hk : k < 8) :
    (x.toUInt64 >>> (OfNat.ofNat k : UInt64)).toUInt8 = x >>> (OfNat.ofNat k : UInt8) := by
  apply UInt8.toNat_inj.mp
  have := x.toNat_lt
  have e1 : (OfNat.ofNat k : UInt64).toNat = k := by show (UInt64.ofNat k).toNat = k; simp [UInt64.toNat_ofNat']; omega
  have e2 : (OfNat.ofNat k : UInt8).toNat = k := by show (UInt8.ofNat k).toNat = k; simp [UInt8.toNat_ofNat']; omega
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt8.toNat_shiftRight, UInt8.toNat_toUInt64, e1, e2,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := k) (by omega)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))

theorem lt8 (x : UInt8) : (x.toUInt64 < 128) ↔ (x < 128) := by
  rw [UInt64.lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt]; simp

theorem asm_rec (op a b c : UInt8) :
    (ax0 op.toUInt64 a.toUInt64 c.toUInt64).toUInt8 = X0 ∧
    (ax1 op.toUInt64 a.toUInt64 b.toUInt64 c.toUInt64).toUInt8 = X1 ∧
    (ax2 op.toUInt64 a.toUInt64 b.toUInt64 c.toUInt64).toUInt8 = X2 ∧
    (ax3 op.toUInt64 a.toUInt64 c.toUInt64).toUInt8 = X3 := by
  simp only [ax0, ax1, ax2, ax3, beq8 op 0 (by decide), beq8 op 1 (by decide), beq8 op 3 (by decide),
    beq8 op 4 (by decide), beq8 op 5 (by decide), beq8 op 6 (by decide), beq8 op 7 (by decide),
    beq8 op 8 (by decide), beq8 op 11 (by decide), beq8 op 14 (by decide), beq8 op 16 (by decide),
    beq8 op 24 (by decide), beq8 op 32 (by decide), beq8 op 40 (by decide), beq8 op 48 (by decide), lt8,
  ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (repeat' split) <;>
    simp [shr8 a 1 (by decide), shr8 b 1 (by decide), shr8 c 1 (by decide), shr8 c 2 (by decide),
      shr8 c 4 (by decide), shr8 a 4 (by decide)]

theorem asm_cons4 (op a b c : UInt8) (r : List UInt8) : asm (op :: a :: b :: c :: r) =
    (ax0 op.toUInt64 a.toUInt64 c.toUInt64).toUInt8 :: (ax1 op.toUInt64 a.toUInt64 b.toUInt64 c.toUInt64).toUInt8 ::
    (ax2 op.toUInt64 a.toUInt64 b.toUInt64 c.toUInt64).toUInt8 :: (ax3 op.toUInt64 a.toUInt64 c.toUInt64).toUInt8 ::
    asm r := by
  obtain ⟨q0, q1, q2, q3⟩ := asm_rec op a b c
  rw [q0, q1, q2, q3, asm]

theorem asm_short : ∀ l : List UInt8, l.length < 4 → asm l = []
  | [], _ => by simp [asm]
  | [_], _ => by simp [asm]
  | [_, _], _ => by simp [asm]
  | [_, _, _], _ => by simp [asm]
  | _ :: _ :: _ :: _ :: _, h => by simp at h; omega

theorem rd_at (xs : List UInt8) (i : UInt64) (k : Nat) (hx : xs.length < 2 ^ 32) (h : i.toNat + k < xs.length) :
    rd xs (i + k.toUInt64) = (xs[i.toNat + k]'h).toUInt64 := by
  unfold rd
  have : (i + k.toUInt64).toNat = i.toNat + k := by simp; omega
  rw [this]; simp [h]

theorem asmL_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n : Nat) (i : UInt64) (o : List UInt8),
    i.toNat ≤ xs.length → xs.length < i.toNat + 4 * n + 4 → asmL n xs i o = o ++ asm (xs.drop i.toNat)
  | 0, i, o, _, h2 => by
    rw [asmL, asm_short _ (by simp; omega)]; simp
  | n + 1, i, o, h1, h2 => by
    rw [asmL]
    by_cases hc : i + 4 ≤ len xs
    · have h4 : i.toNat + 4 ≤ xs.length := by
        unfold len at hc; rw [UInt64.le_iff_toNat_le] at hc; simp at hc; omega
      rw [if_pos hc]
      have r0 : rd xs i = (xs[i.toNat]'(by omega)).toUInt64 := by
        unfold rd; simp [List.getElem?_eq_getElem (show i.toNat < xs.length by omega)]
      have r1 := rd_at xs i 1 hx (by omega)
      have r2 := rd_at xs i 2 hx (by omega)
      have r3 := rd_at xs i 3 hx (by omega)
      have e1 : (1 : Nat).toUInt64 = 1 := rfl
      have e2 : (2 : Nat).toUInt64 = 2 := rfl
      have e3 : (3 : Nat).toUInt64 = 3 := rfl
      rw [e1] at r1; rw [e2] at r2; rw [e3] at r3
      rw [r0, r1, r2, r3]
      have hd : xs.drop i.toNat = xs[i.toNat] :: xs[i.toNat + 1] :: xs[i.toNat + 2] :: xs[i.toNat + 3] ::
          xs.drop (i.toNat + 4) := by
        rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
          List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]; rfl
      have hi4 : (i + 4).toNat = i.toNat + 4 := by simp; omega
      rw [asmL_eq xs hx n (i + 4) _ (by rw [hi4]; omega) (by rw [hi4]; omega), hi4, hd, asm_cons4]
      simp only [put, List.append_assoc, List.cons_append, List.nil_append]; rfl
    · have h4 : ¬ i.toNat + 4 ≤ xs.length := by
        intro q; apply hc; unfold len; rw [UInt64.le_iff_toNat_le]; simp; omega
      rw [if_neg hc, asm_short _ (by simp; omega)]; simp

/-- **the bridge**: the nano v2 source is the assembler, on every input of length < 2^32 -/
theorem asmV_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : asmV xs = asm xs := by
  unfold asmV; rw [asmL_eq xs hx _ 0 [] (by simp) (by simp; omega)]; simp

end Nano.V2S
