/- B₁ bootstrap (branch nano-v2-boot, Testing/notes/NANO_V2_BOOT.md): the nano v2 prelude in the form the S3 front end
(`s3_compileF`) accepts. S3 has no `Nat`↔`UInt64` conversion and `o ++ [b]` copies `o` (quadratic allocation), so
each v2 stage gets an S3 twin with
* `rdS`/`lenS`: list recursion for `rd`/`len` (equal on every input);
* `putR`: the output kept REVERSED (`b :: o`), the entry reverses once;
* fuel as a word (`UInt64`, well-founded on `toNat`) instead of `Nat` (equal while the fuel is `< 2^64`). -/
import Nano.V2S.Prelude

namespace Nano.V2B
open Nano.V2S

def rdS : List UInt8 → UInt64 → UInt64
  | [], _ => 0
  | x :: r, i => if i == 0 then x.toUInt64 else rdS r (i - 1)

def lenS : List UInt8 → UInt64
  | [] => 0
  | _ :: r => lenS r + 1

/-- `put` on the reversed output -/
def putR (o : List UInt8) (b : UInt64) : List UInt8 := b.toUInt8 :: o

theorem rdS_eq : ∀ (xs : List UInt8) (i : UInt64), rdS xs i = rd xs i
  | [], _ => by simp [rdS, rd]
  | x :: r, i => by
    unfold rdS
    by_cases h : i = 0
    · subst h; simp [rd]
    · have hi : i.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
      rw [if_neg (by simpa using h), rdS_eq r (i - 1)]
      unfold rd
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      obtain ⟨n, hn⟩ : ∃ n, i.toNat = n + 1 := ⟨i.toNat - 1, by omega⟩
      simp [hn]

theorem lenS_eq : ∀ xs : List UInt8, lenS xs = len xs
  | [] => rfl
  | _ :: r => by
    rw [lenS, lenS_eq r]; unfold len; simp

theorem putR_rev (o : List UInt8) (b : UInt64) : putR o.reverse b = (put o b).reverse := by
  simp [putR, put]

/-- a word fuel `f ≠ 0` is a successor -/
theorem fuel_succ (n : Nat) (h : n + 1 < 2 ^ 64) : (n + 1).toUInt64 ≠ 0 ∧ (n + 1).toUInt64 - 1 = n.toUInt64 := by
  constructor
  · intro e; have := congrArg UInt64.toNat e; simp at this; omega
  · apply UInt64.toNat_inj.mp; simp

theorem fuel_zero : (0 : Nat).toUInt64 = 0 := rfl

theorem dec_lt {f : UInt64} (h : ¬ f = 0) : (f - 1).toNat < f.toNat := by
  have hk : f.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-- the twins test `b < a` (S3's certificate search refutes `<`/`¬ <` pairs, not `≤`/`<` on words) -/
theorem ite_lt_swap {α : Type} (a b : UInt64) (x y : α) : (if b < a then y else x) = (if a ≤ b then x else y) := by
  by_cases h : a ≤ b
  · rw [if_pos h, if_neg (UInt64.not_lt.mpr h)]
  · rw [if_neg h, if_pos (UInt64.not_le.mp h)]

end Nano.V2B
