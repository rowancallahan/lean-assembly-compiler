/- rv2arm meets the generic `EncOK` for the ARM adapter: Gen's bytes are its words' little-endian bytes (`g40_le4`),
rv2arm turns them into the blocks' bytes (`ArmRA.rv2arm_ok`), which are `tbytes (armTarget M X W)` (`bytes_tbytes`). -/
import Nano.Main.TopOn
import Nano.Run.ArmTarget
import Nano.Run.ArmRA3
namespace NanoMain
open Proven.Top JT CallProbe ArmEnc

theorem g40_le4 (c : List UInt8) (ws : List UInt64) (hl : ws.length < 2 ^ 64) :
    ∀ n i (o : List UInt8), ws.length ≤ i + n → i ≤ ws.length →
      C.g40 n c ws (UInt64.ofNat i) o = o ++ (ws.drop i).flatMap ArmRA.le4
  | 0, i, o, h1, h2 => by
    rw [List.drop_of_length_le (by omega)]; simp [C.g40]
  | n + 1, i, o, h1, h2 => by
    simp only [C.g40, bsize, bget]
    have hi : (UInt64.ofNat i).toNat = i := by simp; omega
    by_cases h : i < ws.length
    · have : UInt64.ofNat i < ws.length.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hi]; simp; omega
      have e1 : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
        apply UInt64.toNat_inj.1; simp; all_goals omega
      simp only [this, ↓reduceIte] -- 4.34.1: `simp only [bsize]` leaves bsize in the Decidable instance, so `rw [if_pos]` misses
      rw [e1, g40_le4 c ws hl n (i + 1) _ (by omega) (by omega), hi]
      simp [put, ArmRA.le4, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rw [List.drop_eq_getElem_cons h, List.flatMap_cons]; rfl
    · have : ¬ UInt64.ofNat i < ws.length.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hi]; simp; omega
      simp only [this, ↓reduceIte]; rw [List.drop_of_length_le (by omega)]; simp

theorem le4_wb (W : Nat) :
    ArmRA.le4 W.toUInt64 = [wbyte (BitVec.ofNat 32 W) 0, wbyte (BitVec.ofNat 32 W) 1, wbyte (BitVec.ofNat 32 W) 2,
      wbyte (BitVec.ofNat 32 W) 3] := by
  simp only [ArmRA.le4, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.1 <;>
    simp [wbyte, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, UInt64.toNat_shiftRight, Nat.toUInt64_eq] <;> omega

theorem bytes_tbytes {M : Machine} {X W : M.State → Nat → Prop} :
    ∀ Cj : List J, Cj.flatMap ArmRA.bytesJ = tbytes (armTarget M X W) Cj
  | [] => rfl
  | j :: Cj => by
    unfold tbytes at *
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_append, bytes_tbytes Cj]
    congr 1
    show (blockJ j).flatMap (fun W => ArmRA.le4 W.toUInt64) = ((blockJ j).map (BitVec.ofNat 32)).flatMap _
    rw [List.flatMap_map]; congr 1; funext W; exact le4_wb W

/-- **rv2arm is a correct ARM encoder** for the generic top theorems -/
theorem rv2arm_enc {M : Machine} {X W : M.State → Nat → Prop} : EncOK (armTarget M X W) ArmRA.rv2arm := by
  refine ⟨rfl, fun c Cj hc hJ hne => ?_⟩
  have e : C.g40 16777216 c (Cj.map encG) 0 [] = (Cj.map encG).flatMap ArmRA.le4 := by
    have := g40_le4 c (Cj.map encG) (by simp; omega) 16777216 0 [] (by simp; omega) (by omega)
    simpa using this
  rw [e] at hne ⊢
  obtain ⟨h1, h2⟩ := ArmRA.rv2arm_ok Cj hc hJ hne
  exact ⟨by rw [h1]; exact bytes_tbytes Cj, h2⟩

end NanoMain
