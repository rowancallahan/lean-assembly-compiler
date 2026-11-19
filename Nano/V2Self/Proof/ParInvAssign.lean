/- Nano/V2Self/Proof/ParInvAssign: Layer 3, pieces for task 68 `assign` (v133), box G.
`v201_eq`: the scan for an earlier INPUT-flagged binding = `(binds.take i).any Bd.inp`. -/
import Nano.V2Self.Proof.ParInvGroup
namespace ParInv
open C BufL ParSpec ParRun

theorem v201_eq {h : Buf} {bs : List Bd} (hB : BindsRep h bs) :
    ∀ (i n : Nat), i ≤ bs.length → i < n → v201 n h i.toUInt64 = if (bs.take i).any Bd.inp then 1 else 0
  | 0, n + 1, _, _ => by rw [v201]; simp
  | i + 1, n + 1, hi, hn => by
    obtain ⟨_, bl, brows⟩ := hB
    have hne : ((i + 1).toUInt64 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have e1 : (i + 1).toUInt64 - 1 = i.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨_, _, _, a3⟩ := brows i (by omega)
    rw [v201]; simp only [hne, e1, a3]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, List.any_append]
    cases hin : (bs[i]'(by omega)).inp with
    | true => simp [b01, hin]
    | false =>
      simp only [b01, Bool.false_eq_true, if_false, List.any_cons, List.any_nil, hin, Bool.or_false]
      have := v201_eq ⟨‹_›, bl, brows⟩ i n (by omega) (by omega)
      simpa using this

end ParInv
