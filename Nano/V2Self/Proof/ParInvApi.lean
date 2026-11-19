/- Nano/V2Self/Proof/ParInvApi: the fields of `RepAPI` (ParInvTop) that follow from box C's state relation directly (parser lead).
* `out_of` : `OutRep` ⇒ the heap tail after the token sentinel IS the emitted word list;
* `ntasks_of` : `TasksRep` ⇒ (h[5] = 0 ↔ no frame). -/
import Nano.V2Self.Proof.ParInvState
import Nano.V2Self.Proof.ParInvTop
namespace ParInv
open C BufL ParSpec ParRun

theorem out_of {h ts : Buf} {out : List UInt64} (r : OutRep h ts out) (hl : h.length < 2 ^ 64) :
    h.drop (184385 + ts.length) = out := by
  obtain ⟨hlen, hw⟩ := r
  apply List.ext_getElem
  · simp [hlen]; omega
  · intro i h1 h2
    have e := hw i h2
    have hi : 184384 + ts.length + 1 + i < 2 ^ 64 := by simp at h1; omega
    rw [← e]
    have hn : (UInt64.ofNat (184384 + ts.length + 1 + i)).toNat = 184385 + ts.length + i := by
      simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi]; omega
    simp only [List.getElem_drop, bget, List.getD, Nat.toUInt64, hn]
    rw [List.getElem?_eq_getElem (show 184385 + ts.length + i < h.length by simp at h1; omega)]
    rfl

theorem ntasks_of {h : Buf} {arena : List RN} {fs : List Frame} (r : TasksRep h arena fs) : (bget h 5 = 0 ↔ fs = []) := by
  obtain ⟨h5, _, _⟩ := r
  constructor
  · intro e; rw [e] at h5; simp at h5; exact List.length_eq_zero_iff.mp h5.symm
  · intro e; subst e; apply UInt64.toNat_inj.mp; simpa using h5

end ParInv
