/- Nano/Ownership/OwnP23: `o15` does not read register 5 (the done flag). -/
import Nano.Ownership.OwnP22
namespace OwnP
open C OwnSpec ParSpec

/-- equal except at register 5 -/
def Ag (s s' : Buf) : Prop := s.length = s'.length ∧ ∀ k, k ≠ 5 → s.getD k 0 = s'.getD k 0

theorem ag_get {s s' : Buf} (h : Ag s s') {k : UInt64} (hk : k.toNat ≠ 5) : bget s k = bget s' k := h.2 _ hk

theorem ag_set {s s' : Buf} (h : Ag s s') (i x : UInt64) : Ag (bset s i x) (bset s' i x) := by
  refine ⟨by simp [bset, h.1], fun k hk => ?_⟩
  simp only [bset]; rw [getD_set, getD_set, h.1, h.2 k hk]

theorem ag_o7 {s s' : Buf} (h : Ag s s') (f : Buf) (x : UInt64) : o7 s f x = o7 s' f x := by
  unfold o7; rw [ag_get h (k := 6) (by decide)]

theorem o15_ag : ∀ (n : Nat) (s s' f v : Buf) (q b : UInt64), Ag s s' →
    Ag (o15 n s f v q b).1 (o15 n s' f v q b).1 ∧ (o15 n s f v q b).2 = (o15 n s' f v q b).2 := by
  intro n; induction n with
  | zero => intro s s' f v q b h; simp only [o15]; exact ⟨ag_set (ag_set h _ _) _ _, trivial⟩
  | succ n ih =>
    intro s s' f v q b h
    rw [o15, o15]
    simp only [ag_get h (k := 8) (by decide), ag_get h (k := 2) (by decide), ag_get h (k := 6) (by decide), ag_o7 h]
    repeat' (split <;> rename_i hc <;> try simp only [hc])
    all_goals first
      | exact ih _ _ _ _ _ _ h
      | exact ih _ _ _ _ _ _ (ag_set h _ _)
      | exact ⟨ag_set h _ _, trivial⟩
      | exact ⟨h, trivial⟩
      | exact ⟨ag_set h _ _, rfl⟩
      | exact ⟨h, rfl⟩

end OwnP
