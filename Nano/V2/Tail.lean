import Nano.V2.Blocks
/- nano v2 small backend: loop-body tails (`Tl.ret` / `Tl.next`): slide the value over the frame part, then jump;
the outcome `JPost` feeds `loop_ok`'s `BOut` (exit = `ret r`, head = `next s'`). -/
namespace Nano.V2B

/-- the outcome of a loop-body tail: the jump `t` with the stack `L ++ vs`, or out of memory -/
def JPost (c : Cfg) (s : St) (h : Nat) (L vs : List UInt64) (t : Tg) : Res → Prop
  | .ok _ => False
  | .jmp t' s' => (t' = t ∧ Stk c s' h (L ++ vs) ∧ Keep s s') ∨ t' = .oom

/-- **`ret`/`next` tails** (per-construct lemma): the value `C` pushed over the frame part `B`, slid down over it,
then the jump (`exit` for `ret r`, `head` for `next s'`) -/
theorem tail_node {c : Cfg} {a : SC} {s : St} {h : Nat} {A B C : List UInt64} (hc : c.Good) (hs : Stk c s h (A ++ B))
    (hm : B.length ≤ 255) (hk : C.length ≤ 255) (t : Tg)
    (ha : ∃ r, SC.Ex c a s r ∧ Post c s h (A ++ B) C r) :
    ∃ r, SC.Ex c (.seq (.seq a (.ins (slide C.length B.length))) (.jmp t)) s r ∧ JPost c s h A C t r := by
  obtain ⟨r, e, p⟩ := ha
  cases r with
  | jmp t' s2 => exact ⟨_, .seqJ (.seqJ e), .inr p⟩
  | ok s2 =>
    obtain ⟨hs2, k2⟩ := p
    obtain ⟨s3, e3, hs3, k3⟩ := slide_ok hc A B C s2 (by simpa using hs2) hm hk
    exact ⟨_, .seq (.seq e (.ins e3)) .jmp,
      .inl ⟨rfl, hs3, k2.trans k3 (by apply UInt64.toNat.inj; rw [hs2.hp, hs.hp])⟩⟩

end Nano.V2B
