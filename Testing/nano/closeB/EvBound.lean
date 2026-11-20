import Legacy.Nano.InlP
import Legacy.Riscv.Frontx.WpCmd
import Legacy.Riscv.Frontx.WpBridge
namespace Nano.IP
open Proven Proven.WA Proven.WP Proven.Top.Alloc

wp_compile inlP reflect_only max 1048576
  invariant fun (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat) =>
    ob.size = 327680 ∧ i ≤ src.size ∧ src.size < 2 ^ 32 ∧ ph ≤ 1 ∧ m < 256 ∧ w ≤ 262136 ∧ n ≤ i ∧ hi < 256 ∧
      cp + rem ≤ 524272 ∧ rem ≤ 262136 ∧ cs ≤ 262136
  measure fun (_ob : Array Nat) (src : ByteArray) (i _ph _m _w _n _hi _cp rem _cs : Nat) =>
    (src.size - i) * 262137 + rem
  invariant fun (out : Array UInt8) (_ob : Array Nat) (t ls len k : Nat) =>
    out.size = 20 * k + len + 38 ∧ t ≤ 20 * k + len + 38 ∧ ls < 16777216 ∧ len < 262144 ∧ k < 256
  measure fun (_out : Array UInt8) (_ob : Array Nat) (t ls len k : Nat) => 20 * k + len + 38 - t

theorem runsE_nil {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r : R.T}
    {E : List MemEvent} (h : RunsE b c s r E) (hp : b.PushFree) : E = [] := by
  induction h with
  | ret _ => rfl
  | call _ _ ih => rw [T.evs_nil _ _ hp, ih]; rfl

theorem pk2 (a b : Nat) :
    pk 0 (MemEvent.alloc 1 :: pushEvs a ++ MemEvent.alloc 1 :: pushEvs b) = 2 + npages a + npages b := by
  rw [(PgEx.pk_allocs _ 0 (by
    intro e he
    simp only [List.mem_append, List.mem_cons] at he
    rcases he with (rfl | he) | (rfl | he)
    · exact ⟨1, rfl⟩
    · exact PgEx.pushFrom_allocs 0 _ e he
    · exact ⟨1, rfl⟩
    · exact PgEx.pushFrom_allocs 0 _ e he)).1]
  simp only [List.cons_append, finE, stepE, finE_append, pushEvs, finE_pushFrom]
  simp [npages, P]; omega

theorem inlP_pk (xs : ByteArray) (y : Array UInt8) (E : List MemEvent)
    (h : inlP.wa.GoodE [inLocP] 9 (xs, ()) y E) : pk 0 E ≤ 600 := by
  simp only [inlP.wa, Pg.GoodE] at h
  obtain ⟨-, r, P1, Eb, Ek, -, -, -, hrun, hk, rfl⟩ := h
  rw [runsE_nil hrun (by simp [T.PushFree, Args.PushFree, A.PushFree])]
  obtain ⟨-, E2, hk, rfl⟩ := hk
  obtain ⟨-, E3, hk, rfl⟩ := hk
  obtain ⟨-, E4, hk, rfl⟩ := hk
  obtain ⟨-, E5, hk, rfl⟩ := hk
  obtain ⟨-, r2, P2, Eb2, Ek2, -, -, -, hrun2, hk, rfl⟩ := hk
  rw [runsE_nil hrun2 (by simp [T.PushFree, Args.PushFree, A.PushFree])]
  obtain ⟨-, rfl⟩ := hk
  simp only [Inis.evsP, Ini.evsP, F.evsP, List.append_nil, List.nil_append]
  rw [pk2]
  wp_dsimp
  unfold npages P
  split <;> omega

end Nano.IP
