/- The inliner's paged stage `Q` (`Nano.IR.inlQ`, Nano/InlR.lean) compiled by OUR paged front end (`wp_compileS`,
spill-first register choice), branch nano-final. -/
import Nano.InlR
import Legacy.Nano.PgStage
import Legacy.Riscv.Frontx.WpBridge
import Legacy.Nano.WpSpill

namespace Nano.IR
open Proven Proven.WA Proven.WP Proven.Top.Alloc Nano.IP

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
wp_compileS inlQ max 1048576
  invariant fun (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) =>
    ob.size = 327680 ∧ i ≤ src.size ∧ src.size ≤ 1048576 ∧ w + (src.size - i) * 65536 + rem ≤ 2 ^ 40 ∧
      cs ≤ w ∧ cp + rem ≤ 2 ^ 46
  measure fun (_ob : Array UInt64) (src : ByteArray) (i _w _cs _cp rem : Nat) => (src.size - i) * 65536 + rem
  invariant fun (out : Array UInt8) (_ob : Array UInt64) (t ls len : Nat) =>
    out.size = len ∧ t ≤ len ∧ ls < 2 ^ 40 ∧ len < 131072
  measure fun (_out : Array UInt8) (_ob : Array UInt64) (t _ls len : Nat) => len - t

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

theorem inlQ_pk (xs : ByteArray) (y : Array UInt8) (E : List MemEvent)
    (h : inlQ.wa.GoodE [inLocP] 9 (xs, ()) y E) : pk 0 E ≤ 600 := by
  simp only [inlQ.wa, Pg.GoodE] at h
  obtain ⟨-, r, P1, Eb, Ek, -, -, -, hrun, hk, rfl⟩ := h
  rw [runsE_nil hrun (by simp [T.PushFree, Args.PushFree, A.PushFree])]
  obtain ⟨-, E2, hk, rfl⟩ := hk
  obtain ⟨-, r2, P2, Eb2, Ek2, -, -, -, hrun2, hk, rfl⟩ := hk
  rw [runsE_nil hrun2 (by simp [T.PushFree, Args.PushFree, A.PushFree])]
  obtain ⟨-, rfl⟩ := hk
  simp only [Inis.evsP, Ini.evsP, F.evsP, List.append_nil, List.nil_append]
  rw [pk2]
  wp_dsimp
  unfold npages P
  (try split) <;> omega

/-- **the compiled stage `Q`**: `Implements1With` in the linker's form -/
theorem inlQ_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) inlQ.pg.body (fun xs => (inlQ xs).toList)
      (fun _ => 8192 * (600 + 1)) (2 ^ 20) true :=
  Nano.Link.pg_stage inlQ.wa 1048576 _ inlQ.pgGood inlQ inlQ.goodE 600 fun xs _ y E h => inlQ_pk xs y E h

set_option maxRecDepth 100000 in
theorem inlQ_code_len : inlQ.pg.body.length < 2 ^ 17 := by decide +kernel

#print axioms inlQ_implements

end Nano.IR
