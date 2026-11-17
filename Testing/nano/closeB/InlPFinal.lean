/- The inliner stage compiled by OUR paged front end (`wp_compile`, branch `nano-closeB`), with its machine theorem
in the linker's form: `Nano.IP.inlP_implements` (work space `8192 · 601` bytes, inputs up to `2^20` bytes, result
length in `a1`) and `inlP_code_len`.  With `inlP_eq` (`Nano/InlPProof.lean`) the stage computes `inlB` on every input
whose inliner table fits (`inlFits`).  Slow (~30+ min); needs a large thread stack (`--tstack`, lakefile). -/
import Nano.InlPProof
import Nano.PgStage
import Riscv.Frontx.WpBridge

namespace Nano.IP
open Proven Proven.WA Proven.WP Proven.Top.Alloc

set_option maxHeartbeats 0 in
wp_compile inlP max 1048576
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

/-- **the compiled inliner stage**: `Implements1With` in the linker's form -/
theorem inlP_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) inlP.pg.body (fun xs => (inlP xs).toList)
      (fun _ => 8192 * (600 + 1)) (2 ^ 20) true :=
  Nano.Link.pg_stage inlP.wa 1048576 _ inlP.pgGood inlP inlP.goodE 600 fun xs _ y E h => inlP_pk xs y E h

set_option maxRecDepth 100000 in
theorem inlP_code_len : inlP.pg.body.length < 2 ^ 17 := by decide +kernel

/-- the stage's equation in the form `selfHosted_parseB` takes -/
theorem inlP_hfi (x : List UInt8) (h : inlFits x) : (fun xs => (inlP xs).toList) (Nano.Link.ofL x) = Nano.U.inlB x :=
  inlP_eq x h

end Nano.IP
