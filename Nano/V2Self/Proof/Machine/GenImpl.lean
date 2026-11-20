/- Opus box E: **Gen's code implements `Sem`** (`gen_implements`): the four host lifts (success, capacity, out of memory,
tiny work block) assembled into `ImplementsCW`, given the semantic case split `HD` that D's converse bridge provides
(for each input and work size: Sem ok and semAt succeeds, or Sem cap and the kinded semantics fails with cap, or the
kinded semantics fails with room below the work bound `R x`). -/
import Nano.V2Self.Proof.Machine.HostTiny
import Nano.V2Self.Proof.Machine.SemCases
namespace SimW
open Proven Nano.V2B Templates CallProbe C GenRef ParSpec

theorem gen_implements (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (R : List UInt8 → Nat)
    (HD : ∀ x, x.length ≤ 2 ^ 20 → ∀ wb wl, wb % 8 = 0 → 2 ^ 31 ≤ wb → wb + wl ≤ 2 ^ 32 →
      wb + 16 ≤ (wb + wl) / 8 * 8 → SemCases p R x wb wl) :
    NanoMain.ImplementsCW (g41 c (serialize p)) (NanoMain.Sem NanoMain.κC p) (fun x => max 16 (R x)) := by
  intro x s entry ra input output work codeR hxl hc hpc he4 _ hB h10 h11 h12 h13 h2 h1 hra4 _ hin hil hout hw8 hram hdis
    hMo hMw
  have rW := hram work (by simp)
  simp only [Region.inRAM] at rW
  by_cases hsm : (work.base + work.len) / 8 * 8 < work.base + 16
  · exact gen_host_tiny c hP Ks hO hK2 hXl h hdb x s entry ra input output work _ hxl hc hpc he4 hB h10 h11 h12 h13
      h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw hsm (Nat.lt_of_lt_of_le (by omega) (Nat.le_max_left 16 (R x))) _
  rcases HD x hxl work.base work.len hw8 rW.1 rW.2 (by omega) with ⟨y, -, hS⟩ | ⟨hSem, hS⟩ | ⟨hS, hlt⟩
  · exact gen_host c hP Ks hO hK2 hXl h hdb x s entry ra input output work _ hxl hc hpc he4 hB h10 h11 h12 h13
      h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw (by omega) hS
  · exact gen_host_cap c hP Ks hO hK2 hXl h hdb x s entry ra input output work _ hxl hc hpc he4 hB h10 h11 h12 h13
      h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw (by omega) hSem hS
  · exact gen_host_oom c hP Ks hO hK2 hXl h hdb x s entry ra input output work _ hxl hc hpc he4 hB h10 h11 h12 h13
      h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw (by omega) (Nat.lt_of_lt_of_le hlt (Nat.le_max_right 16 (R x))) hS

end SimW
