/- Nano/V2Self/Proof/ParInvAppend: `rep_append` — Rep survives an output append `H ++ ws` (box C, for the parser lead's tasks 80–83).
Every cell Rep reads lies below |H| (the IRV word d11 + |ts| + 1 is the first output word, so |out| ≥ 1); the token frame lemmas
need only `TokAgreeN` (cells below 184386 + h[7]). -/
import Nano.V2Self.Proof.ParInvFlatM
import Nano.V2Self.Proof.ParInvExpr
namespace ParInv
open C BufL ParSpec ParRun

theorem rep_append {H ts : Buf} {st : St} {fs : List Frame} (r : Rep H ts st fs) (ws : List UInt64) :
    Rep (H ++ ws) ts { st with out := st.out ++ ws } fs := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds r
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  obtain ⟨rl, rd⟩ := rO
  have h7 : (bget H 7).toNat = ts.length := by rw [rT.2.2.2]; simp; omega
  have hout : 1 ≤ st.out.length := by
    rcases Nat.eq_zero_or_pos st.out.length with hz' | hp
    · have := rT.2.2.1
      have hi : (d11 + ts.length.toUInt64 + 1).toNat = 184385 + ts.length := by rw [d11a1 _ (by simp; omega)]; simp; omega
      rw [show bget H (d11 + ts.length.toUInt64 + 1) = 0 by
        simp only [bget, List.getD_eq_getElem?_getD]; rw [List.getElem?_eq_none (by rw [hi]; omega)]; rfl] at this
      exact absurd this (by decide)
    · omega
  have e : ∀ i : UInt64, i.toNat < 184385 + ts.length + 1 → bget (H ++ ws) i = bget H i :=
    fun i hi => bget_append_lt _ _ _ (by omega)
  have et : TokAgreeN H (H ++ ws) := ⟨e 7 (by simp only [show (7 : UInt64).toNat = 7 from rfl]; omega), fun i _ b => e i (by omega)⟩
  have es : ShTabAgree H (H ++ ws) := fun i _ b => e i (by omega)
  have ea : ArenaAgree H (H ++ ws) := fun i _ b => e i (by omega)
  have c : ∀ n : UInt64, n.toNat < 64 → bget (H ++ ws) n = bget H n := fun n hn => e n (by omega)
  refine ⟨tokensAt_frameN rT et rts, rts, by rw [c 0 (by decide)]; exact r0, by rw [c 3 (by decide)]; exact tokAt_frameN et hn7 r3,
    by rw [c 11 (by decide)]; exact r11,
    binds_frameN rB (c 4 (by decide)) (fun i _ b => e i (by omega)) et hn7 es,
    defs_frameN rD (c 12 (by decide)) (c 27 (by decide)) (c 26 (by decide)) (fun i _ b => e i (by omega)) et hn7 es,
    arena_frame rA (c 8 (by decide)) (c 9 (by decide)) (fun i _ b => e i (by omega)) es,
    fun s hs => by rw [c 25 (by decide)]; exact (r25 s hs).frame es,
    fun x hx => by rw [c 29 (by decide)]; exact nameAt_frameN et (by omega) (r29 x hx),
    by rw [c 30 (by decide)]; exact r30, by rw [c 32 (by decide)]; exact r32, ⟨?_, ?_⟩,
    tasks_frameN rK (c 5 (by decide)) (fun i _ b => e i (by have := rK.2.1; omega)) et hn7 es ea har⟩
  · simp only [List.length_append]; omega
  · rw [List.drop_append_of_le_length (by omega), rd]
