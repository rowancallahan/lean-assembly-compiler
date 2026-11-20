/- Machine bridge (Opus box E): the J-level program theorem.
`gen_words`: if Gen succeeds on the serialized resolved program `ds`, the code after the def phase is the stub code
followed by the def templates (`defsJ`), def k at its table start word.
`gen_defs_run`: on any J program holding those templates, every def satisfies its contract `DefX` for `semAt` (the
machine-level semantics of the program) — in particular main.  Remaining for the full chain: the start code (g35:
needs J's srli/bne/sb), the Sail lift (Safe runs), side conditions from the parser + g53. -/
import Nano.V2Self.Proof.Machine.NdProgW
namespace Templates
open CallProbe C GenRef ParSpec

theorem SerAt_serialize (ds : List DefA) : SerAt (serialize ds) 1 (ds.flatMap DefA.ser) := by
  intro j hj
  simp only [serialize, tg, List.getD_eq_getElem?_getD]
  rw [show 1 + j = j + 1 by omega, List.getElem?_cons_succ]

theorem At_defsJ {C : List J} {P : PC} {ds : List DefA} : ∀ (n k h : Nat), At C h (defsJ P ds k n) →
    (∀ j, j < n → P.T (k + j) = h + (defsJ P ds k j).length) →
    ∀ j, j < n → At C (P.T (k + j)) (defT (scAt P ds (k + j)) (dA ds (k + j)).body (P.T (k + j)) (dA ds (k + j)).nres)
  | 0, _, _, _, _, j, hj => absurd hj (by omega)
  | n + 1, k, h, hC, hT, j, hj => by
    simp only [defsJ] at hC
    rcases j with _ | j
    · have := hT 0 (by omega); simp only [Nat.add_zero, defsJ, List.length_nil] at this ⊢
      rw [this] at hC ⊢; exact hC.left
    · have r := At_defsJ n (k + 1) _ hC.right (fun j' hj' => by
        have := hT (j' + 1) (by omega)
        rw [show k + (j' + 1) = k + 1 + j' by omega] at this
        rw [this]; simp [defsJ, Nat.add_assoc]
        try (have e := hT 0 (by omega); simp [defsJ] at e
             rw [e]; simp [defT, proA, pushA, push, tm_len, epi, copy_len]; omega)) j (by omega)
      rw [show k + (j + 1) = k + 1 + j by omega]; exact r

/-- the start-word table Gen built -/
def pcOf (κ hb : Nat) (c29 : UInt64) (inp : Nat → UInt64) (T : Buf) : PC :=
  ⟨κ, hb, c29, inp, fun j => (bget T j.toUInt64).toNat⟩

/-- **Gen's words**: on success, the def phase emitted the def templates after the stubs -/
theorem gen_words (c : List UInt8) (ds : List DefA) (hXl : (serialize ds).length < 2 ^ 31)
    (h : g41 c (serialize ds) ≠ []) (hdb : ∀ d ∈ ds, DB d) (hb : Nat) (c29 : UInt64) (inp : Nat → UInt64) :
    ∃ hs T o, DefsC (serialize ds) g_999 bnew 1 (g34 bnew) hs T (serialize ds).length o ∧ hs ≠ [] ∧
      g41 c (serialize ds) = g40 16777216 c (startW (bset o 0 (g13 0 0 (bsize o))) (bget T (bsize T - 1))) 0 [] ∧
      (o.length < 2 ^ 24 →
        o = g34 bnew ++ (defsJ (pcOf 524288 hb c29 inp T) ds 0 hs.length).map encG ∧
        ∀ j, j < hs.length → (pcOf 524288 hb c29 inp T).T j =
          (g34 bnew).length + (defsJ (pcOf 524288 hb c29 inp T) ds 0 j).length) := by
  obtain ⟨_, _, hs, T, o, hD, hne, _, _, hg, -⟩ := gen41_ok c (serialize ds) hXl h
  refine ⟨hs, T, o, hD, hne, hg, fun hol => ?_⟩
  have := chainW (P := pcOf 524288 hb c29 inp T) (ds := ds) (u := g_999) rfl (Tf := T) (fun j => rfl) hD rfl ds
    (by simp [bnew]) (SerAt_serialize ds) (by simp [serialize]; omega) hdb (by simp [bnew]) (by simp [bnew]) hol
  simp [bnew] at this; exact ⟨this.1, this.2.1⟩

/-- **every def runs per its semantics** on a J program holding the def templates (Gen's words, by `gen_words`) -/
theorem gen_defs_run (P : PC) (ds : List DefA) (C : List J) (IG : St → Prop) (E0 : Nat) (c28 : UInt64) (n h : Nat)
    (hig : IGOK P.hb E0 IG) (he : E0 < 2 ^ 62) (hcb : ∀ s, IG s → s.b + s.w * C.length < 2 ^ 64)
    (hinp : InpOK IG c28 P.c29 P.inp) (hC : At C h (defsJ P ds 0 n))
    (hT : ∀ j, j < n → P.T j = h + (defsJ P ds 0 j).length)
    (hd : ∀ k, k < n → (dA ds k).npw < 2 ^ 20 ∧ (dA ds k).npw ≤ (dA ds k).nslots ∧ OkV (scAt P ds k) (dA ds k).body ∧
      wd (scAt P ds k) (dA ds k).body = (dA ds k).nres ∧ ∀ j, rd (dA ds k).body j → j < (dA ds k).npw) :
    ∀ k, k < n → DefX C (P.T k) (dA ds k).npw (dA ds k).nres IG P.hb E0 (semAt P ds k) := by
  apply progRun P ds C IG E0 c28 hig he hcb hinp n
  intro k hk
  obtain ⟨a1, a2, a3, a4, a5⟩ := hd k hk
  have := At_defsJ n 0 h hC (fun j hj => by rw [Nat.zero_add]; exact hT j hj) k hk
  rw [Nat.zero_add] at this
  exact ⟨a1, a2, a3, a4, a5, this⟩

end Templates
