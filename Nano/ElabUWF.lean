/- nano: what the non-inlined elaboration produces is well formed (`Nano.U.WF`, `Nano/SerU.lean`): bodies scoped in
their parameters, every call to an earlier def with the right number of arguments (integration, nano-int).
`nanoElabU_wf`; the two size conditions (arities < 256, at most 65536 defs) stay hypotheses (they belong to the
domain `D` of the target).  With `genR_chain`: **`chain_eq`**, the Lean-level equation of the whole staged compiler. -/
import Nano.SerU

namespace Nano.U
open Nano

theorem idx_lt (g : List UInt8) : ∀ (sc : List (List UInt8)) (i0 i : Nat), idx g sc i0 = some i → i < i0 + sc.length
  | [], _, _, h => by simp [idx] at h
  | t :: ts, i0, i, h => by
    simp only [idx] at h
    split at h
    · cases h; simp
    · have := idx_lt g ts (i0 + 1) i h; simp only [List.length_cons]; omega

/-- the marker table: every body is the marker of a def with that arity -/
def TG (ar : List Nat) (ds : Defs) : Prop :=
  ∀ g k b, findDef g ds = some (k, b) → ∃ j, b = Ex.var j ∧ ar[j]? = some k

/-- **what the parser functions return is well formed** -/
theorem pwf (ar : List Nat) (ds : Defs) (htg : TG ar ds) (hlen : ar.length ≤ 65536) : ∀ f : Nat,
    (∀ sc ts e r, pExpr f sc ds ts = some (e, r) → WU ar e sc.length = true) ∧
    (∀ sc acc ts e r, pAdd f sc ds acc ts = some (e, r) → WU ar acc sc.length = true → WU ar e sc.length = true) ∧
    (∀ sc ts e r, pMul f sc ds ts = some (e, r) → WU ar e sc.length = true) ∧
    (∀ sc acc ts e r, pMulT f sc ds acc ts = some (e, r) → WU ar acc sc.length = true →
      WU ar e sc.length = true) ∧
    (∀ sc ts e r, pApp f sc ds ts = some (e, r) → WU ar e sc.length = true) ∧
    (∀ sc k ts e r, pArgs f sc ds k ts = some (e, r) → WUA ar e sc.length = true ∧ cnt e = k) ∧
    (∀ sc ts e r, pAtom f sc ds ts = some (e, r) → WU ar e sc.length = true)
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [pExpr, pAdd, pMul, pMulT, pApp, pArgs, pAtom]
  | f + 1 => by
    obtain ⟨hE, hA, hM, hT, hP, hG, hO⟩ := pwf ar ds htg hlen f
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro sc ts e r h
      unfold pExpr at h
      split at h
      · rename_i h0; cases h0
      · rename_i h0; cases h0
        split at h
        · rename_i v r1 h1
          split at h
          · rename_i b r2 h2
            cases h
            simp only [WU, Bool.and_eq_true]
            exact ⟨hE _ _ _ _ h1, by simpa using hE _ _ _ _ h2⟩
          · cases h
        · cases h
      · rename_i h0 _; cases h0
        split at h
        · rename_i v r1 h1; exact hA _ _ _ _ _ h (hM _ _ _ _ h1)
        · cases h
    · intro sc acc ts e r h hacc
      unfold pAdd at h
      split at h
      · rename_i h0; cases h0
      · rename_i h0; cases h0
        split at h
        · rename_i v r1 h1
          exact hA _ _ _ _ _ h (by simp only [WU, Bool.and_eq_true]; exact ⟨hacc, hM _ _ _ _ h1⟩)
        · cases h
      · rename_i h0; cases h0
        split at h
        · rename_i v r1 h1
          exact hA _ _ _ _ _ h (by simp only [WU, Bool.and_eq_true]; exact ⟨hacc, hM _ _ _ _ h1⟩)
        · cases h
      · cases h; exact hacc
    · intro sc ts e r h
      simp only [pMul] at h
      split at h
      · rename_i v r1 h1; exact hT _ _ _ _ _ h (hP _ _ _ _ h1)
      · cases h
    · intro sc acc ts e r h hacc
      unfold pMulT at h
      split at h
      · rename_i h0; cases h0
      · rename_i h0; cases h0
        split at h
        · rename_i v r1 h1
          exact hT _ _ _ _ _ h (by simp only [WU, Bool.and_eq_true]; exact ⟨hacc, hP _ _ _ _ h1⟩)
        · cases h
      · cases h; exact hacc
    · intro sc ts e r h
      unfold pApp at h
      split at h
      · rename_i h0; cases h0
      · rename_i h0; cases h0
        split at h
        · rename_i i hi
          cases h
          have := idx_lt _ _ _ _ hi
          simp only [WU, decide_eq_true_eq]; omega
        · split at h
          · rename_i k b hfd
            split at h
            · rename_i as r1 hpa
              cases h
              obtain ⟨j, rfl, hj⟩ := htg _ _ _ hfd
              obtain ⟨hwa, hc⟩ := hG _ _ _ _ _ hpa
              have hjl : j < ar.length := (List.getElem?_eq_some_iff.1 hj).1
              simp only [WU, Bool.and_eq_true, decide_eq_true_eq, hc]
              exact ⟨⟨hwa, hj⟩, by omega⟩
            · cases h
          · cases h
      · cases h; simp only [WU]
      · rename_i h0 _ _; cases h0
        exact hO _ _ _ _ h
    · intro sc k ts e r h
      unfold pArgs at h
      split at h
      · rename_i h0; cases h0
      · cases h; simp only [WUA, cnt, and_self]
      · rename_i h0; cases h0
        split at h
        · rename_i e1 r1 h1
          split at h
          · rename_i es r2 h2
            cases h
            obtain ⟨hwa, hc⟩ := hG _ _ _ _ _ h2
            simp only [WUA, Bool.and_eq_true, cnt, hc, and_true]
            exact ⟨hO _ _ _ _ h1, hwa⟩
          · cases h
        · cases h
    · intro sc ts e r h
      unfold pAtom at h
      split at h
      · cases h
      · cases h; simp only [WU]
      · split at h
        · rename_i i hi
          cases h
          have := idx_lt _ _ _ _ hi
          simp only [WU, decide_eq_true_eq]; omega
        · split at h
          · rename_i b hfd
            cases h
            obtain ⟨j, rfl, hj⟩ := htg _ _ _ hfd
            have hjl : j < ar.length := (List.getElem?_eq_some_iff.1 hj).1
            simp only [WU, WUA, cnt, Bool.and_eq_true, decide_eq_true_eq, true_and]
            exact ⟨hj, by omega⟩
          · cases h
      · rename_i h0; cases h0
        split at h
        · rename_i e1 r1 h1; cases h; exact hE _ _ _ _ h1
        · cases h
      · cases h

/-! ## programs -/

mutual
theorem pParams_len : ∀ (f : Nat) (sc : List (List UInt8)) (n : Nat) (ts : List Tok) (sc' : List (List UInt8))
    (n' : Nat) (r : List Tok), pParams f sc n ts = some (sc', n', r) → sc.length = n → sc'.length = n'
  | 0, _, _, _, _, _, _, h, _ => by simp [pParams] at h
  | f + 1, sc, n, ts, sc', n', r, h, hl => by
    unfold pParams at h
    split at h
    · rename_i h0; cases h0
    · rename_i h0; cases h0
      split at h
      · rename_i sc2 n2 r2 h1
        exact pParams_len f _ _ _ _ _ _ h (pNames_len f _ _ _ _ _ _ h1 hl)
      · cases h
    · cases h; exact hl
theorem pNames_len : ∀ (f : Nat) (sc : List (List UInt8)) (n : Nat) (ts : List Tok) (sc' : List (List UInt8))
    (n' : Nat) (r : List Tok), pNames f sc n ts = some (sc', n', r) → sc.length = n → sc'.length = n'
  | 0, _, _, _, _, _, _, h, _ => by simp [pNames] at h
  | f + 1, sc, n, ts, sc', n', r, h, hl => by
    unfold pNames at h
    split at h
    · rename_i h0; cases h0
    · rename_i h0; cases h0
      exact pNames_len f _ _ _ _ _ _ h (by simp [hl])
    · cases h; exact hl
    · cases h
end

/-- the result extends the defs read so far -/
theorem pDefsU_ext : ∀ (f : Nat) (ds : Defs) (acc : List (Nat × Ex)) (ts : List Tok) (u : List (Nat × Ex)),
    pDefsU f ds acc ts = some u → (∀ d ∈ acc, d ∈ u) ∧ acc.length < u.length
  | 0, _, _, _, _, h => by simp [pDefsU] at h
  | f + 1, ds, acc, ts, u, h => by
    unfold pDefsU at h
    split at h
    · rename_i h0; cases h0
    · rename_i h0; cases h0
      split at h
      · split at h
        · cases h; exact ⟨fun d hd => List.mem_cons_of_mem _ hd, by simp⟩
        · have := pDefsU_ext f _ _ _ _ h
          exact ⟨fun d hd => this.1 d (List.mem_cons_of_mem _ hd), by have := this.2; simp at this; omega⟩
        · cases h
      · cases h
    · cases h

theorem pDefsU_wf : ∀ (f : Nat) (ds : Defs) (acc : List (Nat × Ex)) (ts : List Tok) (u : List (Nat × Ex)),
    pDefsU f ds acc ts = some u → TG (arities acc) ds → WF acc = true → (∀ d ∈ u, d.1 < 256) → u.length ≤ 65536 →
    WF u = true
  | 0, _, _, _, _, h, _, _, _, _ => by simp [pDefsU] at h
  | f + 1, ds, acc, ts, u, h, htg, hwf, hb, hl => by
    have hext := pDefsU_ext (f + 1) ds acc ts u h
    have hla := length_arities acc
    unfold pDefsU at h
    split at h
    · rename_i h0; cases h0
    · rename_i h0; cases h0
      rename_i g ts'
      split at h
      · rename_i sc n s r hp
        have hsc : sc.length = n := pParams_len f [] 0 _ _ _ _ hp rfl
        split at h
        · rename_i e hin
          cases h
          split at hin
          · cases hin
          · have hw := (pwf _ _ htg (by rw [hla]; have := hl; simp only [List.length_cons] at this; omega) f).1 _ _ _ _ hin
            rw [hsc] at hw
            simp only [WF, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨hwf, hw⟩, hb _ (List.mem_cons_self ..)⟩
        · rename_i e r2 _ hin
          have hext2 := pDefsU_ext f _ _ _ _ h
          split at hin
          · cases hin
          · have hw := (pwf _ _ htg (by rw [hla]; have := hext2.2; simp only [List.length_cons] at this; omega) f).1 _ _ _ _ hin
            rw [hsc] at hw
            refine pDefsU_wf f _ _ _ _ h ?_ ?_ hb hl
            · intro g' k b hfd
              simp only [findDef] at hfd
              split at hfd
              · cases hfd
                exact ⟨_, rfl, by simp [arities, ← hla]⟩
              · obtain ⟨j, hj, hjk⟩ := htg _ _ _ hfd
                refine ⟨j, hj, ?_⟩
                simp only [arities]
                rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hjk).1]; exact hjk
            · simp only [WF, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨hwf, hw⟩, hb _ (hext2.1 _ (List.mem_cons_self ..))⟩
        · cases h
      · cases h
    · cases h

/-- **the non-inlined elaboration is well formed** (given the two size conditions) -/
theorem nanoElabU_wf (xs : List UInt8) (u : List (Nat × Ex)) (h : nanoElabU xs = some u)
    (hb : ∀ d ∈ u, d.1 < 256) (hl : u.length ≤ 65536) : WF u = true ∧ u ≠ [] := by
  unfold nanoElabU at h
  split at h
  · split at h
    · exact ⟨pDefsU_wf _ _ _ _ _ h (fun g k b hfd => by simp [findDef] at hfd) rfl hb hl, by
        have := (pDefsU_ext _ _ _ _ _ h).2; intro hn; rw [hn] at this; simp at this⟩
    · cases h
  · cases h

/-- **the staged compiler, in Lean**: for an accepted source, the code the spec defines (`nanoGen p = asm (genR p)`)
is `asm` after the expander `mexp` after the inliner `inlB`, applied to the NON-inlined stream `serU u` of the
non-inlined elaboration `u` -/
theorem chain_eq (xs : List UInt8) (p : Prog) (hp : nanoElab xs = some p) :
    ∃ u, nanoElabU xs = some u ∧
      ((∀ d ∈ u, d.1 < 256) → u.length ≤ 65536 → asm (mexp (inlB (serU u))) = nanoGen p) := by
  have h := hp
  rw [nanoElab_eq] at h
  cases hu : nanoElabU xs with
  | none => rw [hu] at h; cases h
  | some u =>
    refine ⟨u, rfl, fun hb hl => ?_⟩
    obtain ⟨hw, hne⟩ := nanoElabU_wf xs u hu hb hl
    rw [genR_chain xs p u hu hp hw hne]; rfl

end Nano.U
