/- Nano/V2Self/Proof/ParRunExpr: Layer 2 → ParSpec for EXPRESSIONS (box B).  Frame inversions and the binary-operator loop. -/
import Nano.V2Self.Proof.ParRunAtom
import Nano.V2Self.Proof.ParTreeOK
import Nano.V2Self.Proof.ParSpecTail
namespace ParRun
open ParSpec

/-- the deferred validation (v209 at the next `defs`) holds for every node of `v` -/
def VT (ds : List DefR) (v : RN) : Prop := ∀ u ∈ nodes v, nodeOK ds u = true

/-- the effect of an expression-like run on the state: one value replaces `base`'s top part; tables unchanged -/
structure Post (st st' : St) (base : List RN) (v : RN) : Prop where
  vals : st'.vals = v :: base
  binds : st'.binds = st.binds
  defs : st'.defs = st.defs
  cur : st'.cur = st.cur
  arm : st'.arm = st.arm
  all : st'.all = st.all
  toks : st'.toks.length ≤ st.toks.length
  nx : st.nx ≤ st'.nx

theorem binLoop_inv {m st k st'} (h : stepF (.binLoop m) st = some (k, st')) :
    (k = [] ∧ st' = st ∧ ∀ t r op p, st.toks = .k t :: r → opInfo t = some (op, p) → p < m) ∨
    (∃ t r op p top rest, st.toks = .k t :: r ∧ opInfo t = some (op, p) ∧ m ≤ p ∧ st.vals = top :: rest ∧ top.pend = false ∧
      st' = { st with toks := r } ∧
      ((t = 28 ∨ t = 29) ∧ k = [.shiftNum op, .binLoop m] ∨ ¬(t = 28 ∨ t = 29) ∧ k = [.expr (p + 1) 2, .mkBin op, .binLoop m])) := by
  simp only [stepF] at h
  split at h
  · rename_i t r ht
    split at h
    · rename_i hop
      simp at h; obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl, fun t' r' op p he ho => by rw [ht] at he; cases he; rw [hop] at ho; cases ho⟩
    · rename_i op p hop
      split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨rfl, rfl, fun t' r' op' p' he ho => by rw [ht] at he; cases he; rw [hop] at ho; cases ho; assumption⟩
      · rename_i hp
        split at h
        · rename_i top rest hv
          split at h
          · simp at h
          · rename_i hpend
            split at h
            · simp at h; obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨t, r, op, p, top, rest, ht, hop, by omega, hv, by simpa using hpend, rfl, Or.inl ⟨by assumption, rfl⟩⟩
            · simp at h; obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨t, r, op, p, top, rest, ht, hop, by omega, hv, by simpa using hpend, rfl, Or.inr ⟨by assumption, rfl⟩⟩
        · simp at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h
    rename_i hne
    exact Or.inl ⟨rfl, rfl, fun t r op p he _ => absurd he (hne t r)⟩

end ParRun
