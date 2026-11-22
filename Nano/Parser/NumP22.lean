/- Nano/Parser/NumP22: `marked` (membership, one round at a time; invariant under permutation of the groups) and the
marking buffers of the machine's rounds. -/
import Nano.Parser.NumP21
namespace NumP
open C ParSpec OwnP

/-- one round of `marked` -/
def mstep (d : Nat) (gs : List NumSpec.G) (m : List Nat) : List Nat :=
  m ++ (gs.filter fun g => g.d == d || g.vs.any m.contains).flatMap (·.vs)

theorem marked_succ (d : Nat) (gs : List NumSpec.G) : ∀ (k : Nat) (m : List Nat),
    NumSpec.marked d gs (k + 1) m = mstep d gs (NumSpec.marked d gs k m)
  | 0, m => rfl
  | k + 1, m => by
    show NumSpec.marked d gs (k + 1) (mstep d gs m) = mstep d gs (NumSpec.marked d gs (k + 1) m)
    rw [marked_succ d gs k (mstep d gs m)]
    show mstep d gs (NumSpec.marked d gs k (mstep d gs m)) = mstep d gs (NumSpec.marked d gs k (mstep d gs m))
    rfl

theorem mem_mstep (d : Nat) (gs : List NumSpec.G) (m : List Nat) (v : Nat) :
    v ∈ mstep d gs m ↔ v ∈ m ∨ ∃ g ∈ gs, (g.d = d ∨ ∃ w ∈ g.vs, w ∈ m) ∧ v ∈ g.vs := by
  simp [mstep]
  constructor
  · rintro (h | ⟨g, ⟨hg, hc⟩, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨g, hg, hc, hv⟩
  · rintro (h | ⟨g, hg, hc, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨g, ⟨hg, hc⟩, hv⟩

/-- membership in `marked` only depends on the groups as a set -/
theorem marked_perm (d : Nat) {X gs : List NumSpec.G} (hp : X.Perm gs) : ∀ (k : Nat) (v : Nat),
    v ∈ NumSpec.marked d X k [] ↔ v ∈ NumSpec.marked d gs k []
  | 0, v => Iff.rfl
  | k + 1, v => by
    rw [marked_succ, marked_succ, mem_mstep, mem_mstep]
    have ih := marked_perm d hp k
    constructor
    · rintro (h | ⟨g, hg, hc, hv⟩)
      · exact Or.inl ((ih v).1 h)
      · refine Or.inr ⟨g, hp.subset hg, ?_, hv⟩
        rcases hc with hc | ⟨w, hw, hm⟩
        · exact Or.inl hc
        · exact Or.inr ⟨w, hw, (ih w).1 hm⟩
    · rintro (h | ⟨g, hg, hc, hv⟩)
      · exact Or.inl ((ih v).2 h)
      · refine Or.inr ⟨g, hp.symm.subset hg, ?_, hv⟩
        rcases hc with hc | ⟨w, hw, hm⟩
        · exact Or.inl hc
        · exact Or.inr ⟨w, hw, (ih w).2 hm⟩

/-- the per-group rule of `numOkD` -/
def gspec (um nm : List Nat) (g : NumSpec.G) : Bool :=
  let isU := g.d == 1 || g.vs.any um.contains
  let isN := g.d == 2 || g.vs.any nm.contains
  !(isU && isN) && !(g.ar && !isU)

theorem gspec_congr {um nm um' nm' : List Nat} (hu : ∀ v, v ∈ um ↔ v ∈ um') (hn : ∀ v, v ∈ nm ↔ v ∈ nm')
    (g : NumSpec.G) : gspec um nm g = gspec um' nm' g := by
  have e1 : g.vs.any um.contains = g.vs.any um'.contains := by
    apply Bool.eq_iff_iff.2; simp [hu]
  have e2 : g.vs.any nm.contains = g.vs.any nm'.contains := by
    apply Bool.eq_iff_iff.2; simp [hn]
  simp only [gspec, e1, e2]

/-- the class rule over X is the class rule over any permutation of it -/
theorem all_perm {X gs : List NumSpec.G} (hp : X.Perm gs) (N : Nat) :
    X.all (gspec (NumSpec.marked 1 X N []) (NumSpec.marked 2 X N [])) = true →
    gs.all (gspec (NumSpec.marked 1 gs N []) (NumSpec.marked 2 gs N [])) = true := by
  intro h
  simp only [List.all_eq_true] at h ⊢
  intro g hg
  rw [← gspec_congr (marked_perm 1 hp N) (marked_perm 2 hp N)]
  exact h g (hp.symm.subset hg)

end NumP
