/- Nano/V2Self/Proof/ParTreeOK: from the machine's checks to emittable trees, pure (parser lead).
* `nodes n` : all nodes of a raw tree in creation (post-)order; `ArenaInv st` : the arena is exactly the nodes of the operand trees.
* `cntOK`   : the child counts the node builders give each tag (local, per node).
* `ok_of_nodes` : every node of `n` has `cntOK` and passes the validation `nodeOK` (`v209`) ⇒ `n.ok` (ParRunFlat), hence
  `words_body : z.words = z.toNd.ser`. -/
import Nano.V2Self.Proof.ParRunFlat
namespace ParRun
open ParSpec

mutual
/-- all nodes of a tree, children first (the order `v5` allocates them) -/
def nodes : RN → List RN
  | .mk t a b s p ks => nodesL ks ++ [.mk t a b s p ks]
def nodesL : List RN → List RN
  | [] => []
  | k :: r => nodes k ++ nodesL r
end

theorem self_mem_nodes (n : RN) : n ∈ nodes n := by
  cases n; simp [nodes]

theorem nodesL_eq (ks : List RN) : nodesL ks = ks.flatMap nodes := by
  induction ks with
  | nil => simp [nodesL]
  | cons k r ih => simp [nodesL, ih]

theorem kid_nodes_sub {t a b : Nat} {s : Option Sh} {p : Bool} {ks : List RN} {k m : RN} (hk : k ∈ ks) (hm : m ∈ nodes k) :
    m ∈ nodes (.mk t a b s p ks) := by
  simp only [nodes, nodesL_eq, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨k, hk, hm⟩

/-- the arena holds exactly the nodes of the operand trees (bottom operand first) -/
def ArenaInv (st : St) : Prop := st.arena = st.vals.reverse.flatMap nodes

/-- child counts per tag, as built by `mkNode` / `leaf` / `locOf` -/
def cntOK (n : RN) : Bool :=
  if n.tag = 1 ∨ n.tag = 2 then n.kids.isEmpty
  else if n.tag = 3 ∨ n.tag = 5 ∨ n.tag = 10 then n.kids.length == 2
  else if n.tag = 4 then n.kids.length == 4
  else if n.tag = 11 then n.kids.length == 1
  else if n.tag = 6 then true
  else if n.tag = 8 then n.b == n.kids.length
  else if n.tag = 9 then true
  else false

theorem filter_len0 {ks : List RN} (h : (ks.filter RN.isInp).length = 0) : (ks.filter RN.isInp).isEmpty = true := by
  simpa using List.length_eq_zero_iff.mp h

theorem okL_of {ks : List RN} (h : ∀ k ∈ ks, k.ok = true) : RN.okL ks = true := by
  induction ks with
  | nil => rfl
  | cons k r ih => rw [RN.okL_cons, h k (by simp), ih (fun k hk => h k (by simp [hk]))]; rfl

mutual
/-- **validation ⇒ emittable**: every node has its tag's child count and passes `nodeOK` (`v209`) -/
theorem ok_of_nodes (ds : List DefR) : ∀ n : RN, (∀ m ∈ nodes n, cntOK m = true ∧ nodeOK ds m = true) → n.ok = true
  | .mk t a b s p ks => by
    intro h
    have hk : RN.okL ks = true := okL_of (kids_ok ds ks (fun k hk m hm => h m (kid_nodes_sub hk hm)))
    obtain ⟨hc, hn⟩ := h _ (self_mem_nodes _)
    simp only [cntOK, RN.tag, RN.kids, RN.b] at hc
    simp only [nodeOK, RN.tag, RN.kids, RN.a, RN.sh, Bool.and_eq_true] at hn
    have hr := hn.1
    rw [RN.ok_mk, hk, Bool.true_and]
    by_cases h12 : t = 1 ∨ t = 2
    · simpa [h12] using hc
    simp only [h12, if_false] at hc ⊢
    by_cases h3 : t = 3 ∨ t = 5 ∨ t = 10
    · have hm : (ks.filter RN.isInp).length = 0 := by
        by_cases hm : (ks.filter RN.isInp).length = 0
        · exact hm
        · rcases h3 with e | e | e <;> subst e <;> simp [hm] at hr
      simp only [h3, if_true] at hc ⊢
      simp at hc
      simp [hc, hm, filter_len0 hm]
    simp only [h3, if_false] at hc ⊢
    by_cases h4 : t = 4
    · have hm : (ks.filter RN.isInp).length = 0 := by
        by_cases hm : (ks.filter RN.isInp).length = 0
        · exact hm
        · subst h4; simp [hm] at hr
      simp only [h4, if_true] at hc ⊢
      simp at hc
      simp [hc, hm, filter_len0 hm]
    simp only [h4, if_false] at hc ⊢
    by_cases h11 : t = 11
    · have hm : (ks.filter RN.isInp).length = 0 := by
        by_cases hm : (ks.filter RN.isInp).length = 0
        · exact hm
        · subst h11; simp [hm] at hr
      simp only [h11, if_true] at hc ⊢
      simp at hc
      simp [hc, hm, filter_len0 hm]
    simp only [h11, if_false] at hc ⊢
    by_cases h6 : t = 6
    · simp [h6]
    simp only [h6, if_false] at hc ⊢
    by_cases h8 : t = 8
    · simp only [h8, if_true] at hc ⊢
      simpa using hc
    simp only [h8, if_false] at hc ⊢
    by_cases h9 : t = 9
    · subst h9
      by_cases ha : a < 4
      · cases ks with
        | nil => simp [ha] at hr
        | cons k r =>
          by_cases hm : ((k :: r).filter RN.isInp).length = 0
          · simp [hm, ha] at hr
          · simp [hm, ha] at hr
            simp [ha, hr.2]
      · simp [ha]
    simp [h9] at hc
theorem kids_ok (ds : List DefR) : ∀ ks : List RN, (∀ k ∈ ks, ∀ m ∈ nodes k, cntOK m = true ∧ nodeOK ds m = true) → ∀ k ∈ ks, k.ok = true
  | [], _ => by intro k hk; cases hk
  | k0 :: r, h => by
    intro k hk
    rcases List.mem_cons.mp hk with e | e
    · subst e; exact ok_of_nodes ds k (h k (by simp))
    · exact kids_ok ds r (fun k hk => h k (by simp [hk])) k e
end

/-- the def body: validated arena ⇒ the emitted words are the serialization of its spec node -/
theorem words_body {ds : List DefR} {z : RN} (h : ∀ m ∈ nodes z, cntOK m = true ∧ nodeOK ds m = true) : z.words = (z.toNd).ser :=
  RN.words_eq z (ok_of_nodes ds z h)

/-! ## the two arena invariants are preserved by every handler -/
theorem arena_congr {st st' : St} (hv : st'.vals = st.vals) (ha : st'.arena = st.arena) (h : ArenaInv st) : ArenaInv st' := by
  unfold ArenaInv at *; rw [hv, ha]; exact h

theorem mkNode_arena {st st' : St} {t a b : Nat} {s : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') (hi : ArenaInv st) : ArenaInv st' := by
  unfold mkNode at h
  split at h
  · cases h
    unfold ArenaInv at *
    simp only [hi, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, nodes, nodesL_eq]
    rw [← List.append_assoc, ← List.flatMap_append, ← List.reverse_append, List.take_append_drop]
  · cases h

theorem leaf_arena (st : St) (t a b : Nat) (s : Sh) (hi : ArenaInv st) : ArenaInv (leaf st t a b s) := by
  unfold ArenaInv leaf at *
  simp [hi, nodes, nodesL]

theorem locOf_arena {st st' : St} {bd : Bd} (h : locOf st bd = some st') (hi : ArenaInv st) : ArenaInv st' := by
  unfold locOf at h
  split at h
  · cases h
  · cases h
    unfold ArenaInv at *
    simp [hi, nodes, nodesL]

theorem stepF_arena {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) (hi : ArenaInv st) : ArenaInv st' := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; exact hi)
    | (cases h; exact arena_congr rfl rfl hi)
    | (cases h; exact leaf_arena _ _ _ _ _ (arena_congr rfl rfl hi))
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | exact mkNode_arena h2 (arena_congr rfl rfl hi)
       | exact locOf_arena h2 (arena_congr rfl rfl hi)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          exact mkNode_arena h2' (mkNode_arena h1 hi)))
    | (cases h; simp [ArenaInv]; done)

/-- every arena node has the child count of its tag -/
def CntInv (st : St) : Prop := ∀ m ∈ st.arena, cntOK m = true

theorem cnt_congr {st st' : St} (ha : st'.arena = st.arena) (h : CntInv st) : CntInv st' := by
  unfold CntInv at *; rw [ha]; exact h

theorem mkNode_cnt {st st' : St} {t a b : Nat} {s : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') (hc : ∀ ks : List RN, ks.length = n → cntOK (.mk t a b s p ks) = true)
    (hi : CntInv st) : CntInv st' := by
  unfold mkNode at h
  split at h
  · rename_i hn
    cases h
    intro m hm
    rcases List.mem_append.mp hm with e | e
    · exact hi m e
    · rw [List.mem_singleton.mp e]
      exact hc _ (by simp; omega)
  · cases h

theorem leaf_cnt (st : St) (t a b : Nat) (s : Sh) (ht : t = 1 ∨ t = 9) (hi : CntInv st) : CntInv (leaf st t a b s) := by
  intro m hm
  rcases List.mem_append.mp hm with e | e
  · exact hi m e
  · rw [List.mem_singleton.mp e]
    rcases ht with e | e <;> subst e <;> simp [cntOK, RN.tag, RN.kids]

theorem locOf_cnt {st st' : St} {bd : Bd} (h : locOf st bd = some st') (hi : CntInv st) : CntInv st' := by
  unfold locOf at h
  split at h
  · cases h
  · cases h
    intro m hm
    rcases List.mem_append.mp hm with e | e
    · exact hi m e
    · rw [List.mem_singleton.mp e]; simp [cntOK, RN.tag, RN.kids]

theorem stepF_cnt {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) (hi : CntInv st) : CntInv st' := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; exact hi)
    | (cases h; exact cnt_congr rfl hi)
    | (cases h; exact leaf_cnt _ _ _ _ _ (by simp) (cnt_congr rfl hi))
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | exact mkNode_cnt h2 (by intro ks hk; simp [cntOK, RN.tag, RN.kids, RN.b, hk]) (cnt_congr rfl hi)
       | exact locOf_cnt h2 (cnt_congr rfl hi)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          exact mkNode_cnt h2' (by intro ks hk; simp [cntOK, RN.tag, RN.kids, RN.b, hk])
            (mkNode_cnt h1 (by intro ks hk; simp [cntOK, RN.tag, RN.kids, RN.b, hk]) hi)))
    | (cases h; intro m hm; cases hm; done)

theorem init_inv (toks : List Tok) : ArenaInv (init toks) ∧ CntInv (init toks) :=
  ⟨rfl, fun m hm => by cases hm⟩

theorem stepS_inv {c d : List Frame × St} (hs : stepS c = some d) (hi : ArenaInv c.2 ∧ CntInv c.2) : ArenaInv d.2 ∧ CntInv d.2 := by
  obtain ⟨fs, st⟩ := c
  cases fs with
  | nil => simp [stepS] at hs
  | cons f fs =>
    obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
    exact ⟨stepF_arena h1 hi.1, stepF_cnt h1 hi.2⟩

/-- both invariants hold along any run -/
theorem Star.inv {c d : List Frame × St} (h : Star c d) (hi : ArenaInv c.2 ∧ CntInv c.2) : ArenaInv d.2 ∧ CntInv d.2 := by
  induction h with
  | refl => exact hi
  | step hs _ ih => exact ih (stepS_inv hs hi)

end ParRun
