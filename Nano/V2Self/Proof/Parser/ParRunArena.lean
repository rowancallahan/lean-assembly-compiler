/- Nano/V2Self/Proof/Parser/ParRunArena: arena facts the validation of task 60 needs (parser lead), pure.
* `kids_lt_arena` : under `ArenaInv`, every arena node has fewer kids than the arena has nodes;
* `CallInv` : every CALL node in the arena targets a FINISHED def (`a < |defs|`), an invariant of every reachable state (with B's `WF`). -/
import Nano.V2Self.Proof.Parser.ParTreeOK
import Nano.V2Self.Proof.Parser.ParRunWFPres
namespace ParRun
open ParSpec

mutual
theorem nodes_len_pos : ∀ n : RN, 0 < (nodes n).length
  | .mk .. => by simp [nodes]
theorem nodesL_len_ge : ∀ ks : List RN, ks.length ≤ (nodesL ks).length
  | [] => by simp [nodesL]
  | k :: r => by
    have := nodes_len_pos k; have := nodesL_len_ge r
    simp [nodesL]; omega
end

theorem kids_lt_nodes (n : RN) : n.kids.length < (nodes n).length := by
  cases n with
  | mk t a b s p ks => have := nodesL_len_ge ks; simp [nodes, RN.kids]; omega

mutual
/-- a subtree has at most as many nodes as the tree -/
theorem nodes_sub : ∀ (v : RN) (m : RN), m ∈ nodes v → (nodes m).length ≤ (nodes v).length
  | .mk t a b s p ks, m, hm => by
    simp only [nodes, List.mem_append, List.mem_singleton] at hm ⊢
    rcases hm with hm | rfl
    · have := nodesL_sub ks m hm; simp; omega
    · simp [nodes]
theorem nodesL_sub : ∀ (ks : List RN) (m : RN), m ∈ nodesL ks → (nodes m).length ≤ (nodesL ks).length
  | [], m, hm => by simp [nodesL] at hm
  | k :: r, m, hm => by
    simp only [nodesL, List.mem_append, List.length_append] at hm ⊢
    rcases hm with hm | hm
    · have := nodes_sub k m hm; omega
    · have := nodesL_sub r m hm; omega
end

theorem kids_lt_arena {st : St} (hA : ArenaInv st) {m : RN} (hm : m ∈ st.arena) : m.kids.length < st.arena.length := by
  rw [hA] at hm ⊢
  rw [← nodesL_eq] at hm ⊢
  have := nodesL_sub _ m hm
  have := kids_lt_nodes m
  omega

/-- CALL nodes target finished defs -/
def CallInv (st : St) : Prop := ∀ m ∈ st.arena, m.tag = 8 → m.a < st.defs.length

theorem callInv_mkNode {st st' : St} {t a b : Nat} {sh : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b sh p n = some st') (ht : t = 8 → a < st.defs.length) (hi : CallInv st) : CallInv st' := by
  unfold mkNode at h; split at h
  · cases h
    intro m hm h8
    rcases List.mem_append.mp hm with hm | hm
    · exact hi m hm h8
    · rw [List.mem_singleton.mp hm] at h8 ⊢; exact ht h8
  · cases h

theorem callInv_leaf {st : St} {t a b : Nat} {s : Sh} (ht : t ≠ 8) (hi : CallInv st) : CallInv (leaf st t a b s) := by
  intro m hm h8
  rcases List.mem_append.mp hm with hm | hm
  · exact hi m hm h8
  · rw [List.mem_singleton.mp hm] at h8; exact absurd h8 ht

theorem callInv_locOf {st st' : St} {bd : Bd} (h : locOf st bd = some st') (hi : CallInv st) : CallInv st' := by
  unfold locOf at h; split at h
  · cases h
  · cases h
    intro m hm h8
    rcases List.mem_append.mp hm with hm | hm
    · exact hi m hm h8
    · rw [List.mem_singleton.mp hm] at h8; simp [RN.tag] at h8

theorem callInv_mono {st st' : St} (ha : st'.arena = st.arena) (hd : st.defs.length ≤ st'.defs.length) (hi : CallInv st) :
    CallInv st' := fun m hm h8 => by rw [ha] at hm; have := hi m hm h8; omega

/-- `CallInv` is preserved by every handler of a WF configuration -/
theorem stepF_callInv {f : Frame} {r k : List Frame} {st st' : St} (hw : WF (f :: r) st) (h : stepF f st = some (k, st'))
    (hi : CallInv st) : CallInv st' := by
  obtain ⟨g1, hg⟩ := wf_pre hw
  cases f
  case mkCall c n =>
    cases c with
    | pr p =>
      simp only [stepF] at h
      obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
      exact callInv_mkNode h2 (fun e => absurd e (by decide)) hi
    | df j =>
      simp only [effF, Ctx.callTgt, St.ctx, rows] at hg
      split at hg
      · rename_i hc
        have hj : j < st.defs.length := by simp at hc; omega
        simp only [stepF] at h
        split at h
        · obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
          exact callInv_mkNode h2 (fun _ => hj) hi
        · cases h
      · cases hg
  case argName =>
    simp only [stepF] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; exact callInv_leaf (by decide) hi)
      | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
         exact callInv_mkNode h2 (fun _ => findD_lt (by assumption)) hi)
  all_goals simp only [stepF] at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hi)
    | (cases h; intro m hm; simp at hm; done)
    | (cases h; exact callInv_mono (st := st) rfl (by simp) hi)
    | (cases h; exact callInv_leaf (by decide) hi)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | (unfold locOf at h2; split at h2 <;> cases h2
          intro m hm h8
          rcases List.mem_append.mp hm with hm | hm
          · exact hi m hm h8
          · rw [List.mem_singleton.mp hm] at h8; simp [RN.tag] at h8)
       | (unfold mkNode at h2; split at h2 <;> cases h2
          intro m hm h8
          rcases List.mem_append.mp hm with hm | hm
          · exact hi m hm h8
          · rw [List.mem_singleton.mp hm] at h8; simp [RN.tag] at h8)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          first | (unfold mkNode at h1; split at h1 <;> cases h1) | cases h1
          all_goals (unfold mkNode at h2'; split at h2' <;> cases h2')
          all_goals (intro m hm h8
                     simp only [List.mem_append, List.mem_singleton, or_assoc] at hm
                     rcases hm with hm | hm
                     · exact hi m hm h8
                     · first
                       | (subst hm; simp [RN.tag] at h8; done)
                       | (rcases hm with hm | hm <;> (subst hm; simp [RN.tag] at h8)))))

/-- `CallInv` along every run from the initial configuration -/
theorem callInv_reach {toks : List Tok} : ∀ {c d : List Frame × St}, Star c d → Star ([.defs], init toks) c → CallInv c.2 → CallInv d.2 := by
  intro c d h
  induction h with
  | refl => exact fun _ hi => hi
  | @step c c1 d hs _ ih =>
    intro hr hi
    obtain ⟨fs, st⟩ := c
    cases fs with
    | nil => simp [stepS] at hs
    | cons f rest =>
      obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
      exact ih (hr.trans (.step hs (.refl _))) (stepF_callInv (wf_star hr) h1 hi)

theorem callInv_star {toks : List Tok} {fs : List Frame} {st : St} (h : Star ([.defs], init toks) (fs, st)) : CallInv st :=
  callInv_reach h (.refl _) (fun m hm => by simp [init] at hm)

end ParRun
