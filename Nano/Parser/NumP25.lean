/- Nano/Parser/NumP25: bounds on the spec's groups (demands below 3, slots below 2^33). -/
import Nano.Parser.NumP24
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

def GB (gs : List NumSpec.G) : Prop := ∀ G ∈ gs, G.d < 3 ∧ ∀ v ∈ G.vs, v < 2 ^ 33

theorem GB.app {a b : NumSpec.R} (ha : GB a.1) (hb : GB b.1) : GB (a.app b).1 := by
  intro G hG; simp only [NumSpec.R.app, List.mem_append] at hG
  rcases hG with hG | hG
  · exact ha G hG
  · exact hb G hG

theorem GB.nil : GB ([] : List NumSpec.G) := by intro G hG; simp at hG

theorem GB.cons {G : NumSpec.G} {gs : List NumSpec.G} (h1 : G.d < 3) (h2 : ∀ v ∈ G.vs, v < 2 ^ 33) (h : GB gs) :
    GB (G :: gs) := by
  intro G' hG'; simp at hG'; rcases hG' with rfl | hG'
  · exact ⟨h1, h2⟩
  · exact h G' hG'

theorem colL_gb (f : Nat) (ks ws : List Nat) (env : List Bool) : ∀ (cs : List Nd),
    (∀ c ∈ cs, GB (NumSpec.col f ks ws env 1 c).1) → GB (colL f ks ws env cs).1
  | [], _ => GB.nil
  | c :: cs, h => GB.app (h c (by simp)) (colL_gb f ks ws env cs (fun c hc => h c (by simp [hc])))

theorem leaves_nb {np : Nat} : ∀ (f : Nat) (e : Nd), NB np e → ∀ l ∈ NumSpec.leaves f e, NB np l
  | 0, e, h, l, hl => by cases e <;> simp [NumSpec.leaves] at hl <;> subst hl <;> exact h
  | f + 1, e, h, l, hl => by
    cases e with
    | bin op a b =>
      simp only [NumSpec.leaves] at hl
      split at hl
      · simp at hl; subst hl; exact h
      · obtain ⟨-, ha, hb⟩ := h
        rcases List.mem_append.1 hl with hl | hl
        · exact leaves_nb f a ha l hl
        · exact leaves_nb f b hb l hl
    | _ => simp [NumSpec.leaves] at hl; subst hl; exact h

/-- the bounds at fuel f -/
def SB (np : Nat) (f : Nat) : Prop :=
  ∀ (e : Nd) (ks ws : List Nat) (env : List Bool), NB np e →
    (∀ dd, dd < 3 → GB (NumSpec.col f ks ws env dd e).1) ∧
    (∀ v ∈ (NumSpec.litG f ks ws env e).1.1, v < 2 ^ 32) ∧ GB (NumSpec.litG f ks ws env e).2.1 ∧
    (∀ sl w, sl < 2 ^ 32 → GB (NumSpec.letG f ks ws env sl w e).1) ∧
    (∀ b, NB np b → GB (NumSpec.cmpG f ks ws env e b).1)

theorem sb_zero (np : Nat) : SB np 0 := by
  intro e ks ws env _
  refine ⟨fun dd _ => ?_, ?_, ?_, fun sl w _ => ?_, fun b _ => ?_⟩ <;>
    simp [NumSpec.col, NumSpec.litG, NumSpec.letG, NumSpec.cmpG, GB]

theorem lpL_gb {np f : Nat} (ih : SB np f) (ks ws : List Nat) (env : List Bool) (sl : Nat) (hsl : sl < 2 ^ 32) :
    ∀ (cs : List Nd) (i : Nat), i + cs.length ≤ 2 ^ 32 → (∀ c ∈ cs, NB np c) → GB (lpL f ks ws env sl cs i).1
  | [], _, _, _ => GB.nil
  | c :: cs, i, hi, hc => by
    rw [lpL_cons]
    refine GB.app ?_ (lpL_gb ih ks ws env sl hsl cs (i + 1) (by simp at hi; omega) (fun c' h => hc c' (by simp [h])))
    obtain ⟨h1, h2, h3, -, -⟩ := ih c ks ws env (hc c (by simp))
    unfold lf
    split
    · refine GB.cons (by simp) ?_ h3
      intro v hv; simp at hv; rcases hv with rfl | hv
      · simp at hi; omega
      · have := h2 v hv; omega
    · exact h1 0 (by omega)

theorem call_gb {np f : Nat} (ih : SB np f) (ks ws : List Nat) (env : List Bool) (id : Nat) (as : List Nd)
    (has : ∀ c ∈ as, NB np c) :
    GB (as.zipIdx.attach.foldr (fun ⟨(a, i), _⟩ r =>
        (NumSpec.col f ks ws env (if ks.getD id 0 == 1 && i == 0 then 2 else 1) a).app r) NumSpec.R.ok).1 := by
  cases as with
  | nil => exact GB.nil
  | cons a as =>
    rw [call_spec]
    refine GB.app ((ih a ks ws env (has a (by simp))).1 _ (by split <;> omega)) ?_
    exact colL_gb f ks ws env as (fun c hc => (ih c ks ws env (has c (by simp [hc]))).1 1 (by omega))

theorem sb_succ {np f : Nat} (ih : SB np f) : SB np (f + 1) := by
  intro e ks ws env hnb
  have hcol : ∀ c, NB np c → ∀ env', GB (NumSpec.col f ks ws env' 1 c).1 := fun c hc env' =>
    (ih c ks ws env' hc).1 1 (by omega)
  -- litG
  have hlit : (∀ v ∈ (NumSpec.litG (f + 1) ks ws env e).1.1, v < 2 ^ 32) ∧ GB (NumSpec.litG (f + 1) ks ws env e).2.1 := by
    rw [litG_succ]
    cases e with
    | loc sl w => exact ⟨by simp; exact hnb.1, GB.nil⟩
    | bin op a b =>
      obtain ⟨-, na, nb⟩ := hnb
      obtain ⟨-, a2, a3, -, -⟩ := ih a ks ws env na
      obtain ⟨-, b2, b3, -, -⟩ := ih b ks ws env nb
      refine ⟨?_, GB.app a3 b3⟩
      intro v hv; simp at hv; rcases hv with hv | hv
      · exact a2 v hv
      · exact b2 v hv
    | ite cm a b t e =>
      obtain ⟨-, na, nb, nt, ne⟩ := hnb
      obtain ⟨-, -, -, -, a5⟩ := ih a ks ws env na
      obtain ⟨-, t2, t3, -, -⟩ := ih t ks ws env nt
      obtain ⟨-, e2, e3, -, -⟩ := ih e ks ws env ne
      refine ⟨?_, GB.app (a5 b nb) (GB.app t3 e3)⟩
      intro v hv; simp at hv; rcases hv with hv | hv
      · exact t2 v hv
      · exact e2 v hv
    | letE sl w v b =>
      obtain ⟨hsl, -, nv, nb⟩ := hnb
      obtain ⟨-, -, -, v4, -⟩ := ih v ks ws env nv
      obtain ⟨-, b2, b3, -, -⟩ := ih b ks ws (NumSpec.setW env sl (NumSpec.lw f ws env v)) nb
      exact ⟨b2, GB.app (v4 sl w hsl) b3⟩
    | _ => exact ⟨by simp, GB.nil⟩
  refine ⟨fun dd hdd => ?_, hlit.1, hlit.2, fun sl w hsl => ?_, fun b nb => ?_⟩
  · -- col
    rw [col_succ]
    split
    · obtain ⟨-, e2, e3, -, -⟩ := ih e ks ws env hnb
      exact GB.cons (by simpa using hdd) (fun v hv => by have := e2 v hv; omega) e3
    · cases e with
      | bin op a b =>
        have hn0 := hnb
        obtain ⟨-, na, nb⟩ := hnb
        dsimp only
        split
        · exact GB.app GB.nil (GB.app (hcol a na env) (hcol b nb env))
        · refine GB.app GB.nil ?_
          rw [colL_attach]
          exact colL_gb f ks ws env _ (fun c hc => hcol c (leaves_nb f _ hn0 c hc) env)
      | ite cm a b t e =>
        obtain ⟨-, na, nb, nt, ne⟩ := hnb
        exact GB.app GB.nil (GB.app ((ih a ks ws env na).2.2.2.2 b nb) (GB.app (hcol t nt env) (hcol e ne env)))
      | letE sl w v b =>
        obtain ⟨hsl, -, nv, nb⟩ := hnb
        exact GB.app ((ih v ks ws env nv).2.2.2.1 sl w hsl) ((ih b ks ws _ nb).1 dd hdd)
      | pair cs =>
        dsimp only; rw [colL_attach]
        exact colL_gb f ks ws env cs (fun c hc => hcol c ((nbl_iff cs).1 hnb.2 c hc) env)
      | call id as => exact call_gb ih ks ws env id as ((nbl_iff as).1 hnb.2.2)
      | prim pn as =>
        dsimp only; rw [colL_attach]
        exact colL_gb f ks ws env as (fun c hc => hcol c ((nbl_iff as).1 hnb.2.2 c hc) env)
      | loop z sv => exact GB.app (hcol z hnb.1 env) (hcol sv hnb.2 env)
      | cont a => exact hcol a hnb.2 env
      | _ => exact GB.nil
  · -- letG
    rw [letG_succ]
    cases e with
    | pair cs => exact lpL_gb ih ks ws env sl hsl cs 0 (by simp; exact Nat.le_of_lt hnb.1) ((nbl_iff cs).1 hnb.2)
    | _ =>
      dsimp only
      obtain ⟨h1, h2, h3, -, -⟩ := ih _ ks ws env hnb
      split
      · refine GB.cons (by simp) ?_ h3
        intro v hv; simp at hv; rcases hv with rfl | hv
        · omega
        · have := h2 v hv; omega
      · exact h1 0 (by omega)
  · -- cmpG
    rw [cmpG_succ]
    obtain ⟨a1, a2, a3, -, -⟩ := ih e ks ws env hnb
    obtain ⟨b1, b2, b3, -, -⟩ := ih b ks ws env nb
    split
    · refine GB.app GB.nil (GB.cons (by simp) ?_ (GB.app a3 b3))
      intro v hv; simp at hv; rcases hv with hv | hv
      · have := a2 v hv; omega
      · have := b2 v hv; omega
    · exact GB.app GB.nil (GB.app (a1 1 (by omega)) (b1 1 (by omega)))

theorem sb_all (np : Nat) : ∀ f, SB np f
  | 0 => sb_zero np
  | f + 1 => sb_succ (sb_all np f)

end NumP
