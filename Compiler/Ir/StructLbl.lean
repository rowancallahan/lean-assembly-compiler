/- The labels of flattened structured code are distinct (`flatS` / `flatT` take fresh labels from the counter), so
every region of `mkFunc` has its blocks found by `lookup` (`mkFunc_region`), the hypothesis `GS.OkT` of
`flatT_ok`. -/
import Compiler.Ir.StructOk

namespace Proven.Ir
set_option autoImplicit false

/-- `lomega` after unfolding the label / register synonyms of `Nat` (`lomega` skips equalities at `Lbl`) -/
macro "lomega" : tactic => `(tactic| ((try simp only [Lbl, FId, VReg] at *); omega))

/-- keys of a block list -/
abbrev keys (L : List (Lbl × Block VReg)) : List Lbl := L.map Prod.fst

/-- flattening from `g` to `g'` adds blocks with distinct fresh labels (the open label of `g`, or from the counter) and
leaves a fresh open label -/
def Fr (g g' : GS) : Prop :=
  g.nl ≤ g'.nl ∧ g'.cl < g'.nl ∧ ∃ X, g'.bs = g.bs ++ X ∧ (keys X ++ [g'.cl]).Nodup ∧
    ∀ k ∈ keys X ++ [g'.cl], k = g.cl ∨ (g.nl ≤ k ∧ k < g'.nl)

theorem Fr.refl (g : GS) (h : g.cl < g.nl) : Fr g g :=
  ⟨Nat.le_refl _, h, [], by simp, by simp, by simp⟩

theorem Fr.trans {g₁ g₂ g₃ : GS} (h₁ : g₁.cl < g₁.nl) (a : Fr g₁ g₂) (b : Fr g₂ g₃) : Fr g₁ g₃ := by
  obtain ⟨n12, c2, X, e2, nd, hk⟩ := a
  obtain ⟨n23, c3, Y, e3, nd', hk'⟩ := b
  refine ⟨by lomega, c3, X ++ Y, by rw [e3, e2, List.append_assoc], ?_, ?_⟩
  · simp only [keys, List.map_append, List.append_assoc] at nd nd' ⊢
    rw [List.nodup_append] at nd ⊢
    refine ⟨nd.1, nd', ?_⟩
    intro a ha b hb e; subst e
    have hX := hk a (by simp [keys, ha])
    have hY := hk' a (by simp only [keys, List.mem_append] at hb ⊢; exact hb)
    have hne : a ≠ g₂.cl := fun e => nd.2.2 a ha g₂.cl (by simp) e
    rcases hY with hY | hY
    · exact hne hY
    · rcases hX with hX | hX
      · lomega
      · lomega
  · intro k hk2
    simp only [keys, List.map_append, List.append_assoc, List.mem_append] at hk2
    rcases hk2 with hk2 | hk2
    · rcases hk k (by simp [keys, hk2]) with e | e
      · exact .inl e
      · exact .inr ⟨e.1, by lomega⟩
    · rcases hk' k (by simp only [keys, List.mem_append] at hk2 ⊢; exact hk2) with e | e
      · subst e
        rcases hk g₂.cl (by simp) with e' | e'
        · exact .inl e'
        · exact .inr ⟨e'.1, by lomega⟩
      · exact .inr ⟨by lomega, e.2⟩

theorem nd_app {A B : List Nat} (ha : A.Nodup) (hb : B.Nodup) (P Q : Nat → Prop) (hA : ∀ a ∈ A, P a)
    (hB : ∀ b ∈ B, Q b) (hPQ : ∀ x, P x → Q x → False) : (A ++ B).Nodup :=
  List.nodup_append.2 ⟨ha, hb, fun a h1 b h2 e => hPQ a (hA a h1) (e ▸ hB b h2)⟩

theorem keys_snoc (X : List (Lbl × Block VReg)) (c : Lbl) (B : Block VReg) : keys (X ++ [(c, B)]) = keys X ++ [c] := by
  simp [keys]

theorem flatS_fr : ∀ (sc : SC) (g : GS), g.cl < g.nl → Fr g (flatS sc g)
  | .nop, g, h => Fr.refl g h
  | .i x, g, h => ⟨Nat.le_refl _, h, [], by simp [flatS], by simp, by simp [flatS]⟩
  | .seq a b, g, h => (flatS_fr a g h).trans h (flatS_fr b _ (flatS_fr a g h).2.1)
  | .ite t a b, g, h => by
    simp only [flatS]
    generalize hg1 : (({ g with nl := g.nl + 3 } : GS).close (.br t g.nl [] (g.nl + 1) [])).open g.nl = g1
    have e1 : g1.nl = g.nl + 3 ∧ g1.cl = g.nl ∧ g1.bs = g.bs ++ [(g.cl, ⟨g.cp, g.ci, .br t g.nl [] (g.nl + 1) []⟩)] := by
      subst hg1; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨na1, ca, XA, eA, ndA, kA⟩ := flatS_fr a g1 (by lomega)
    generalize flatS a g1 = ga at na1 ca eA ndA kA
    generalize hg2 : (ga.close (.jmp (g.nl + 2) [])).open (g.nl + 1) = g2
    have e2 : g2.nl = ga.nl ∧ g2.cl = g.nl + 1 ∧ g2.bs = ga.bs ++ [(ga.cl, ⟨ga.cp, ga.ci, .jmp (g.nl + 2) []⟩)] := by
      subst hg2; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨nb1, cb, XB, eB, ndB, kB⟩ := flatS_fr b g2 (by lomega)
    generalize flatS b g2 = gb at nb1 cb eB ndB kB
    refine ⟨by simp [GS.close, GS.open]; lomega, by simp [GS.close, GS.open]; lomega,
      [(g.cl, ⟨g.cp, g.ci, .br t g.nl [] (g.nl + 1) []⟩)] ++ XA ++ [(ga.cl, ⟨ga.cp, ga.ci, .jmp (g.nl + 2) []⟩)] ++ XB ++
        [(gb.cl, ⟨gb.cp, gb.ci, .jmp (g.nl + 2) []⟩)], ?_, ?_, ?_⟩
    · simp only [GS.open, GS.close, eB, e2, eA, e1, List.append_assoc]
    · have : keys ([(g.cl, ⟨g.cp, g.ci, .br t g.nl [] (g.nl + 1) []⟩)] ++ XA ++ [(ga.cl, ⟨ga.cp, ga.ci, .jmp (g.nl + 2) []⟩)] ++ XB ++
          [(gb.cl, ⟨gb.cp, gb.ci, .jmp (g.nl + 2) []⟩)]) ++ [(((gb.close (.jmp (g.nl + 2) [])).open (g.nl + 2))).cl] =
          [g.cl] ++ ((keys XA ++ [ga.cl]) ++ ((keys XB ++ [gb.cl]) ++ [g.nl + 2])) := by
        simp [keys, GS.close, GS.open]
      rw [this]
      obtain ⟨e1a, e1b, -⟩ := e1
      obtain ⟨e2a, e2b, -⟩ := e2
      refine nd_app (A := [g.cl]) (by simp) ?_ (· < g.nl) (· ≥ g.nl) (by simpa using h) ?_ (fun _ a b => by lomega)
      · refine nd_app ndA ?_ (fun k => k = g.nl ∨ (g.nl + 3 ≤ k ∧ k < ga.nl))
          (fun k => (k = g.nl + 1 ∨ k = g.nl + 2) ∨ k ≥ ga.nl)
          (fun k hk => by
            rcases kA k hk with e | e
            · exact .inl (by lomega)
            · exact .inr ⟨by lomega, e.2⟩) ?_
          (fun x p q => by lomega)
        · refine nd_app (B := [g.nl + 2]) ndB (by simp) (fun k => k = g.nl + 1 ∨ ga.nl ≤ k) (· = g.nl + 2) ?_ (by simp)
            (fun x p q => by lomega)
          intro k hk; rcases kB k hk with e | e
          · exact .inl (by lomega)
          · exact .inr (by lomega)
        · intro k hk; simp only [List.mem_append, List.mem_singleton] at hk
          rcases hk with hk | hk
          · rcases kB k (by simp only [List.mem_append, List.mem_singleton]; exact hk) with e | e
            · exact .inl (.inl (by lomega))
            · exact .inr (by lomega)
          · exact .inl (.inr hk)
      · intro k hk; simp only [List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | hk | hk
        · rcases kA k (by simp only [List.mem_append, List.mem_singleton]; exact hk) with e | e <;> lomega
        · rcases kB k (by simp only [List.mem_append, List.mem_singleton]; exact hk) with e | e <;> lomega
        · lomega
    · intro k hk
      simp only [keys, List.map_append, List.map_cons, List.map_nil, GS.close, GS.open, List.mem_append,
        List.mem_singleton, List.append_assoc] at hk
      simp only [GS.close, GS.open]
      have hA := fun k h => kA k (by simp only [keys, List.mem_append, List.mem_singleton]; exact h)
      have hB := fun k h => kB k (by simp only [keys, List.mem_append, List.mem_singleton]; exact h)
      obtain ⟨e1a, e1b, -⟩ := e1
      obtain ⟨e2a, e2b, -⟩ := e2
      rcases hk with hk | hk | hk | hk | hk | hk
      · exact .inl hk
      · rcases hA k (.inl hk) with e | e <;> right <;> constructor <;> lomega
      · rcases hA k (.inr hk) with e | e <;> right <;> constructor <;> lomega
      · rcases hB k (.inl hk) with e | e <;> right <;> constructor <;> lomega
      · rcases hB k (.inr hk) with e | e <;> right <;> constructor <;> lomega
      · right; constructor <;> lomega
  | .loop t b, g, h => by
    simp only [flatS]
    generalize hg2 : (((({ g with nl := g.nl + 3 } : GS).close (.jmp g.nl [])).open g.nl).close
      (.br t (g.nl + 1) [] (g.nl + 2) [])).open (g.nl + 1) = g2
    have e2 : g2.nl = g.nl + 3 ∧ g2.cl = g.nl + 1 ∧ g2.bs = g.bs ++ [(g.cl, ⟨g.cp, g.ci, .jmp g.nl []⟩),
        (g.nl, ⟨[], [], .br t (g.nl + 1) [] (g.nl + 2) []⟩)] := by
      subst hg2; simp [GS.close, GS.open]
    obtain ⟨nb1, cb, XB, eB, ndB, kB⟩ := flatS_fr b g2 (by lomega)
    generalize flatS b g2 = gb at nb1 cb eB ndB kB
    obtain ⟨e2a, e2b, e2c⟩ := e2
    refine ⟨by simp [GS.close, GS.open]; lomega, by simp [GS.close, GS.open]; lomega,
      [(g.cl, ⟨g.cp, g.ci, .jmp g.nl []⟩), (g.nl, ⟨[], [], .br t (g.nl + 1) [] (g.nl + 2) []⟩)] ++ XB ++
        [(gb.cl, ⟨gb.cp, gb.ci, .jmp g.nl []⟩)], ?_, ?_, ?_⟩
    · simp only [GS.open, GS.close, eB, e2c, List.append_assoc, List.cons_append, List.nil_append]
    · have : keys ([(g.cl, ⟨g.cp, g.ci, .jmp g.nl []⟩), (g.nl, ⟨[], [], .br t (g.nl + 1) [] (g.nl + 2) []⟩)] ++ XB ++
          [(gb.cl, ⟨gb.cp, gb.ci, .jmp g.nl []⟩)]) ++ [(((gb.close (.jmp g.nl [])).open (g.nl + 2))).cl] =
          [g.cl] ++ ([g.nl] ++ ((keys XB ++ [gb.cl]) ++ [g.nl + 2])) := by
        simp [keys, GS.close, GS.open]
      rw [this]
      refine nd_app (A := [g.cl]) (by simp) ?_ (· < g.nl) (· ≥ g.nl) (by simpa using h) ?_ (fun _ a b => by lomega)
      · refine nd_app (A := [g.nl]) (by simp) ?_ (· = g.nl) (· ≥ g.nl + 1) (by simp) ?_ (fun _ a b => by lomega)
        · refine nd_app (B := [g.nl + 2]) ndB (by simp) (fun k => k = g.nl + 1 ∨ g.nl + 3 ≤ k) (· = g.nl + 2) ?_
            (by simp) (fun x p q => by lomega)
          intro k hk; rcases kB k hk with e | e
          · exact .inl (by lomega)
          · exact .inr (by lomega)
        · intro k hk; simp only [List.mem_append, List.mem_singleton] at hk
          rcases hk with hk | hk
          · rcases kB k (by simp only [List.mem_append, List.mem_singleton]; exact hk) with e | e <;> lomega
          · lomega
      · intro k hk; simp only [List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | hk | hk
        · lomega
        · rcases kB k (by simp only [List.mem_append, List.mem_singleton]; exact hk) with e | e <;> lomega
        · lomega
    · intro k hk
      simp only [keys, List.map_append, List.map_cons, List.map_nil, GS.close, GS.open, List.mem_append,
        List.mem_singleton, List.append_assoc, List.mem_cons, List.not_mem_nil, or_false] at hk
      simp only [GS.close, GS.open]
      have hB := fun k h => kB k (by simp only [keys, List.mem_append, List.mem_singleton]; exact h)
      rcases hk with (hk | hk) | hk | hk | hk
      · exact .inl hk
      · right; constructor <;> lomega
      · rcases hB k (.inl hk) with e | e <;> right <;> constructor <;> lomega
      · rcases hB k (.inr hk) with e | e <;> right <;> constructor <;> lomega
      · right; constructor <;> lomega

/-- code with a terminator adds blocks with distinct labels: its open label or fresh ones -/
def FrT (g g' : GS) : Prop :=
  g.nl ≤ g'.nl ∧ ∃ X, g'.bs = g.bs ++ X ∧ (keys X).Nodup ∧ ∀ k ∈ keys X, k = g.cl ∨ (g.nl ≤ k ∧ k < g'.nl)

theorem flatT_fr : ∀ (tc : TC) (g : GS), g.cl < g.nl → FrT g (flatT tc g)
  | .term t, g, h => ⟨Nat.le_refl _, [(g.cl, ⟨g.cp, g.ci, t⟩)], rfl, by simp [keys], by simp [keys, GS.close]⟩
  | .seq a t, g, h => by
    obtain ⟨n1, c1, X, e1, nd1, k1⟩ := flatS_fr a g h
    obtain ⟨n2, Y, e2, nd2, k2⟩ := flatT_fr t (flatS a g) c1
    simp only [flatT]
    generalize flatS a g = ga at *
    refine ⟨by lomega, X ++ Y, by rw [e2, e1, List.append_assoc], ?_, ?_⟩
    · simp only [keys, List.map_append] at nd1 ⊢
      rw [List.nodup_append] at nd1
      refine nd_app nd1.1 nd2 (fun k => k ≠ ga.cl ∧ (k = g.cl ∨ (g.nl ≤ k ∧ k < ga.nl)))
        (fun k => k = ga.cl ∨ ga.nl ≤ k) (fun k hk => ⟨fun e => nd1.2.2 k hk ga.cl (by simp) e, k1 k (by simp [keys, hk])⟩)
        (fun k hk => by
          rcases k2 k hk with e | e
          · exact .inl e
          · exact .inr e.1) (fun x p q => by
          rcases p with ⟨p1, p2 | p2⟩ <;> rcases q with q | q <;> lomega)
    · intro k hk; simp only [keys, List.map_append, List.mem_append] at hk
      rcases hk with hk | hk
      · rcases k1 k (by simp [keys, hk]) with e | e
        · exact .inl e
        · exact .inr ⟨e.1, by lomega⟩
      · rcases k2 k hk with e | e
        · rcases k1 ga.cl (by simp) with e' | e'
          · exact .inl (e.trans e')
          · exact .inr ⟨by lomega, by lomega⟩
        · exact .inr ⟨by lomega, e.2⟩
  | .ite t a b, g, h => by
    simp only [flatT]
    generalize hg1 : (({ g with nl := g.nl + 2 } : GS).close (.br t g.nl [] (g.nl + 1) [])).open g.nl = g1
    have e1 : g1.nl = g.nl + 2 ∧ g1.cl = g.nl ∧ g1.bs = g.bs ++ [(g.cl, ⟨g.cp, g.ci, .br t g.nl [] (g.nl + 1) []⟩)] := by
      subst hg1; exact ⟨rfl, rfl, rfl⟩
    obtain ⟨e1a, e1b, e1c⟩ := e1
    obtain ⟨na1, XA, eA, ndA, kA⟩ := flatT_fr a g1 (by lomega)
    generalize flatT a g1 = ga at na1 eA ndA kA
    have c2 : (ga.open (g.nl + 1)).cl < (ga.open (g.nl + 1)).nl := by simp [GS.open]; lomega
    obtain ⟨nb1, XB, eB, ndB, kB⟩ := flatT_fr b (ga.open (g.nl + 1)) c2
    generalize flatT b (ga.open (g.nl + 1)) = gb at nb1 eB ndB kB
    simp only [GS.open] at nb1 eB kB
    refine ⟨by lomega, [(g.cl, ⟨g.cp, g.ci, .br t g.nl [] (g.nl + 1) []⟩)] ++ XA ++ XB, ?_, ?_, ?_⟩
    · rw [eB, eA, e1c]; simp only [List.append_assoc]
    · have : keys ([(g.cl, ⟨g.cp, g.ci, .br t g.nl [] (g.nl + 1) []⟩)] ++ XA ++ XB) = [g.cl] ++ (keys XA ++ keys XB) := by
        simp [keys]
      rw [this]
      refine nd_app (A := [g.cl]) (by simp) (nd_app ndA ndB (fun k => k = g.nl ∨ (g.nl + 2 ≤ k ∧ k < ga.nl))
        (fun k => k = g.nl + 1 ∨ ga.nl ≤ k) (fun k hk => by rcases kA k hk with e | e <;> lomega)
        (fun k hk => by rcases kB k hk with e | e <;> lomega) (fun x p q => by lomega)) (· < g.nl) (· ≥ g.nl)
        (by simpa using h) ?_ (fun _ a b => by lomega)
      intro k hk; simp only [List.mem_append] at hk
      rcases hk with hk | hk
      · rcases kA k hk with e | e <;> lomega
      · rcases kB k hk with e | e <;> lomega
    · intro k hk
      simp only [keys, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hk
      rcases hk with (hk | hk) | hk
      · exact .inl hk
      · rcases kA k hk with e | e <;> right <;> constructor <;> lomega
      · rcases kB k hk with e | e <;> right <;> constructor <;> lomega

end Proven.Ir

namespace Proven.Ir

theorem flatRs_keys : ∀ (rs : List (Lbl × TC)) (nl : Nat) (ps : List VReg), (rs.map Prod.fst).Nodup →
    (∀ x ∈ rs, x.1 < nl) → (keys (flatRs nl ps rs)).Nodup ∧ ∀ k ∈ keys (flatRs nl ps rs), k ∈ rs.map Prod.fst ∨ nl ≤ k
  | [], _, _, _, _ => by simp [flatRs, keys]
  | (l, t) :: rs, nl, ps, hn, hl => by
    simp only [flatRs]
    have h0 : l < nl := hl (l, t) (by simp)
    obtain ⟨n1, X, eX, ndX, kX⟩ := flatT_fr t ⟨nl, [], l, ps, []⟩ h0
    generalize flatT t ⟨nl, [], l, ps, []⟩ = g at n1 eX ndX kX
    simp only [List.nil_append] at eX; subst eX
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨nd2, k2⟩ := flatRs_keys rs g.nl [] hn.2 (fun x hx => by have := hl x (by simp [hx]); lomega)
    refine ⟨?_, ?_⟩
    · simp only [keys, List.map_append]
      refine nd_app ndX nd2 (fun k => k = l ∨ (nl ≤ k ∧ k < g.nl)) (fun k => k ∈ rs.map Prod.fst ∨ g.nl ≤ k) kX k2 ?_
      intro x p q
      rcases q with q | q
      · have hx : x < nl := by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 q; exact hl y (by simp [hy])
        rcases p with p | p
        · subst p; exact hn.1 q
        · lomega
      · rcases p with p | p <;> lomega
    · intro k hk; simp only [keys, List.map_append, List.mem_append] at hk
      rcases hk with hk | hk
      · rcases kX k hk with e | e
        · exact .inl (by simp [e])
        · exact .inr e.1
      · rcases k2 k hk with e | e
        · exact .inl (by simp [e])
        · exact .inr (by lomega)

theorem lookup_of_nodup : ∀ (L : List (Lbl × Block VReg)), (keys L).Nodup → ∀ lb ∈ L, L.lookup lb.1 = some lb.2
  | [], _, _, h => nomatch h
  | (k, B) :: L, hn, lb, h => by
    simp only [keys, List.map_cons, List.nodup_cons] at hn
    simp only [List.lookup_cons]
    rcases List.mem_cons.1 h with e | e
    · subst e; simp
    · have hne : lb.1 ≠ k := fun e' => hn.1 (by rw [← e']; exact List.mem_map_of_mem e)
      simp only [show (lb.1 == k) = false from by simpa using hne]
      exact lookup_of_nodup L hn.2 lb e

theorem flatRs_sub : ∀ (rs : List (Lbl × TC)) (nl : Nat) (ps : List VReg) (i : Nat) (hi : i < rs.length),
    ∃ nl', ∀ x ∈ (flatT rs[i].2 ⟨nl', [], rs[i].1, if i = 0 then ps else [], []⟩).bs, x ∈ flatRs nl ps rs
  | [], _, _, _, hi => absurd hi (by simp)
  | (l, t) :: rs, nl, ps, 0, _ => ⟨nl, fun x hx => by simp only [flatRs]; exact List.mem_append_left _ (by simpa using hx)⟩
  | (l, t) :: rs, nl, ps, i + 1, hi => by
    obtain ⟨nl', h⟩ := flatRs_sub rs (flatT t ⟨nl, [], l, ps, []⟩).nl [] i (by simp at hi; omega)
    refine ⟨nl', fun x hx => ?_⟩
    simp only [flatRs]
    refine List.mem_append_right _ (h x ?_)
    simp only [List.getElem_cons_succ, Nat.add_one_ne_zero, if_false] at hx
    simpa only [ite_self] using hx

/-- **every region of `mkFunc` is found by `lookup`** (distinct region labels below the counter) -/
theorem mkFunc_region {params ps : List VReg} {nl : Nat} {rs : List (Lbl × TC)} (hn : (rs.map Prod.fst).Nodup)
    (hl : ∀ x ∈ rs, x.1 < nl) (i : Nat) (hi : i < rs.length) :
    ∃ nl', GS.OkT (mkFunc params ps nl rs) (flatT rs[i].2 ⟨nl', [], rs[i].1, if i = 0 then ps else [], []⟩) := by
  obtain ⟨nl', h⟩ := flatRs_sub rs nl ps i hi
  exact ⟨nl', fun lb hlb => lookup_of_nodup _ (flatRs_keys rs nl ps hn hl).1 lb (h lb hlb)⟩

theorem mkFunc_entry (params ps : List VReg) (nl : Nat) (l : Lbl) (t : TC) (rs : List (Lbl × TC)) :
    (mkFunc params ps nl ((l, t) :: rs)).entry = l := rfl

end Proven.Ir
