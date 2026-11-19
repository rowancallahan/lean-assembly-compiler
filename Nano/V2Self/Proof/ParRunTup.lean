/- Nano/V2Self/Proof/ParRunTup: tuples (box B).  After a `,`, the machine runs `expr 0 0 :: tupRest` (and `mkPair`s below);
`tup_sound`: that run builds the right-nested remainder node = ParSpec `pTup` on `, …`. -/
import Nano.V2Self.Proof.ParRunExprMain
namespace ParRun
open ParSpec

/-- v209 on a value PAIR (shape code ≠ 0): no input-local child -/
theorem nodeOK_pair_noInp {ds : List DefR} {a b : Nat} {s : Sh} {p : Bool} {ks : List RN}
    (h : nodeOK ds (.mk 6 a b (some s) p ks) = true) : ∀ k ∈ ks, k.isInp = false := by
  intro k hk
  cases hki : k.isInp
  · rfl
  · exfalso
    have hm : (ks.filter RN.isInp).length ≠ 0 := by
      intro h0; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0; have := h0 k hk; simp [hki] at this
    simp only [nodeOK, RN.kids, RN.tag, RN.sh, Bool.and_eq_true] at h
    obtain ⟨h1, _⟩ := h
    simp [hm] at h1

theorem pairNode_toNd {s : Option Sh} {x y : RN} (hx : x.isInp = false) (hy : y.isInp = false) :
    (RN.mk 6 2 0 s false [x, y]).toNd = .pair [x.toNd, y.toNd] := by
  rw [RN.toNd_mk]; simp [RN.toNdL_cons, RN.toNdL, hx, hy]

theorem pTup_eq {f cx r nx} : pTup (f + 1) cx (.k 15 :: r) nx =
    (pExpr f cx false r nx).bind fun (e, t, r1, nx1) =>
      match tyShape t, r1 with
      | some s, .k 7 :: r2 => some (e, s, r2, nx1)
      | some s, .k 15 :: _ => (pTup f cx r1 nx1).map fun (rest, sr, r3, nx3) => (.pair [e, rest], .p s sr, r3, nx3)
      | _, _ => none := by
  simp only [pTup]; rfl

/-- a tuple component's ParSpec shape is its machine shape -/
theorem comp_shape {v : RN} {t : Ty} {s : Sh} (hrel : TyRel v t) (hsh : v.sh = some s) (hnn : s.nnt = true) (hnt : s ≠ .nt)
    (hb : t ≠ .bot) (hi : v.isInp = false) : tyShape t = some s := by
  cases t with
  | inp => rw [hrel.1] at hi; cases hi
  | _ => exact let_shape hrel hsh hnn hnt hb (by simp)

/-- after a `,`: the remainder of a tuple -/
def TupSpec (n : Nat) : Prop := ∀ ks st fin cx, StarN n (.expr 0 0 :: .tupRest :: ks, st) ([], fin) → CxRel st cx → CxNN st →
  ∃ w st' n', n' < n ∧ Post st st' st.vals w ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧
    ShNN w.sh ∧
    (VT (rows st) w → (∀ s, w.sh = some s → s ≠ .nt) → w.isInp = false → ∃ sh, w.sh = some sh ∧
      ∀ f, 4 * st.toks.length + 5 ≤ f → pTup f cx (.k 15 :: st.toks) st.nx = some (w.toNd, sh, st'.toks, st'.nx))


theorem tup_sound : ∀ n, (∀ n' ≤ n, ExprSpec n') → TupSpec n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihT =>
  intro hE ks st fin cx h hc hnn
  -- the component
  obtain ⟨e, stE, nE, hnE, hpE, hltE, hEr, _, hnvE, hspE⟩ := hE n (Nat.le_refl _) 0 _ _ fin cx (by omega) h hc hnn
  match nE, hEr with
  | 0, hEr => exact absurd hEr.zero_nil.1 (by simp)
  | nE + 1, hEr =>
  obtain ⟨k, st1, hs1, h1⟩ := hEr.head
  rcases tupRest_inv hs1 with ⟨r, hr, rfl, rfl⟩ | ⟨r, hr, rfl, rfl⟩
  · -- `)`: the remainder is the component
    simp only [List.nil_append] at h1
    try simp only at hr hltE
    have l1 : r.length + 1 = stE.toks.length := by simp [hr]
    refine ⟨e, { stE with toks := r }, nE, by omega, ⟨hpE.vals, hpE.binds, hpE.defs, hpE.cur, hpE.arm, hpE.all,
      by have := hpE.toks; simp; omega, hpE.nx⟩, by simp; omega, h1, hnvE, fun hvt hnt hni => ?_⟩
    obtain ⟨s, hs, hsnn⟩ := hnvE
    obtain ⟨t, ht, _, hf⟩ := hspE hvt
    refine ⟨s, hs, fun f hf' => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have pE := hf g (by omega)
    simp only [show (0 == 1) = false from rfl] at pE
    have hb : t ≠ .bot := (nobot g).1 _ _ _ _ pE
    rw [pTup_eq, pE]; simp only [Option.bind_some, comp_shape ht hs hsnn (hnt s hs) hb hni, hr]
  · -- `,`: the rest of the tuple, then the pair
    simp only [List.cons_append, List.nil_append] at h1
    try simp only at hr hltE
    obtain ⟨w, st2, n2, hn2, hp2, hlt2, h2, hnv2, hsp2⟩ := ihT nE (by omega) (fun n' hn' => hE n' (by omega)) _ _ fin cx h1
      (CxRel.transport hc (by simp [hpE.binds]) (by simp [hpE.defs]) (by simp [hpE.cur]) (by simp [hpE.arm]))
      (CxNN.transport hnn (by simp [hpE.binds]) (by simp [hpE.defs]) (by simp [hpE.cur]))
    match n2, h2 with
    | 0, h2 => exact absurd h2.zero_nil.1 (by simp)
    | n2 + 1, h2 =>
    obtain ⟨k3, st3, hs3, h3⟩ := h2.head
    obtain ⟨y, x, rest, l, rr, hv3, hxl, hyr, _, _, hl, hrr, rfl, hst3⟩ := mkPair_inv hs3
    rw [hp2.vals] at hv3; simp only [List.cons.injEq] at hv3; obtain ⟨rfl, hv3⟩ := hv3
    rw [hpE.vals] at hv3; simp only [List.cons.injEq] at hv3; obtain ⟨rfl, rfl⟩ := hv3
    simp only [List.nil_append] at h3
    have hb2 := hp2.binds; have hd2 := hp2.defs; have hc2 := hp2.cur; have ha2 := hp2.arm; have hl2 := hp2.all
    have ht2 := hp2.toks; have hn2' := hp2.nx
    simp only at hb2 hd2 hc2 ha2 hl2 ht2 hn2' hlt2
    refine ⟨_, st3, n2, by omega, ⟨by rw [hst3], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, h3, ?_, fun hvt _ _ => ?_⟩
    · rw [hst3]; simp [hb2, hpE.binds]
    · rw [hst3]; simp [hd2, hpE.defs]
    · rw [hst3]; simp [hc2, hpE.cur]
    · rw [hst3]; simp [ha2, hpE.arm]
    · rw [hst3]; simp [hl2, hpE.all]
    · rw [hst3]; simp [hr] at hltE; simp; omega
    · rw [hst3]; have := hpE.nx; simp; omega
    · rw [hst3]; simp [hr] at hltE; simp; omega
    · obtain ⟨s1, hs1, hnn1⟩ := hnvE; obtain ⟨s2, hs2, hnn2⟩ := hnv2
      rw [hxl] at hs1; cases hs1; rw [hyr] at hs2; cases hs2
      refine ⟨.p l rr, by simp [RN.sh], ?_⟩
      simp [Sh.nnt, hl, hrr, hnn1, hnn2]
    -- the spec side
    have hok := hvt.self
    have hni := nodeOK_pair_noInp hok
    have hnx := hni e (by simp); have hny := hni w (by simp)
    obtain ⟨s1, hs1, hnn1⟩ := hnvE
    rw [hxl] at hs1; cases hs1
    obtain ⟨t, ht, _, hf⟩ := hspE (hvt.kid (by simp))
    obtain ⟨sr, hsr, hf2⟩ := hsp2 (by have := hvt.kid (k := w) (by simp); simpa [ParRun.rows, hpE.defs, hpE.cur] using this)
      (by intro s hs; rw [hyr] at hs; cases hs; exact hrr) hny
    rw [hyr] at hsr; cases hsr
    refine ⟨.p l rr, by simp [RN.sh], fun f hf' => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have pE := hf g (by omega)
    simp only [show (0 == 1) = false from rfl] at pE
    have hb : t ≠ .bot := (nobot g).1 _ _ _ _ pE
    have l1 : r.length + 1 = stE.toks.length := by simp [hr]
    have p2 := hf2 g (by simp; omega)
    simp only at p2
    rw [pTup_eq, pE]; simp only [Option.bind_some, comp_shape ht hxl hnn1 hl hb hnx, hr]
    rw [p2]
    simp [pairNode_toNd hnx hny, hst3]

end ParRun
