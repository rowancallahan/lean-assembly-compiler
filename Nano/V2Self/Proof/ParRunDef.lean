/- Nano/V2Self/Proof/ParRunDef: Layer-2 def level (parser lead), pure.  Expression-family frames never emit output; a plain def
from `.binders` to the next `.defs` is `pDef`'s plain branch (`plainB_spec`). -/
import Nano.V2Self.Proof.ParRunBody
import Nano.V2Self.Proof.ParRunShape
import Nano.V2Self.Proof.ParTreeOK
namespace ParRun
open ParSpec

/-- frames that write output -/
def isOutF : Frame → Bool
  | .defEnd | .flat _ | .flatL _ | .defClose => true
  | _ => false

/-- a frame that is neither def-level nor an output frame keeps the output and pushes only such frames -/
theorem stepF_noOut {f : Frame} {st st' : St} {k : List Frame} (hD : isD f = false) (hO : isOutF f = false)
    (h : stepF f st = some (k, st')) : st'.out = st.out ∧ k.all (fun g => !isD g && !isOutF g) = true := by
  cases f <;> simp only [isD, isOutF] at hD hO <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases hD; done)
    | (cases hO; done)
    | (cases h; done)
    | (cases h; exact ⟨rfl, by decide⟩)
    | (cases h; exact ⟨rfl, by simp [isD, isOutF]⟩)
    | (cases h; exact ⟨by simp [leaf], by simp [isD, isOutF]⟩)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       refine ⟨?_, by simp [isD, isOutF]⟩
       first
       | (rw [mkNode_out h2]; done)
       | (rw [locOf_out h2]; done)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          rw [mkNode_out h2', mkNode_out h1]; done))

/-- runs of such frames keep the output -/
theorem Star.noOut {c d : List Frame × St} (h : Star c d) (hk : c.1.all (fun g => !isD g && !isOutF g) = true) :
    d.2.out = c.2.out ∧ d.1.all (fun g => !isD g && !isOutF g) = true := by
  induction h with
  | refl => exact ⟨rfl, hk⟩
  | @step c c1 d hs _ ih =>
    obtain ⟨fs, st⟩ := c
    cases fs with
    | nil => simp [stepS] at hs
    | cons f rest =>
      obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hk
      obtain ⟨⟨hD, hO⟩, hr⟩ := hk
      obtain ⟨e1, e2⟩ := stepF_noOut hD hO h1
      obtain ⟨e3, e4⟩ := ih (by simp [List.all_append, e2, hr])
      exact ⟨e3.trans e1, e4⟩


theorem pBinders_noLs : ∀ (f : Nat) (b : Bool) (ts : List Tok) (g : List (List (List Nat) × TyR)) (r : List Tok),
    pBinders f b ts = some (g, r) → ∀ x ∈ g, x.2 ≠ .sh .ls := by
  intro f
  induction f with
  | zero => intro b ts g r h; simp [pBinders] at h
  | succ f ih =>
    intro b ts g r h x hx
    rw [pBinders.eq_def] at h
    simp only at h
    split at h
    all_goals first
      | (cases h; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp at hx; done)
      | (obtain rfl : f = _ := Nat.succ.inj ‹f + 1 = _›
         obtain ⟨⟨ns, r1⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h
         simp only at h2
         split at h2
         · obtain ⟨⟨t, r3⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
           simp only at h4
           split at h4
           all_goals first
             | (cases h4; done)
             | (obtain ⟨⟨g', r5⟩, h5, h6⟩ := Option.map_eq_some_iff.mp h4
                simp only [Prod.mk.injEq] at h6; obtain ⟨rfl, rfl⟩ := h6
                rcases List.mem_cons.mp hx with rfl | hx
                · exact (pTy_noLs f).2 _ _ _ h3
                · exact ih _ _ _ _ h5 x hx)
         · cases h2)

theorem mem_go_kind (p : Ps) : ∀ (s : Nat) (ns : List (List Nat)) (e : List Nat × Nat × Ps), e ∈ (bindSlots.go p s ns).1 → e.2.2 = p := by
  intro s ns e he
  induction ns generalizing s with
  | nil => simp [go_nil] at he
  | cons x l ih =>
    rw [go_cons] at he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact ih _ he

theorem mem_bindSlots_kind : ∀ (g : List (List (List Nat) × TyR)) (s : Nat) (u : Bool) (e : List Nat × Nat × Ps),
    e ∈ (bindSlots s u g).1 → e.2.2 ∈ (bindSlots s u g).2.1
  | [], s, u, e, he => by simp [bindSlots_nil] at he
  | (ns, t) :: g, s, u, e, he => by
    rw [bindSlots_cons] at he ⊢
    rcases List.mem_append.mp he with he | he
    · apply List.mem_append_left
      rw [mem_go_kind _ _ _ _ he, go_ps]
      cases ns with
      | nil => simp [go_nil] at he
      | cons y l => simp
    · exact List.mem_append_right _ (mem_bindSlots_kind g _ _ e he)


/-- the state right after `.defs` opened def `x` -/
structure DefStart (st : St) (x : List Nat) : Prop where
  binds : st.binds = []
  vals : st.vals = []
  arena : st.arena = []
  nx : st.nx = 0
  arm : st.arm = false
  cur : st.cur = DefR.fresh x

/-- finished rows carry no nested Nat (the `rows` half of B's `CxNN`) -/
def DefsNN (ds : List DefR) : Prop := ∀ d ∈ ds, ShNN d.res ∧ ∀ p ∈ d.params, p.nnt = true

/-- with the arm flag off, an expression run leaves no pending value (no self-call; to be discharged) -/
def NoPend : Prop := ∀ (st st' : St), st.arm = false → st.vals = [] → Star ([.expr 0 0], st) ([], st') → ∀ v ∈ st'.vals, v.pend = false

/-- **plain def with binders**: from `.binders` (after `def x`, first token `(`) to the next `.defs` -/
theorem plainB_spec (hNP : NoPend) {n : Nat} {ks : List Frame} {st0 fin : St} {x : List Nat} {dis : List DefI}
    (h : StarN n (.binders :: ks, st0) ([], fin)) (hS : DefStart st0 x) (hD : DRel st0.defs dis) (hNN : DefsNN st0.defs)
    (hfr : findD st0.defs x = none) (hn8 : ∀ r, st0.toks ≠ .k 8 :: r) :
    ∃ st2 n', n' < n ∧ StarN n' (.defs :: ks, st2) ([], fin) ∧ st2.toks.length < st0.toks.length ∧
      (st2.arena.all (nodeOK st2.defs) = true →
        ∃ di da, (∀ f, 4 * st0.toks.length + 4 ≤ f → pDef f dis (.k 1 :: .id x :: st0.toks) = some (di, da, st2.toks)) ∧
          st2.out = st0.out ++ da.ser ∧ DRel st2.defs (dis ++ [di]) ∧ DefsNN st2.defs) := by
  obtain ⟨g, r, n1, ty', nni', hn1, hlr, hpB, hps, hFJ, h1⟩ := binders_spec n true h
  simp only [hS.binds, hS.nx, List.any_nil, List.nil_append] at hps hFJ h1
  have hkind := mem_bindSlots_kind g 0 false
  have hinp := bindSlots_inpInv g false 0 [] ⟨fun i h => absurd h (by simp), fun _ q hq => by simp at hq⟩ rfl hFJ
    (pBinders_noLs _ true _ g _ (hpB _ (Nat.le_refl _)))
  generalize hbs : bindSlots 0 false g = BS at hps h1 hkind hinp
  obtain ⟨E, PS, NPW⟩ := BS
  simp only [List.nil_append] at hinp
  dsimp only at hps h1
  obtain ⟨resT, r3, n2, hn2, hl3, hpT, h2, hnnt⟩ := (ty_sound n1).1 h1
  dsimp only at hl3 hpT h2
  have hcur0 : st0.cur.params = [] := by rw [hS.cur]; rfl
  have hE : ∀ e ∈ E, e.2.2 ≠ .fuel ∧ psCode e.2.2 ≠ .nt := fun e he => let h := hps _ (hkind e he); ⟨h.1, h.2.1⟩
  obtain ⟨r4, v, st', n3, hn3, ht4, hw, hP, h3, hstar, hNNv, _, hV⟩ := body_spec h2 rfl (cxrel_body hD rfl hE hS.arm) hS.arm (by
    refine ⟨fun bd hbd => ?_, fun d hd => ?_⟩
    · simp only [St.withTy, List.mem_map] at hbd
      obtain ⟨e, he, rfl⟩ := hbd
      exact ⟨_, rfl, (hps _ (hkind e he)).2.2⟩
    · simp only [rows, St.withTy, List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact hNN d hd
      · refine ⟨⟨_, rfl, hnnt⟩, fun p hp => ?_⟩
        simp only [bodyRow, St.withTy, hcur0, List.nil_append, List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        exact (hps q hq).2.2)
  simp only [St.withTy, bodyRow] at hP hV hstar ht4 hw
  obtain ⟨z, n4, hn4, hz, hzs, hzi, h4⟩ := defEnd_tail h3
  have hvz : z = v := by rw [hP.vals, hS.vals] at hz; simpa using hz.symm
  subst hvz
  have hl4 : st'.toks.length < st0.toks.length := by
    have := hP.toks; simp only at this; rw [ht4] at hl3; simp at hl3; omega
  refine ⟨_, n4, by omega, h4, hl4, fun hval => ?_⟩
  dsimp only at hval
  have inv := Star.inv hstar ⟨by simp [ArenaInv, hS.arena, hS.vals], by simp [CntInv, hS.arena]⟩
  dsimp only at inv
  have hA : st'.arena = nodes z := by rw [inv.1, hP.vals, hS.vals]; simp
  have hall : ∀ m ∈ nodes z, cntOK m = true ∧ nodeOK (st'.defs ++ [st'.cur]) m = true := fun m hm =>
    ⟨inv.2 m (by rw [hA]; exact hm), List.all_eq_true.mp hval m (by rw [hA]; exact hm)⟩
  obtain ⟨ty, hTy, _, hpE⟩ := hV (fun u hu => by have := (hall u hu).2; rw [hP.defs, hP.cur] at this; exact this)
  have hwords := words_body hall
  have hfr' : findDef dis x = none := by
    have := hD.2.1 x; rw [hfr] at this; cases h : findDef dis x <;> simp_all
  refine ⟨{ name := x, params := PS, res := trRes resT, resLst := (match resT with | .lst => true | _ => false), npw := NPW },
    { id := dis.length, npw := NPW, nslots := st'.nx, kind := 0, nres := (trRes resT).width, body := z.toNd },
    fun f hf => ?_, ?_, ?_, ?_⟩
  · simp only [pDef, hfr', Option.isSome_none, Bool.false_eq_true, if_false]
    split
    · rename_i r' he; exact absurd he (hn8 _)
    · have hzres : z.sh = some (trRes resT) := by rw [hzs, hP.cur]
      have hok : tyOk (trRes resT) ty = true := by
        cases ty with
        | s w' => obtain ⟨e1, _, _⟩ := hTy; rw [hzres] at e1; simp only [Option.some.injEq] at e1; simp [tyOk, e1]
        | lit => obtain ⟨e1, _⟩ := hTy; rw [hzres] at e1; simp only [Option.some.injEq] at e1; simp [tyOk, e1]
        | inp => exact absurd hTy.1 (by simp [hzi])
        | bot =>
          have := hNP _ _ (by simpa using hS.arm) (by simpa using hS.vals) hstar z (by rw [hP.vals]; simp)
          exact absurd hTy (by simp [TyRel, this])
      have hN1 : (trRes resT).hasN = false := Sh.hasN_of_nnt hnnt hw
      have hN2 : (PS.any fun p => match p with | Ps.sh s => s.hasN | _ => false) = false := by
        rw [List.any_eq_false]; intro p hp
        obtain ⟨h1, h2, h3⟩ := hps p hp
        cases p with
        | inp => simp
        | fuel => exact absurd rfl h1
        | sh w' => simp only [psCode] at h2 h3; simp [Sh.hasN_of_nnt h3 h2]
      rw [hpB f (by omega)]
      simp only [Option.bind_some]
      subst ht4
      simp only [List.length_cons] at hl3
      rw [hpT f (by omega)]
      simp only [Option.bind_some, hbs, hN1, hN2, Bool.or_false, Bool.false_eq_true, if_false]
      rw [hpE f (by omega)]
      simp [hok]
      refine ⟨fun p hp => by simpa using List.any_eq_false.mp hN2 p hp, ?_⟩
      cases resT <;> rfl
  · have eo := (Star.noOut hstar (by simp [isD, isOutF])).1
    dsimp only at eo
    have hc := hP.cur
    have hd := hP.defs
    dsimp only at hc hd
    simp only [eo, defHdr, hc, hd, hD.1, DefA.ser, hwords, cw, List.append_assoc, Bool.false_eq_true, if_false]
    rfl
  · have hc := hP.cur
    have hd := hP.defs
    dsimp only at hc hd
    show DRel (st'.defs ++ [st'.cur]) _
    rw [hd, hc]
    have hname : st0.cur.name = x := by rw [hS.cur]; rfl
    refine drel_snoc hD (by simpa [hname] using hfr) (by simp [hname]) (by simp [hcur0]) rfl (fun i h => ?_) (fun p hp e => ?_)
    · rw [hinp.1 i h]; simp [hcur0]
    · subst e; exact (hps _ hp).2.1 rfl
  · have hc := hP.cur
    have hd := hP.defs
    dsimp only at hc hd
    show DefsNN (st'.defs ++ [st'.cur])
    rw [hd, hc]
    intro d hd'
    rcases List.mem_append.mp hd' with hd' | hd'
    · exact hNN d hd'
    · simp at hd'; subst hd'
      refine ⟨⟨_, rfl, hnnt⟩, fun p hp => ?_⟩
      simp only [hcur0, List.nil_append, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact (hps q hq).2.2

end ParRun
