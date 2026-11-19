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

/-- **plain def with binders**: from `.binders` (after `def x`, first token `(`) to the next `.defs` -/
theorem plainB_spec {n : Nat} {ks : List Frame} {st0 fin : St} {x : List Nat} {dis : List DefI}
    (h : StarN n (.binders :: ks, st0) ([], fin)) (hS : DefStart st0 x) (hD : DRel st0.defs dis) (hNN : DefsNN st0.defs)
    (hfr : findD st0.defs x = none) (hnl : ∀ r, st0.toks ≠ .k 8 :: .k 35 :: .k 17 :: r) :
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
    · have hzres : z.sh = some (trRes resT) := by rw [hzs, hP.cur]
      have hok : tyOk (trRes resT) ty = true := by
        cases ty with
        | s w' => obtain ⟨e1, _, _⟩ := hTy; rw [hzres] at e1; simp only [Option.some.injEq] at e1; simp [tyOk, e1]
        | lit => obtain ⟨e1, _⟩ := hTy; rw [hzres] at e1; simp only [Option.some.injEq] at e1; simp [tyOk, e1]
        | inp => exact absurd hTy.1 (by simp [hzi])
        | bot =>
          exact absurd rfl ((nobot f).1 _ _ _ _ (hpE f (by rw [ht4] at hl3; simp at hl3; omega)))
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


/-- counted runs concatenate along a frame split -/
theorem StarN.cat {n1 n2 : Nat} {k ks : List Frame} {S S' fin : St} (h1 : StarN n1 (k, S) ([], S')) (h2 : StarN n2 (ks, S') ([], fin)) :
    StarN (n1 + n2) (k ++ ks, S) ([], fin) := by
  induction n1 generalizing k S with
  | zero => obtain ⟨rfl, rfl⟩ := h1.zero_nil; simpa using h2

  | succ n ih =>
    match k, h1 with
    | f :: k', h1 =>
      obtain ⟨k2, st2, e1, e2⟩ := h1.head
      have := ih e2
      rw [List.append_assoc] at this
      rw [show n + 1 + n2 = (n + n2) + 1 by omega]
      exact .step (stepS_some.mpr ⟨_, _, e1, rfl⟩) this

/-- on `:=`, `afterColon` behaves as `plainBody` -/
theorem afterColon_k9 {st : St} {r : List Tok} (ht : st.toks = .k 9 :: r) : stepF .afterColon st = stepF .plainBody st := by
  simp only [stepF, ht]
  try (by_cases h : st.ty = some .nt <;> simp [h])

theorem StarN.afterColon_k9 {n : Nat} {ks : List Frame} {st fin : St} {r : List Tok} (ht : st.toks = .k 9 :: r)
    (h : StarN n (.afterColon :: ks, st) ([], fin)) : StarN n (.plainBody :: ks, st) ([], fin) := by
  cases h with
  | step hs h' => exact .step (by rw [stepS_cons, ← ParRun.afterColon_k9 ht, ← stepS_cons]; exact hs) h'


theorem pTy_nat_arrow (f : Nat) (r : List Tok) : pTy (f + 2) (.k 35 :: .k 17 :: r) = some (.sh .nt, .k 17 :: r) := by
  rw [pTy_succ']
  simp [pTyAtom, crossK]

/-- **plain def without binders** (`def x : T := e`): reduces to `plainB_spec` (the binders frame on `:` pushes exactly
`[tyAtom, plainBody]`); otherwise the run is the fuel-loop header (`afterColon` on `→`, B's `loop_spec`) -/
theorem plainC_spec {n : Nat} {ks : List Frame} {S fin : St} {x : List Nat} {dis : List DefI}
    (h : StarN n (.tyAtom :: .afterColon :: ks, S) ([], fin)) (hS : DefStart S x) (hD : DRel S.defs dis) (hNN : DefsNN S.defs)
    (hfr : findD S.defs x = none) :
    (∃ st' n', n' ≤ n ∧ Star ([.tyAtom], S) ([], st') ∧ StarN n' (.afterColon :: ks, st') ([], fin) ∧ ∃ r, st'.toks = .k 17 :: r) ∨
    (∃ st2 n', n' ≤ n ∧ StarN n' (.defs :: ks, st2) ([], fin) ∧ st2.toks.length < S.toks.length + 1 ∧
      (st2.arena.all (nodeOK st2.defs) = true →
        ∃ di da, (∀ f, 4 * (S.toks.length + 1) + 4 ≤ f → pDef f dis (.k 1 :: .id x :: .k 8 :: S.toks) = some (di, da, st2.toks)) ∧
          st2.out = S.out ++ da.ser ∧ DRel st2.defs (dis ++ [di]) ∧ DefsNN st2.defs)) := by
  obtain ⟨st', n1, n2, hn, e1, e2⟩ := StarN.split (k := [.tyAtom]) (ks := .afterColon :: ks) h
  rcases ht : st'.toks with _ | ⟨tk, r9⟩
  · match n2, e2 with
    | n2 + 1, e2 => obtain ⟨_, _, h1, _⟩ := e2.head; simp [stepF, ht] at h1
  · cases tk with
    | num v => match n2, e2 with
      | n2 + 1, e2 => obtain ⟨_, _, h1, _⟩ := e2.head; simp [stepF, ht] at h1
    | id y => match n2, e2 with
      | n2 + 1, e2 => obtain ⟨_, _, h1, _⟩ := e2.head; simp [stepF, ht] at h1
    | k c =>
      by_cases c17 : c = 17
      · subst c17; exact Or.inl ⟨st', n2, by omega, e1.toStar, e2, r9, ht⟩
      by_cases c9 : c = 9
      · subst c9
        right
        have e2' := StarN.afterColon_k9 ht e2
        have hcat := StarN.cat e1 e2'
        have hB : StarN (n1 + n2 + 1) (.binders :: ks, { S with toks := .k 8 :: S.toks }) ([], fin) :=
          .step (stepS_some.mpr ⟨[.tyAtom, .plainBody], S, by simp [stepF], rfl⟩) hcat
        have hnl : ∀ r, (.k 8 :: S.toks : List Tok) ≠ .k 8 :: .k 35 :: .k 17 :: r := by
          intro r e
          simp only [List.cons.injEq, true_and] at e
          obtain ⟨t, r', n', _, _, hpT, e3, _⟩ := (ty_sound n1).1 e1
          obtain ⟨_, he⟩ := StarN.nil_inv e3
          have := hpT (2 * S.toks.length + 2) (Nat.le_refl _)
          rw [e, show 2 * (Tok.k 35 :: Tok.k 17 :: r).length + 2 = (2 * (Tok.k 35 :: Tok.k 17 :: r).length) + 2 from rfl,
            pTy_nat_arrow] at this
          simp only [Option.some.injEq, Prod.mk.injEq] at this
          obtain ⟨_, hr'⟩ := this
          have hst : st'.toks = r' := by have := congrArg (fun c => c.2.toks) he; simpa using this
          rw [ht, ← hr'] at hst
          simp at hst
        obtain ⟨st2, n', hn', h2, hl, hv⟩ := plainB_spec hB ⟨hS.binds, hS.vals, hS.arena, hS.nx, hS.arm, hS.cur⟩ hD hNN hfr hnl
        exact ⟨st2, n', by omega, h2, by simpa using hl, fun hval => by simpa using hv hval⟩
      · match n2, e2 with
        | n2 + 1, e2 => obtain ⟨_, _, h1, _⟩ := e2.head; simp [stepF, ht, c9, c17] at h1


/-! ## tokens are consumed from the front -/
theorem mkNode_toks {st st' : St} {t a b : Nat} {s : Option Sh} {p : Bool} {n : Nat}
    (h : mkNode st t a b s p n = some st') : st'.toks = st.toks ∧ st'.all = st.all := by
  unfold mkNode at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

theorem locOf_toks {st st' : St} {bd : Bd} (h : locOf st bd = some st') : st'.toks = st.toks ∧ st'.all = st.all := by
  unfold locOf at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

/-- every handler keeps `all` and leaves a suffix of the tokens -/
theorem stepF_toks {f : Frame} {st st' : St} {k : List Frame} (h : stepF f st = some (k, st')) :
    st'.all = st.all ∧ st'.toks <:+ st.toks := by
  cases f <;> simp only [stepF] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; exact ⟨rfl, List.suffix_refl _⟩)
    | (cases h; refine ⟨rfl, ?_⟩; simp_all [List.suffix_cons_iff]; done)
    | (cases h; refine ⟨rfl, ?_⟩; simp [leaf]; done)
    | (cases h; refine ⟨rfl, ?_⟩; simp_all [leaf, List.suffix_cons_iff]; done)
    | (cases h; refine ⟨rfl, ?_⟩; simp_all; done)
    | (obtain ⟨s2, h2, h3⟩ := Option.map_eq_some_iff.mp h; cases h3
       first
       | (obtain ⟨e1, e2⟩ := mkNode_toks h2; rw [e1, e2]; simp_all [List.suffix_cons_iff]; done)
       | (obtain ⟨e1, e2⟩ := locOf_toks h2; rw [e1, e2]; simp_all [List.suffix_cons_iff]; done)
       | (obtain ⟨s1, h1, h2'⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨e1, e2⟩ := mkNode_toks h1
          obtain ⟨e3, e4⟩ := mkNode_toks h2'
          rw [e3, e4, e1, e2]; simp_all [List.suffix_cons_iff]))


theorem Star.toks {c d : List Frame × St} (h : Star c d) : d.2.all = c.2.all ∧ d.2.toks <:+ c.2.toks := by
  induction h with
  | refl => exact ⟨rfl, List.suffix_refl _⟩
  | @step c c1 d hs _ ih =>
    obtain ⟨fs, st⟩ := c
    cases fs with
    | nil => simp [stepS] at hs
    | cons f rest =>
      obtain ⟨k, st', h1, rfl⟩ := stepS_some.mp hs
      obtain ⟨e1, e2⟩ := stepF_toks h1
      exact ⟨ih.1.trans e1, ih.2.trans e2⟩

/-- how the spec's type parser can produce `Nat`: the bare keyword, or a parenthesized type (last token `)`) -/
theorem pTy_nt_form : ∀ (f : Nat) (T R : List Tok), pTy f T = some (.sh .nt, R) →
    ∃ C, T = C ++ R ∧ (C = [.k 35] ∨ C.getLast? = some (.k 7)) := by
  intro f
  induction f using Nat.strongRecOn with
  | _ f ih =>
  intro T R h
  match f, h with
  | f + 1, h =>
    rw [pTy_succ'] at h
    obtain ⟨⟨a, r1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    unfold crossK at h2
    simp only at h2
    split at h2
    · obtain ⟨⟨b, r3⟩, _, h4⟩ := Option.bind_eq_some_iff.mp h2
      simp at h4
    · simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rw [pTyAtom.eq_def] at h1
      simp only at h1
      split at h1
      all_goals first
        | (cases h1; done)
        | (simp only [Option.some.injEq, Prod.mk.injEq, TyR.sh.injEq] at h1; obtain ⟨h1a, rfl⟩ := h1; cases h1a; done)
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨h1a, rfl⟩ := h1; cases h1a; done)
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨_, rfl⟩ := h1
           exact ⟨[.k 35], rfl, Or.inl rfl⟩)
        | (obtain ⟨⟨t1, r2⟩, h3, h5⟩ := Option.bind_eq_some_iff.mp h1
           simp only at h5
           split at h5
           · simp only [Option.some.injEq, Prod.mk.injEq] at h5
             obtain ⟨rfl, rfl⟩ := h5
             obtain ⟨C', hC', _⟩ := ih _ (by omega) _ _ h3
             exact ⟨.k 6 :: (C' ++ [.k 7]), by simp_all, Or.inr (by rw [← List.cons_append]; exact List.getLast?_concat)⟩
           · cases h5)


theorem getLast?_take_append (pre C R : List Tok) (hC : C ≠ []) :
    ((pre ++ C ++ R).take ((pre ++ C ++ R).length - R.length)).getLast? = C.getLast? := by
  have : (pre ++ C ++ R).length - R.length = (pre ++ C).length := by simp; omega
  rw [this, List.take_left]
  rw [List.getLast?_append]
  cases h : C.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) hC
  | some c => simp

/-- **loop header tokens**: if the run takes `afterColon`'s `→` branch, the header was literally `Nat →` -/
theorem loop_toks {ks : List Frame} {S st' fin : St} {n' : Nat} {r : List Tok} (hall : ∃ pre, S.all = pre ++ S.toks)
    (e1 : Star ([.tyAtom], S) ([], st')) (e2 : StarN n' (.afterColon :: ks, st') ([], fin)) (ht : st'.toks = .k 17 :: r) :
    S.toks = .k 35 :: .k 17 :: r := by
  obtain ⟨m, e1N⟩ := e1.toN
  obtain ⟨t, R, n'', _, _, hpT, e3, _⟩ := (ty_sound m).1 e1N
  obtain ⟨_, he⟩ := StarN.nil_inv e3
  have hst : st' = S.withTy R (trRes t) := by have := congrArg Prod.snd he; simpa using this
  subst hst
  simp only [St.withTy_toks] at ht
  subst ht
  match n', e2 with
  | n' + 1, e2 =>
    obtain ⟨k, _, h1, _⟩ := e2.head
    simp only [stepF, St.withTy_toks] at h1
    split at h1
    · rename_i hc
      obtain ⟨hty, hprev⟩ := hc
      simp only [St.withTy_ty, Option.some.injEq] at hty
      have ht' : t = .sh .nt := by cases t with
        | lst => simp [trRes] at hty
        | sh w => simp [trRes] at hty; rw [hty]
      subst ht'
      obtain ⟨C, hC, hform⟩ := pTy_nt_form _ _ _ (hpT (2 * S.toks.length + 2) (Nat.le_refl _))
      obtain ⟨pre, hpre⟩ := hall
      have hCne : C ≠ [] := by
        rcases hform with rfl | h
        · simp
        · intro e; subst e; simp at h
      have hp : prevTok (S.withTy (.k 17 :: r) (trRes (.sh .nt))) = C.getLast? := by
        simp only [prevTok, St.withTy]
        rw [hpre, hC, ← List.append_assoc]
        exact getLast?_take_append pre C _ hCne
      rw [hp] at hprev
      rcases hform with rfl | h
      · simpa using hC
      · rw [h] at hprev; simp at hprev
    · cases h1

end ParRun
