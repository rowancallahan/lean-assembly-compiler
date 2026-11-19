/- Nano/V2Self/Proof/ParRunProg: the Layer-2 PROGRAM level (box B).  `loopStep`: B's `loop_spec` in the shape F's
`defs_spec` consumes; the program theorem (Accepts ⇒ refParse = some p ∧ o = serialize p) on top of `defs_spec`. -/
import Nano.V2Self.Proof.ParRunDef
import Nano.V2Self.Proof.ParRunLoop
namespace ParRun
open ParSpec

theorem loopStep : LoopStep := by
  intro n ks st fin defs name r h ht hcur hb hv _ harm hD hNN hfr
  obtain ⟨lp, st', n', hn, hrun, hstar, hv', hd, ho, hal, hname, hloop, hlt, hspec⟩ :=
    loop_spec h ht hcur hb hv harm hD hNN hfr
  exact ⟨lp, st', n', hn, hstar, hrun, hv', hd, ho, hname, hloop, hlt, hspec⟩

/-- a parsed def with a List result that is not a fuel loop has `resLst` -/
theorem pDef_resLst {f : Nat} {defs : List DefI} {ts : List Tok} {di : DefI} {da : DefA} {r : List Tok}
    (h : pDef f defs ts = some (di, da, r)) (hres : di.res = .ls) (hhd : di.params.head? ≠ some .fuel) :
    di.resLst = true := by
  unfold pDef at h
  split at h
  · rename_i name ts'
    split at h
    · cases h
    split at h
    · -- the loop branch: params start with the fuel
      exfalso
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨tys, r1⟩, _, h⟩ := h
      split at h
      · split at h
        · cases h
        split at h
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨⟨zn, r3⟩, _, h⟩ := h
          split at h
          · cases h
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨envZ, _, ⟨⟨z, tz, r4, nx1⟩, _, h⟩⟩ := h
          split at h
          · cases h
          split at h
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨⟨sn, r6⟩, _, h⟩ := h
            split at h
            · cases h
            simp only [Option.bind_eq_some_iff] at h
            obtain ⟨envS, _, ⟨⟨s, ts'', r7, nx2⟩, _, h⟩⟩ := h
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, _, _⟩ := h
              exact hhd rfl
            · cases h
          · cases h
        · cases h
      · cases h
    · -- the plain branch
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨groups, r1⟩, _, h⟩ := h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨⟨resT, r3⟩, hT, h⟩ := h
        split at h
        · split at h
          · cases h
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨⟨b, tb, r5, nx⟩, _, h⟩ := h
          split at h
          · cases h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _, _⟩ := h
          have hn := (pTy_noLs f).2 _ _ _ hT
          simp only at hres ⊢
          have := (trRes_ls hn).mp hres
          subst this; rfl
        · cases h
      · cases h
  · cases h

def ResLstOK (d : DefI) : Prop := d.res = .ls → d.params.head? ≠ some .fuel → d.resLst = true

theorem pDefs_resLst {F : Nat} : ∀ (G : Nat) {dis dis' : List DefI} {ts : List Tok} {as : List DefA},
    pDefs F G dis ts = some (dis', as) → (∀ d ∈ dis, ResLstOK d) → ∀ d ∈ dis', ResLstOK d
  | 0, _, _, _, _, h, _ => by simp [pDefs] at h
  | G + 1, dis, dis', ts, as, h, hd => by
    cases ts with
    | nil => simp [pDefs] at h; obtain ⟨rfl, _⟩ := h; exact hd
    | cons t ts =>
      rw [pDefs_cons] at h
      obtain ⟨⟨di, da, r⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨ds, as'⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
      simp only [Prod.mk.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4
      refine pDefs_resLst G h3 (fun d hdm => ?_)
      rcases List.mem_append.mp hdm with hdm | hdm
      · exact hd d hdm
      · simp at hdm; subst hdm; exact fun hr hh => pDef_resLst h1 hr hh

theorem findDef_get {l : List DefI} {x : List Nat} {j : Nat} {di : DefI} (h : findDef l x = some (j, di)) :
    l[j]? = some di ∧ di.name = x := by
  unfold findDef at h
  obtain ⟨⟨d, i⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
  have hm := List.mem_of_find?_eq_some h1
  have hp := List.find?_some h1
  simp only [beq_iff_eq] at hp
  rw [List.mem_zipIdx_iff_getElem?] at hm
  exact ⟨by simpa using hm, hp⟩

theorem findD_last {ds : List DefR} {d : DefR} (h : ds.getLast? = some d) : findD ds d.name = some (ds.length - 1) := by
  unfold findD
  have hne : ds ≠ [] := by intro e; subst e; simp at h
  obtain ⟨init, rfl⟩ : ∃ init, ds = init ++ [d] := List.getLast?_eq_some_iff.mp h
  simp [List.findIdx?_cons]

/-- **Layer-2 parser soundness**: an accepted run's output is the serialization of the reference parse. -/
theorem accepts_sound {ts : List UInt64} {toks : List Tok} (htok : tokens ts = some toks) :
    ∀ o, Accepts toks o → ∃ p, ParsesProgram ts p ∧ o = serialize p := by
  intro o ⟨fin, hstar, hacc, hmain, hout⟩
  obtain ⟨n, hN⟩ := hstar.toN
  have hD0 : DRel (init toks).defs [] :=
    ⟨rfl, fun x => by simp [findDef, findD, init], fun x j di h => by simp [findDef] at h⟩
  have hNN0 : DefsNN (init toks).defs := by simp [DefsNN, init]
  obtain ⟨dis', as, hp, hfo, hDR, _⟩ := defs_spec loopStep n hN hD0 hNN0 ⟨[], rfl⟩
  -- the main row
  unfold mainOK at hmain
  split at hmain
  · rename_i d hlast
    simp only [Bool.and_eq_true, beq_iff_eq] at hmain
    obtain ⟨⟨⟨⟨hname, _⟩, hl1⟩, hhd⟩, hres⟩ := hmain
    obtain ⟨hlen, hdefs, hrow⟩ := hDR
    have hfd := hdefs d.name
    rw [findD_last hlast] at hfd
    obtain ⟨⟨j, di⟩, hfd', hj⟩ := Option.map_eq_some_iff.mp hfd
    simp only at hj; subst hj
    obtain ⟨hget, hdn⟩ := findDef_get hfd'
    obtain ⟨d', hd', hpar, hres', hinp, _⟩ := hrow _ _ di hfd'
    have hne : fin.defs ≠ [] := by intro e; rw [e] at hlast; simp at hlast
    have hd'' : d' = d := by
      rw [List.getLast?_eq_getElem?] at hlast; rw [hlast] at hd'; cases hd'; rfl
    subst hd''
    have hlast' : dis'.getLast? = some di := by
      rw [List.getLast?_eq_getElem?, ← hlen]; exact hget
    -- isMain
    obtain ⟨p0, hp0⟩ : ∃ p0, di.params = [p0] := by
      have hl : di.params.length = 1 := by rw [← hl1, ← hpar]; simp
      match hq : di.params, hl with
      | [p0], _ => exact ⟨p0, rfl⟩
    have hcode : psCode p0 = .ls := by
      have := congrArg List.head? hpar; rw [hp0, hhd] at this; simpa using this
    have hpinp : p0 = .inp := by
      have h0 := (hinp 0 (by simp [hp0])).mpr
      simp only [hp0, List.getElem_cons_zero] at h0
      apply h0
      refine ⟨?_, fun j hj => absurd hj (by omega)⟩
      rw [← hpar, hp0]; simp [hcode]
    have hresl : di.res = .ls := by rw [hres] at hres'; exact (Option.some.inj hres').symm
    have hrl : di.resLst = true := by
      have hall := pDefs_resLst (toks.length + 1) (hp (8 * toks.length + 8) (toks.length + 1) (by simp [init]; omega)
        (by simp [init])) (fun d hd => by simp at hd)
      exact hall di (List.mem_of_getElem? hget) hresl (by rw [hp0, hpinp]; simp)
    have hmainD : isMain di = true := by
      simp [isMain, hrl, hp0, hpinp, hdn, hname]
    refine ⟨as, ?_, ?_⟩
    · unfold ParsesProgram refParse
      rw [htok]
      simp only [Option.bind_some]
      have := hp (8 * toks.length + 8) (toks.length + 1) (by simp [init]; omega) (by simp [init])
      simp only [init] at this
      rw [this]
      simp [hlast', hmainD]
    · rw [← hout, hfo]; simp [init, serialize]
  · cases hmain

end ParRun
