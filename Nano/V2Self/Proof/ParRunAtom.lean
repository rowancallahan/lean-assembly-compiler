/- Nano/V2Self/Proof/ParRunAtom: Layer 2 → ParSpec for the LEAF ATOMS (box G).
`CxRel st cx`: the Layer-2 tables (bindings, finished def rows) are ParSpec's context (`findB` = `findEnv`, `findD` = `findDef`).
`TyRel v ty`: what a ParSpec type says about the arena node.  `atomLeaf_spec`: every `AtomLeaf` step is the corresponding
clause of `ParSpec.pAtom` at EVERY fuel ≥ 1, with result node `v.toNd`. -/
import Nano.V2Self.Proof.ParRunPrim
namespace ParRun
open ParSpec

/-- the ParSpec kind of a typed binding -/
def bdPs (bd : Bd) : Option Ps :=
  if bd.inp then some .inp else
  match bd.sh with
  | some .nt => some .fuel
  | some s => some (.sh s)
  | none => none

/-- parameter `i` is the first code-`ls` parameter -/
def FirstLs (ws : List Sh) (i : Nat) : Prop := ws[i]? = some .ls ∧ ∀ j, j < i → ws[j]? ≠ some .ls

/-- Layer-2 tables ↔ ParSpec context -/
structure CxRel (st : St) (cx : Cx) : Prop where
  /-- every binding is typed (binder placeholders exist only while a binder group is parsed) -/
  typed : ∀ x bd, findB st.binds x = some bd → bd.sh.isSome
  /-- the input binding is a List -/
  inp : ∀ x bd, findB st.binds x = some bd → bd.inp = true → bd.sh = some .ls
  /-- name resolution -/
  env : ∀ x, findEnv cx.env x = (findB st.binds x).bind fun bd => (bdPs bd).map fun p => (bd.slot, p)
  /-- def lookup among the FINISHED defs -/
  defs : ∀ x, (findDef cx.defs x).map (fun e => e.1) = findD st.defs x
  /-- a finished row is its DefI; its input parameter is the row's first List code (fix J), and no parameter is a bare Nat shape -/
  row : ∀ x j di, findDef cx.defs x = some (j, di) → ∃ d, st.defs[j]? = some d ∧ di.params.map psCode = d.params ∧ d.res = some di.res ∧
    (∀ (i : Nat) (h : i < di.params.length), (di.params[i] = .inp ↔ FirstLs d.params i)) ∧ ∀ p ∈ di.params, p ≠ .sh .nt
  /-- the def being parsed (self-call target) is not among the finished defs (ParSpec.pDef rejects duplicates) -/
  selfFresh : ∀ sn sps, cx.self = some (sn, sps) → findDef cx.defs sn = none
  /-- in a step arm (box B, self-calls): the self context is the current row minus its fuel parameter -/
  self : st.arm = true → ∃ sps, cx.self = some (st.cur.name, sps) ∧ sps ≠ [] ∧
    sps ≠ [.inp] ∧ -- TEMPORARY (Par1 finding L: a lone input state); derivable from validation once Par1 checks it
    sps.map psCode = st.cur.params.tail ∧
    (∀ (i : Nat) (h : i < sps.length), (sps[i] = .inp ↔ FirstLs st.cur.params.tail i)) ∧ ∀ p ∈ sps, p ≠ .sh .nt

/-- node ↔ ParSpec type -/
def TyRel (v : RN) : Ty → Prop
  | .s s => v.sh = some s ∧ (v.isInp = true → ∃ l r, s = .p l r) ∧ v.tag ≠ 1
  | .lit => v.sh = some .uw ∧ v.isInp = false
  | .inp => v.isInp = true ∧ v.sh = some .ls
  | .bot => v.pend = true

theorem Sh.width_pos (s : Sh) : 0 < s.width := by
  cases s <;> simp [Sh.width]
  rename_i a b; have := Sh.width_pos a; omega

theorem atomLeaf_spec {st st1 : St} {cx : Cx} (hc : CxRel st cx) (h : AtomLeaf st st1) (tl : Bool) (nx : Nat) :
    ∃ v ty r, st1 = { st with toks := r, vals := v :: st.vals, arena := st.arena ++ [v] } ∧ TyRel v ty ∧ v.pend = false ∧
      ∀ f, pAtom (f + 1) cx tl st.toks nx = some (v.toNd, ty, r, nx) := by
  cases h with
  | num ht =>
    refine ⟨_, .lit, _, rfl, ⟨rfl, rfl⟩, rfl, fun f => ?_⟩
    rw [ht]; simp [pAtom, RN.toNd]
  | nil ht =>
    refine ⟨_, .s .ls, _, rfl, ⟨rfl, by simp [RN.isInp, RN.tag], by decide⟩, rfl, fun f => ?_⟩
    rw [ht]; simp [pAtom, RN.toNd, RN.toNdL]
  | bnew ht =>
    refine ⟨_, .s .bf, _, rfl, ⟨rfl, by simp [RN.isInp, RN.tag], by decide⟩, rfl, fun f => ?_⟩
    rw [ht]; simp [pAtom, RN.toNd, RN.toNdL]
  | @loc x r bd _ ht hb hl =>
    unfold locOf at hl
    split at hl
    · simp at hl
    · rename_i hnt
      simp only [Option.some.injEq] at hl
      subst hl
      have henv := hc.env x
      rw [hb] at henv
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hc.typed x bd hb)
      by_cases hi : bd.inp = true
      · have hls := hc.inp x bd hb hi
        simp only [Option.bind_some, bdPs, hi, if_true, Option.map_some] at henv
        refine ⟨_, .inp, r, rfl, ⟨by simp [RN.isInp, RN.tag, RN.b, hi], hls⟩, rfl, fun f => ?_⟩
        rw [ht]; simp [pAtom, henv, RN.toNd, hi]
      · have hi' : bd.inp = false := by simpa using hi
        have hps : bdPs bd = some (.sh s) := by
          unfold bdPs; rw [hs] at hnt ⊢; simp only [hi', Bool.false_eq_true, if_false]
          cases s <;> first | rfl | exact absurd rfl hnt
        simp only [Option.bind_some, hps, Option.map_some] at henv
        have hw := Sh.width_pos s
        have hpi : (RN.mk 2 bd.slot (if bd.inp = true then 0 else cw bd.sh) bd.sh false []).isInp = true → ∃ l r, s = .p l r := by
          intro h1; cases s <;> simp_all [RN.isInp, RN.tag, RN.b, cw, Sh.width]
        refine ⟨_, .s s, r, rfl, ⟨hs, hpi, by simp [RN.tag]⟩, rfl, fun f => ?_⟩
        rw [ht]; simp [pAtom, henv, RN.toNd, hi', hs, cw]
  | @cst x r j d _ ht hb hd hj hp hm =>
    obtain ⟨_, rfl⟩ := mkNode_inv hm
    have henv := hc.env x
    rw [hb] at henv
    have hdf := hc.defs x
    rw [hd] at hdf
    obtain ⟨⟨j', di⟩, hfd, hj'⟩ := Option.map_eq_some_iff.mp hdf
    simp only at hj'; subst hj'
    obtain ⟨d', hd', hpar, hres, _, _⟩ := hc.row x _ di hfd
    rw [hj] at hd'; cases hd'
    have hemp : di.params = [] := by
      have : (di.params.map psCode).length = 0 := by rw [hpar]; exact hp
      simpa using this
    refine ⟨_, .s di.res, r, rfl, ⟨hres, by simp [RN.isInp, RN.tag], by simp [RN.tag]⟩, rfl, fun f => ?_⟩
    rw [ht]; simp [pAtom, henv, hfd, hemp, RN.toNd, RN.toNdL]

end ParRun
