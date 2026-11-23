/- Bridge.Real.IndHeads: `IndStored env indHeads` (List, List.nil, List.cons, UInt8, UInt64 stored as declared)
FROM ACCEPTANCE, given a decidable check that the stream holds those three one-member blocks (`indOkBlocks`). -/
import Bridge.Real.IndStored
import Bridge.Real.NanoDen

namespace Bridge.Real.IndHeads
open ConLeche Bridge.Real Bridge.Real.Engine Bridge.Real.NanoDen

universe w

def cvOf (p : Name × Head) : ConstantVal := ⟨p.1, p.2.ps, piV p.2.Ts p.2.B⟩

/-- the stream holds the List, UInt8 and UInt64 blocks with these declared members -/
def indOkBlocks (ds : Array Declaration) : Bool :=
  match indHeads with
  | [lst, nil, cons, u8, u64] =>
    Ind.blockHas ds (cvOf lst) [cvOf nil, cvOf cons] && Ind.blockHas ds (cvOf u8) [] && Ind.blockHas ds (cvOf u64) []
  | _ => false

theorem entry {env : Env} {p : Name × Head} (hh : headSc p.2 = true)
    (h : ∃ c, env.find? (cvOf p).name = some c ∧ c.toConstantVal.levelParams = (cvOf p).levelParams ∧
      AnnotOf (cvOf p).type c.toConstantVal.type) :
    ∃ ci, env.find? p.1 = some ci ∧ ci.toConstantVal.levelParams = p.2.ps ∧
      ∃ ms : List BinderMeta, ms.length = p.2.Ts.length ∧ ci.toConstantVal.type = piN (p.2.Ts.zip ms) p.2.B := by
  obtain ⟨c, hf, hl, ha⟩ := h
  have hT : ∀ T ∈ p.2.Ts, BF T := by
    intro T hT
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
    exact sc_BF (headSc_T hh i _ (List.getElem?_eq_getElem hi))
  obtain ⟨ms', hl', hty⟩ := Ind.annot_tele (by simp [nev]) hT (sc_BF (headSc_B hh)) ha
  exact ⟨c, hf, hl, ms', hl', hty⟩

/-- **`IndStored` from acceptance** -/
theorem indStored_of (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env) (h : indOkBlocks ds = true) :
    IndStored env indHeads := by
  simp only [indOkBlocks, indHeads, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have s1 := Ind.blockHas_stored V accepted h1
  have s2 := Ind.blockHas_stored V accepted h2
  have s3 := Ind.blockHas_stored V accepted h3
  intro p hp
  simp only [indHeads, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact entry (by decide) (s1 _ (by simp))
  · exact entry (by decide) (s1 _ (by simp))
  · exact entry (by decide) (s1 _ (by simp))
  · exact entry (by decide) (s2 _ (by simp))
  · exact entry (by decide) (s3 _ (by simp))

end Bridge.Real.IndHeads
