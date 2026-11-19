/- Box O: the parser's WIDTH CAP gives every parsed def `nslots < 2^20` and `nres < 2^20`.  This proves `BndStage` and
`CapStage`, so `C_correctLC` loses both premises (`C_correctL`). -/
import Nano.V2Self.Proof.DBStageE
namespace Templates
open ParSpec NanoMain

theorem pDef_cap (fuel : Nat) (defs : List DefI) (ts : List Tok) (di : DefI) (da : DefA) (r : List Tok)
    (h : pDef fuel defs ts = some (di, da, r)) : da.nslots < 2 ^ 20 ∧ da.nres < 2 ^ 20 := by
  unfold pDef at h
  split at h
  · split at h
    · cases h
    · split at h
      · obtain ⟨⟨tys, r1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
        simp only at h
        split at h
        · split at h
          · cases h
          · split at h
            · obtain ⟨⟨zn, r3⟩, hz, h⟩ := Option.bind_eq_some_iff.1 h
              simp only at h
              split at h
              · cases h
              · obtain ⟨envZ, hZ, h⟩ := Option.bind_eq_some_iff.1 h
                obtain ⟨⟨z, tz, r4, nx1⟩, hpz, h⟩ := Option.bind_eq_some_iff.1 h
                simp only at h
                split at h
                · cases h
                · split at h
                  · obtain ⟨⟨sn, r6⟩, hs, h⟩ := Option.bind_eq_some_iff.1 h
                    simp only at h
                    split at h
                    · cases h
                    · obtain ⟨envS, hS, h⟩ := Option.bind_eq_some_iff.1 h
                      obtain ⟨⟨sb, ts', r7, nx2⟩, hps, h⟩ := Option.bind_eq_some_iff.1 h
                      simp only at h
                      split at h
                      · split at h
                        · cases h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        simp only [not_or, Nat.not_le] at *; omega
                      · cases h
                  · cases h
            · cases h
        · cases h
      · obtain ⟨⟨groups, r1⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
        simp only at h
        split at h
        · obtain ⟨⟨resT, r3⟩, ht, h⟩ := Option.bind_eq_some_iff.1 h
          simp only at h
          split at h
          · split at h
            · cases h
            · obtain ⟨⟨b, tb, r5, nx⟩, hpe, h⟩ := Option.bind_eq_some_iff.1 h
              simp only at h
              split at h
              · cases h
              · split at h
                · cases h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                simp only [not_or, Nat.not_le] at *; omega
          · cases h
        · cases h
  · cases h

theorem pDefs_cap (fuel : Nat) : ∀ (f : Nat) (defs : List DefI) (ts : List Tok) (ds : List DefI) (as : List DefA),
    pDefs fuel f defs ts = some (ds, as) → ∀ d ∈ as, d.nslots < 2 ^ 20 ∧ d.nres < 2 ^ 20
  | 0, _, _, _, _, h => by simp [pDefs] at h
  | f + 1, defs, [], ds, as, h => by
    simp [pDefs] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | f + 1, defs, t :: ts, ds, as, h => by
    simp only [pDefs] at h
    obtain ⟨⟨di, da, r⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨ds', as'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    intro d hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact pDef_cap fuel defs _ di _ r hd
    · exact pDefs_cap fuel f (defs ++ [di]) r ds' as' hr d hm

theorem parsed_cap {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) :
    ∀ d ∈ p, d.nslots < 2 ^ 20 ∧ d.nres < 2 ^ 20 := by
  unfold ParsesProgram refParse at h
  obtain ⟨toks, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨ds, as⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
  simp only at h
  split at h
  · split at h
    · cases h
      exact pDefs_cap _ _ _ _ _ _ hd
    · cases h
  · cases h

/-- the bounds agreed with D: O's `OwnWF.Bnd` and Gen's `DB` for every parsed program -/
theorem parsed_bnd {ts : List UInt64} {p : List DefA} (hp : ParsesProgram ts p) (hts : ts.length < 2 ^ 24) :
    OwnWF.Bnd p ∧ ∀ d ∈ p, DB d := by
  have hser := ParSerLen.ser_lt hp hts
  have hpl := len_le_flatMap p
  simp only [serialize, List.length_cons] at hser
  have hc := parsed_cap hp
  refine ⟨⟨by omega, fun d hd => ⟨(hc d hd).1, by have := (hc d hd).2; omega⟩⟩, parsed_DB hp hts fun d hd => ?_⟩
  have := hc d hd; omega

end Templates

open LeanRV64D
namespace NanoMain
open Proven.Top Proven.Top.Alloc

theorem capStage : CapStage := fun _ _ hp _ d hd => by
  have := Templates.parsed_cap hp d hd; omega

theorem bndStage : BndStage := fun _ _ _ hp hts _ => (Templates.parsed_bnd hp hts).1

/-- **C is correct**: `C_correctLC` with both of its premises proved -/
theorem C_correctLO : CompileCorrectL riscv compileC := C_correctLC bndStage capStage

end NanoMain

#print axioms NanoMain.C_correctLO
