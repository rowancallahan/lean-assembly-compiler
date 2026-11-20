/- Opus box E: Gen's field bounds `DB` for parsed programs, given the width cap (nslots, nres < 2^32; O's parsed_bnd).
`dbStage`: `DBStage` from that cap. -/
import Nano.V2Self.Proof.Parser.DBPar
namespace Templates
open ParSpec NanoMain

theorem len_flatMap_mem {d : DefA} : ∀ {p : List DefA}, d ∈ p → d.ser.length ≤ (p.flatMap DefA.ser).length
  | _ :: _, .head _ => by simp
  | _ :: _, .tail _ h => by have := len_flatMap_mem h; simp only [List.flatMap_cons, List.length_append]; omega

theorem len_le_flatMap : ∀ p : List DefA, p.length ≤ (p.flatMap DefA.ser).length
  | [] => by simp
  | d :: p => by have := len_le_flatMap p; simp only [List.flatMap_cons, List.length_append, List.length_cons, DefA.ser]; omega

theorem nb_tyB {D : List Sig} {Γ : List (Option Kd)} {b : Nd} {ks : List Kd} (np : Nat) (h : TyB D Γ b ks)
    (hΓ : Γ.length < 2 ^ 32) (hD : D.length < 2 ^ 32) (hs : b.ser.length < 2 ^ 32) (hp : PAr b)
    (hloop : ∀ z s, b = .loop z s → 1 ≤ np) : NB np b := by
  cases h with
  | plain h => exact nb_ty np h hΓ hD (by simp) hs hp
  | loop _ hz hs' =>
    simp only [Nd.ser, List.length_cons, List.length_append] at hs; simp only [PAr] at hp
    exact ⟨nb_ty np hz hΓ hD (by simp) (by omega) hp.1, nb_ty np hs' hΓ hD (fun _ => hloop _ _ rfl) (by omega) hp.2⟩

theorem parsed_DB {ts : List UInt64} {p : List DefA} (hp : ParsesProgram ts p) (hts : ts.length < 2 ^ 24)
    (hcap : ∀ d ∈ p, d.nslots < 2 ^ 32 ∧ d.nres < 2 ^ 32) : ∀ d ∈ p, DB d := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have hser := ParSerLen.ser_lt hp hts
  have hpl := len_le_flatMap p
  have hdl := len_flatMap_mem hd
  simp only [serialize, List.length_cons] at hser
  obtain ⟨hpa, hk, hid⟩ := parsed_par hp i _ (List.getElem?_eq_getElem hi)
  obtain ⟨sigs, hsl, hty, -⟩ := refParse_ty hp
  obtain ⟨sg, hsg⟩ : ∃ sg, sigs[i]? = some sg := ⟨sigs[i]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨h1, h2, h3, h4⟩ := hty i _ sg (List.getElem?_eq_getElem hi) hsg
  obtain ⟨c1, c2⟩ := hcap _ hd
  simp only [DefA.ser, List.length_append, List.length_cons, List.length_nil] at hdl
  refine ⟨by omega, by omega, c1, by omega, c2, ?_⟩
  refine nb_tyB _ h4 (by simp; omega) (by simp; omega) (by omega) hpa ?_
  intro z s hb
  rw [hb] at h4
  cases h4 with
  | plain h => cases h
  | loop hΓ _ _ =>
    rcases hl : sg.1 with _ | ⟨k, l⟩
    · rw [hl] at hΓ
      have : (List.replicate (p[i].nslots - p[i].npw) (none : Option Kd))[0]? = some (some Kd.w) := by
        simp only [List.map_nil, List.nil_append] at hΓ; rw [hΓ]; rfl
      simp [List.getElem?_replicate] at this
    · rw [h1, hl]; simp
end Templates

namespace NanoMain
open Proven.Top Proven.Top.Alloc

/-- the width cap of O's `parsed_bnd`, the part `DB` needs -/
def CapStage : Prop := ∀ (ts : List UInt64) (p : List ParSpec.DefA), ParSpec.ParsesProgram ts p → ts.length < 2 ^ 24 →
  ∀ d ∈ p, d.nslots < 2 ^ 32 ∧ d.nres < 2 ^ 32

theorem dbStage (HC : CapStage) : DBStage := fun _ ts p hp hts _ _ => Templates.parsed_DB hp hts (HC ts p hp hts)

end NanoMain
