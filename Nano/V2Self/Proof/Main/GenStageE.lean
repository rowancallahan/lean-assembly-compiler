/- Opus box E: **`GenStage` from D's semantic bridge** (`gen_stage`): `SemCases` holds for parsed linear programs
(`gen_HD`, from D's `gen_R` above the work bound and `gen_all` below it), so `gen_implements` gives `ImplementsC`.
O's `DB` bound stays an explicit hypothesis `HDB`. -/
import Nano.V2Self.Proof.Machine.GenImpl
import Nano.V2Self.Proof.Bridge.MainConvG
namespace SimW
open Proven Nano.V2B Templates CallProbe C GenRef ParSpec

theorem semAtF_pcT (κ hb : Nat) (c : UInt64) (i : Nat → UInt64) (T T' : Buf) (p : List DefA) (k : Nat) :
    semAtF (pcOf κ hb c i T) p k = semAtF (pcOf κ hb c i T') p k :=
  NanoMain.semAtF_T (pcOf κ hb c i T') _ p k

theorem semAt_pcT (κ hb : Nat) (c : UInt64) (i : Nat → UInt64) (T T' : Buf) (p : List DefA) (k : Nat) :
    semAt (pcOf κ hb c i T) p k = semAt (pcOf κ hb c i T') p k :=
  NanoMain.semAt_T (pcOf κ hb c i T') _ p k

theorem sem3 (r : Except NanoMain.Stop (List UInt8)) :
    (∃ y, r = .ok y) ∨ r = .error .cap ∨ r = .error .stuck := by
  rcases r with f | y
  · cases f
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exact Or.inl ⟨y, rfl⟩

theorem gen_HD {ts : List UInt64} {p : List DefA} (hp : ParsesProgram ts p) (hL : NanoMain.LinearK p) :
    ∃ R : List UInt8 → Nat, ∀ x, x.length ≤ 2 ^ 20 → ∀ wb wl, wb % 8 = 0 → 2 ^ 31 ≤ wb → wb + wl ≤ 2 ^ 32 →
      wb + 16 ≤ (wb + wl) / 8 * 8 → SemCases p R x wb wl := by
  refine ⟨fun x => if hx : x.length ≤ 2 ^ 20 then Classical.choose (NanoMain.gen_R hp hL x hx) else 0, ?_⟩
  intro x hx wb wl hw8 _ hwl _
  have hR := Classical.choose_spec (NanoMain.gen_R hp hL x hx)
  unfold SemCases; simp only [hx, dite_true]
  by_cases hle : Classical.choose (NanoMain.gen_R hp hL x hx) ≤ wl
  · rcases sem3 (NanoMain.Sem NanoMain.κC p x) with ⟨y, hS⟩ | hS | hS
    · refine Or.inl ⟨y, hS, fun T => ?_⟩
      obtain ⟨a, l, H', e, -⟩ := (hR T wb wl hw8 hwl hle).1 y hS
      exact ⟨_, _, e⟩
    · exact Or.inr (Or.inl ⟨hS, fun T => (hR T wb wl hw8 hwl hle).2 hS⟩)
    · exact absurd hS (NanoMain.parsed_not_stuck hp _ x)
  · have hlt : wl < Classical.choose (NanoMain.gen_R hp hL x hx) := by omega
    obtain h | h | ⟨h, hS⟩ := NanoMain.gen_all hp hL x hx [] (wb + 16) ((wb + wl) / 8 * 8) ⟨wb + 16, fun _ => none⟩
      (by show (wb + 16) % 8 = 0; omega) (Nat.le_refl _)
    · obtain ⟨a, l, H', e, -, hS⟩ := h
      refine Or.inl ⟨_, hS, fun T => ⟨[a], H', ?_⟩⟩
      rw [semAt_pcT _ _ _ _ T [], ← oD_semAt]
      show toO (semAtF _ p _ [] _ _) = _
      rw [show (524288 : Nat) = NanoMain.κC from rfl, e]; rfl
    · exact Or.inr (Or.inr ⟨fun T => by rw [semAtF_pcT _ _ _ _ T []]; exact h, hlt⟩)
    · exact Or.inr (Or.inl ⟨hS, fun T => by rw [semAtF_pcT _ _ _ _ T []]; exact h⟩)

/-- **`GenStage`**, given O's field bound `DB` for the programs Gen accepts -/
theorem gen_stage (HDB : ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p →
    ts.length < 2 ^ 24 → NanoMain.LinearK p → g41 c (serialize p) ≠ [] → ∀ d ∈ p, DB d) : NanoMain.GenStage := by
  intro c ts p hp hts hL h
  obtain ⟨R, hR⟩ := gen_HD hp hL
  obtain ⟨Ks, hO, hK2⟩ := hL
  exact ⟨_, gen_implements c hp Ks hO hK2 (ParSerLen.ser_lt hp hts) h (HDB c ts p hp hts ⟨Ks, hO, hK2⟩ h) R hR⟩

end SimW
