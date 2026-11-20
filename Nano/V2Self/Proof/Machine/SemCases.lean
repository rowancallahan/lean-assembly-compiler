/- The semantic case split the machine theorems need (`SemCases`: ok / cap / out of room below a bound, for a work block
and every code-position table) and its proof for parsed linear programs (`gen_HD`, from D's `gen_R` / `gen_all`).
Machine-independent (split out of GenImpl / GenStageE). -/
import Nano.V2Self.Proof.Bridge.MainConvG
import Nano.V2Self.Proof.Bridge.MainConvX7
import Nano.V2Self.Proof.Bridge.MainConv8
import Nano.V2Self.Proof.Bridge.SemX
import Nano.V2Self.Proof.Machine.NdTop
namespace SimW
open Templates CallProbe C GenRef ParSpec

/-- the semantic case split the machine theorem needs, for input `x`, work block `[wb, wb + wl)` (8-aligned base, at
least 16 usable bytes) and every code-position table `T` -/
def SemCases (p : List DefA) (R : List UInt8 → Nat) (x : List UInt8) (wb wl : Nat) : Prop :=
  (∃ y, NanoMain.Sem NanoMain.κC p x = .ok y ∧ ∀ T, ∃ vs H', semAt (pcOf 524288 (wb + 16) (UInt64.ofNat x.length)
      (NanoMain.inpW x) T) p (p.length - 1) [] ((wb + wl) / 8 * 8) ⟨wb + 16, fun _ => none⟩ = some (vs, H')) ∨
  (NanoMain.Sem NanoMain.κC p x = .error .cap ∧ ∀ T, semAtF (pcOf 524288 (wb + 16) (UInt64.ofNat x.length)
      (NanoMain.inpW x) T) p (p.length - 1) [] ((wb + wl) / 8 * 8) ⟨wb + 16, fun _ => none⟩ = .error .cap) ∨
  ((∀ T, semAtF (pcOf 524288 (wb + 16) (UInt64.ofNat x.length) (NanoMain.inpW x) T) p (p.length - 1) []
      ((wb + wl) / 8 * 8) ⟨wb + 16, fun _ => none⟩ = .error .room) ∧ wl < R x)

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

end SimW
