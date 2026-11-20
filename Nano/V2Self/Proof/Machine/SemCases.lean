/- The semantic case split the machine theorems need (`SemCases`: ok / cap / out of room below a bound, for a work block
and every code-position table).
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

end SimW
