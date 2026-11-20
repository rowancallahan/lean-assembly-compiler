/- Opus box E: **`GenStage` from D's semantic bridge** (`gen_stage`): `SemCases` holds for parsed linear programs
(`gen_HD`, from D's `gen_R` above the work bound and `gen_all` below it), so `gen_implements` gives `ImplementsC`.
O's `DB` bound stays an explicit hypothesis `HDB`. -/
import Nano.V2Self.Proof.Machine.GenImpl
import Nano.V2Self.Proof.Bridge.MainConvG
namespace SimW
open Proven Nano.V2B Templates CallProbe C GenRef ParSpec

/-- **`GenStage`**, given O's field bound `DB` for the programs Gen accepts -/
theorem gen_stage (HDB : ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p →
    ts.length < 2 ^ 24 → NanoMain.LinearK p → g41 c (serialize p) ≠ [] → ∀ d ∈ p, DB d) : NanoMain.GenStage := by
  intro c ts p hp hts hL h
  obtain ⟨R, hR⟩ := gen_HD hp hL
  obtain ⟨Ks, hO, hK2⟩ := hL
  exact ⟨_, gen_implements c hp Ks hO hK2 (ParSerLen.ser_lt hp hts) h (HDB c ts p hp hts ⟨Ks, hO, hK2⟩ h) R hR⟩

end SimW
