/- Nano/V2Self/Proof/MainConvG: the converse in E's GenStage vocabulary — for a parsed `LinearK` program and an input of
at most 2^20 bytes: one work bound `R` (uniform in the work base and in Gen's def table T) above which E's semantics
returns `Sem`'s outcome; and at every work size, the kinded outcome is ok (agreeing with `Sem`), room, or cap exactly
when `Sem` caps. -/
import Nano.V2Self.Proof.MainConvF7
import Nano.V2Self.Proof.NdTop

namespace NanoMain
open Templates

/-- **the work bound** -/
theorem gen_R {ts : List UInt64} {p : List ParSpec.DefA} (hp : ParSpec.ParsesProgram ts p) (hL : LinearK p) (x : List UInt8)
    (hx : x.length ≤ 2 ^ 20) :
    ∃ R, ∀ (T : Buf) (base len : Nat), base % 8 = 0 → base + len ≤ 2 ^ 32 → R ≤ len →
      (∀ y, Sem κC p x = .ok y → ∃ a l H', semAt (pcOf κC (base + 16) (UInt64.ofNat x.length) (inpW x) T) p (p.length - 1)
        [] ((base + len) / 8 * 8) ⟨base + 16, fun _ => none⟩ = some ([a], H') ∧
        BufAt (base + 16) κC H' a l ∧ y = l.map UInt64.toUInt8) ∧
      (Sem κC p x = .error .cap → semAtF (pcOf κC (base + 16) (UInt64.ofNat x.length) (inpW x) T) p (p.length - 1)
        [] ((base + len) / 8 * 8) ⟨base + 16, fun _ => none⟩ = .error .cap) := by
  obtain ⟨sigs, hTy⟩ := refParse_ty hp
  obtain ⟨Ks, hO, hK2⟩ := hL
  have hil : x.length < 2 ^ 64 := by omega
  have hκ : κC < 2 ^ 40 := by decide
  cases hS : Sem κC p x with
  | ok y =>
    obtain ⟨R, hR⟩ := main_room p sigs Ks x hTy hO hK2 hil κC hκ y hS
    refine ⟨R, fun T base len h8 h2 h3 => ⟨fun y' hy => ?_, fun h => (by cases h)⟩⟩
    cases hy
    exact hR (pcOf κC (base + 16) (UInt64.ofNat x.length) (inpW x) T) base len rfl rfl rfl rfl h8 h2 h3
  | error e =>
    cases e with
    | stuck => exact absurd hS (parsed_not_stuck hp κC x)
    | cap =>
      obtain ⟨R, hR⟩ := main_capR p sigs Ks x hTy hO hK2 hil κC hκ hS
      exact ⟨R, fun T base len h8 h2 h3 => ⟨fun y hy => (by cases hy),
        fun _ => hR (pcOf κC (base + 16) (UInt64.ofNat x.length) (inpW x) T) base len rfl rfl rfl rfl h8 h2 h3⟩⟩

/-- **every work size** -/
theorem gen_all {ts : List UInt64} {p : List ParSpec.DefA} (hp : ParSpec.ParsesProgram ts p) (hL : LinearK p) (x : List UInt8)
    (hx : x.length ≤ 2 ^ 20) (T : Buf) (hb sp : Nat) (H : Hp) (h8 : H.top % 8 = 0) (hhb : hb ≤ H.top) :
    let P := pcOf κC hb (UInt64.ofNat x.length) (inpW x) T
    (∃ a l H', semAtF P p (p.length - 1) [] sp H = .ok ([a], H') ∧ BufAt hb κC H' a l ∧
      Sem κC p x = .ok (l.map UInt64.toUInt8)) ∨
    semAtF P p (p.length - 1) [] sp H = .error .room ∨
    (semAtF P p (p.length - 1) [] sp H = .error .cap ∧ Sem κC p x = .error .cap) := by
  obtain ⟨sigs, hTy⟩ := refParse_ty hp
  obtain ⟨Ks, hO, hK2⟩ := hL
  exact main_all _ p sigs Ks x hTy hO hK2 rfl rfl (by omega) sp H h8 hhb

end NanoMain
