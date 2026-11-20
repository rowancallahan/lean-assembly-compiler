/- Normal jal offsets: `norm` replaces a jal offset `o` by `jw o`, its value modulo 2^19 in [−2^18, 2^18).  Gen's words
do not change (`encG_norm`: the J-type immediate keeps 21 bits of `4·o`), and safe runs do not change (`SafeX` bounds
every executed jal by ±2^18, where `norm` is the identity: `sstarX_norm`).  So Gen's program may be taken with every
instruction `JOK` (GoodX, jal offsets in ±2^18), what a byte translator such as rv2arm needs to read it back. -/
import Nano.V2Self.Proof.Machine.ArmRA
namespace SimW
open CallProbe

/-- an offset modulo 2^19, in [−2^18, 2^18) -/
def jw (o : Int) : Int := (o + 2 ^ 18) % 2 ^ 19 - 2 ^ 18

/-- the jal offset normalised (every other instruction unchanged) -/
def norm : J → J
  | .jal rd o => .jal rd (jw o)
  | j => j

/-- Gen's instructions in normal form: `GoodX`, jal offsets in [−2^18, 2^18) -/
def JOK (j : J) : Prop := GoodX j ∧ ∀ rd o, j = .jal rd o → -2 ^ 18 ≤ o ∧ o < 2 ^ 18

theorem jw_id {o : Int} (h1 : -2 ^ 18 ≤ o) (h2 : o < 2 ^ 18) : jw o = o := by unfold jw; omega

theorem encG_norm (j : J) : encG (norm j) = encG j := by
  cases j with
  | jal rd o =>
    simp only [norm, encG]
    have e : ((4 * jw o) % 2 ^ 64).toNat % 2 ^ 21 = ((4 * o) % 2 ^ 64).toNat % 2 ^ 21 := by unfold jw; omega
    unfold C.g5
    have h1 : (iu (4 * jw o) >>> 20) &&& C.g_1 = (iu (4 * o) >>> 20) &&& C.g_1 := ArmRA.u64 (by
      simp only [show C.g_1 = 1 from rfl]; wnorm; rw [CallProbe.iu_toNat, CallProbe.iu_toNat]; omega)
    have h2 : (iu (4 * jw o) >>> 1) &&& C.g_1023 = (iu (4 * o) >>> 1) &&& C.g_1023 := ArmRA.u64 (by
      simp only [show C.g_1023 = 1023 from rfl]; wnorm; rw [CallProbe.iu_toNat, CallProbe.iu_toNat]; omega)
    have h3 : (iu (4 * jw o) >>> 11) &&& C.g_1 = (iu (4 * o) >>> 11) &&& C.g_1 := ArmRA.u64 (by
      simp only [show C.g_1 = 1 from rfl]; wnorm; rw [CallProbe.iu_toNat, CallProbe.iu_toNat]; omega)
    have h4 : (iu (4 * jw o) >>> 12) &&& C.g_255 = (iu (4 * o) >>> 12) &&& C.g_255 := ArmRA.u64 (by
      simp only [show C.g_255 = 255 from rfl]; wnorm; rw [CallProbe.iu_toNat, CallProbe.iu_toNat]; omega)
    rw [h1, h2, h3, h4]
  | _ => rfl

theorem jok_norm (j : J) (h : GoodX j) : JOK (norm j) := by
  cases j with
  | jal rd o => exact ⟨h, fun rd' o' e => by cases e; unfold jw; omega⟩
  | _ => exact ⟨h, fun _ _ e => by cases e⟩

theorem norm_id {j : J} (h : ∀ rd o, j = .jal rd o → -2 ^ 18 ≤ o ∧ o < 2 ^ 18) : norm j = j := by
  cases j with
  | jal rd o => obtain ⟨h1, h2⟩ := h rd o rfl; simp only [norm, jw_id h1 h2]
  | _ => rfl

theorem getN {K : LayW} {C : List J} {pc : Nat} {s : St} (h : SafeX K C (pc, s)) : (C.map norm)[pc]? = C[pc]? := by
  rw [List.getElem?_map]
  simp only [SafeX] at h
  cases hc : C[pc]? with
  | none => rfl
  | some j =>
    rw [hc] at h
    simp only [Option.map_some]; congr 1
    cases j with
    | jal rd o => obtain ⟨-, h1, h2, -⟩ := h; simp only [norm, jw_id h1 h2]
    | _ => rfl

theorem safeX_norm {K : LayW} {C : List J} {a : Nat × St} (h : SafeX K C a) :
    SafeX K (C.map norm) a ∧ step (C.map norm) a = step C a := by
  obtain ⟨pc, s⟩ := a
  have e := getN h
  refine ⟨?_, ?_⟩
  · simp only [SafeX] at h ⊢; rw [e, List.length_map]; exact h
  · simp only [step]; rw [e]

theorem sstarX_norm {K : LayW} {C : List J} {a b : Nat × St} (h : SStarX K C a b) : SStarX K (C.map norm) a b := by
  induction h with
  | refl a => exact .refl a
  | head hS hs _ ih =>
    obtain ⟨h1, h2⟩ := safeX_norm hS
    exact .head h1 (by rw [h2]; exact hs) ih

theorem at_norm {C : List J} {i : Nat} {L : List J} (h : At C i L) (hL : ∀ j ∈ L, norm j = j) :
    At (C.map norm) i L := by
  intro k hk
  rw [List.getElem?_map, h k hk, List.getElem?_eq_getElem hk]
  simp only [Option.map_some]; rw [hL _ (List.getElem_mem hk)]

end SimW
