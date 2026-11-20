/- `gen_main` for Gen's program with its jal offsets normalised (`SimW.norm`): the same words, the same safe runs, and
every instruction `JOK` (what a byte translator such as rv2arm needs). -/
import Nano.V2Self.Proof.Machine.GenMain
import Nano.V2Self.Proof.Machine.JNorm
namespace Templates
open CallProbe C GenRef ParSpec

/-- the start code's first words (its size check), the same for every main address -/
def startPre : List J :=
  [.addi 30 12 16, .srli 31 2 3, .slli 31 31 3, .bgeu 31 30 4, .addi 10 0 (-1), .addi 11 0 0, .jalr 0 1]

theorem at_pre {C : List J} {S w : Nat} (h : At C S (startJ S w)) : At C S startPre := by
  intro i hi
  have := h i (by simp [startJ]; simp [startPre] at hi; omega)
  rw [this]; simp [startPre] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem gen_mainN (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (s0 : St) (x : List UInt8) (hx11 : s0.x 11 = UInt64.ofNat x.length) (hxl : x.length < 2 ^ 64)
    (hxm : ∀ i, i < x.length → lbm s0.m ((s0.x 10).toNat + i) = (x.getD i 0).toUInt64) :
    ∃ (C : List J) (pr S : Nat) (T : Buf),
      let P := pcOf 524288 ((s0.x 12).toNat + 16) (s0.x 11) (NanoMain.inpW x) T
      g41 c (serialize p) = g40 16777216 c (C.map encG) 0 [] ∧ C.length < 2 ^ 18 ∧ At C 0 (stubJ S) ∧
      At C S startPre ∧ S + 32 ≤ C.length ∧ (∀ j ∈ C, SimW.JOK j) ∧
      ∀ (KL : SimW.LayW) E0, ((s0.x 2 >>> 3) <<< 3).toNat = E0 → s0.x 0 = 0 → (s0.x 12).toNat % 8 = 0 →
        2048 ≤ (s0.x 12).toNat →
        (s0.x 12).toNat + 16 ≤ E0 → E0 < 2 ^ 62 → s0.b + s0.w * C.length < 2 ^ 64 →
        (s0.x 10).toNat + (s0.x 11).toNat < 2 ^ 63 →
        ((s0.x 10).toNat + (s0.x 11).toNat ≤ (s0.x 12).toNat ∨ E0 ≤ (s0.x 10).toNat) →
        KL.lo ≤ (s0.x 12).toNat → E0 ≤ KL.hi → s0.b = KL.base →
        (∀ i, i < (s0.x 11).toNat → SimW.bok KL ((s0.x 10).toNat + i)) →
        (∀ vs H', semAt P p (p.length - 1) [] E0 ⟨(s0.x 12).toNat + 16, fun _ => none⟩ = some (vs, H') →
        ∃ y, NanoMain.Sem NanoMain.κC p x = .ok y ∧
          ((s0.x 13).toNat + y.length < 2 ^ 64 →
           ((s0.x 13).toNat + y.length ≤ (s0.x 12).toNat ∨ E0 ≤ (s0.x 13).toNat) →
           (∀ i, i < y.length → SimW.sok KL ((s0.x 13).toNat + i)) →
           ∃ s3, SimW.SStarX KL C (0, s0) (pr, s3) ∧ C[pr]? = some (.jalr 0 1) ∧ (∀ j, keepR j = true → s3.x j = s0.x j) ∧ s3.b = s0.b ∧ s3.x 1 = s0.x 1 ∧
             s3.x 8 = s0.x 8 ∧ s3.x 10 = (if y = [] then 1 else 0) ∧ s3.x 11 = UInt64.ofNat y.length ∧
             (∀ i, i < y.length → lbm s3.m ((s0.x 13).toNat + i) = (y.getD i 0).toUInt64))) ∧
        (∀ fk, fk ≠ .stuck → semAtF P p (p.length - 1) [] E0 ⟨(s0.x 12).toNat + 16, fun _ => none⟩ = .error fk →
         ∃ s2, SimW.SStarX KL C (0, s0) (stubW fk, s2) ∧ s2.m (s0.x 12).toNat = s0.x 1 ∧
           s2.m ((s0.x 12).toNat + 8) = s0.x 8 ∧ s2.x 0 = 0 ∧ (∀ j, keepR j = true → s2.x j = s0.x j) ∧ s2.b = s0.b) := by
  obtain ⟨C, pr, S, T, hg, hc18, hst, hss, h32, hgl, hrun⟩ := gen_main c hP Ks hO hK2 hXl h hdb s0 x hx11 hxl hxm
  have hmap : (C.map SimW.norm).map encG = C.map encG := by
    rw [List.map_map]; apply List.map_congr_left; intro j _; exact SimW.encG_norm j
  have hlen : (C.map SimW.norm).length = C.length := List.length_map _
  refine ⟨C.map SimW.norm, pr, S, T, by rw [hmap]; exact hg, by rw [hlen]; exact hc18, ?_, ?_, by rw [hlen]; exact h32, ?_, ?_⟩
  · refine SimW.at_norm hst (fun j hj => ?_)
    simp only [stubJ, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact SimW.norm_id (fun rd o e => by cases e; omega)
    all_goals rfl
  · obtain ⟨w, hw⟩ := hss
    refine SimW.at_norm (at_pre hw) (fun j hj => ?_)
    simp only [startPre, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro j hj
    obtain ⟨j0, hj0, rfl⟩ := List.mem_map.1 hj
    exact SimW.jok_norm j0 (hgl j0 hj0)
  · intro KL E0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    rw [hlen] at a7
    obtain ⟨r1, r2⟩ := hrun KL E0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
    refine ⟨fun vs H' hS => ?_, fun fk hk hS => ?_⟩
    · obtain ⟨y, hy, hY⟩ := r1 vs H' hS
      refine ⟨y, hy, fun b1 b2 b3 => ?_⟩
      obtain ⟨s3, h3, h4, rest⟩ := hY b1 b2 b3
      exact ⟨s3, SimW.sstarX_norm h3, by rw [List.getElem?_map, h4]; rfl, rest⟩
    · obtain ⟨s2, h2, rest⟩ := r2 fk hk hS
      exact ⟨s2, SimW.sstarX_norm h2, rest⟩

end Templates
