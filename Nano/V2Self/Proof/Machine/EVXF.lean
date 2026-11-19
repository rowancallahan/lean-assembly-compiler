/- Machine bridge (Opus box E): the remaining closing fragments under the heap contract (HeapEV's Fin1/Fin2):
BIN (`binT op`, all 8 ops) and RD (`rdT`, input bytes kept by `Inv`). -/
import Nano.V2Self.Proof.Machine.EVXL
namespace Templates
open CallProbe

def aluF2 (op : Nat) : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) := fun a b _ H => some (aluf op a b, H)

theorem fin2_alu {C : List J} {q op : Nat} {Inv : St → Prop} {hb : Nat} (hC : At C q (binT op)) :
    Fin2 C q 5 Inv hb (aluF2 op) := by
  intro s2 H2 v H3 I2 z2 hR hl hF
  simp only [aluF2, Option.some.injEq, Prod.mk.injEq] at hF
  obtain ⟨rfl, rfl⟩ := hF
  have hr := bin_run s2 hC hl
  have t8 : (UInt64.ofNat ((s2.x 31).toNat + 8)).toNat = (s2.x 31).toNat + 8 := by
    simp only [UInt64.toNat_ofNat']; omega
  have t8' : (s2.x 31 + 8).toNat = (s2.x 31).toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨_, run_star hr, ?_, ?_, ?_, ?_, ?_⟩
  · simp [upd, t8']
  · simp [upd_same]
  · refine HRel_stack hR (by simp [upd_ne]) (by simp [upd, t8']; have := hR.2.2.1; omega) ?_
    intro a h1 h2; simp only []; rw [upd_other _ _ (by have := hR.2.2.1; omega)]
  · intro r h5 h6 _ _ _ h31; simp [upd_ne, h5, h6, h31]
  · intro a ha _; simp only []; rw [upd_other _ _ ha]

def rdF1 (c29 : UInt64) (inp : Nat → UInt64) : UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun i _ H => some (if i.toNat < c29.toNat then inp i.toNat else 0, H)

/-- the input facts the invariant carries: base t3 = c28, length t4 = c29, bytes `inp` -/
def InpOK (Inv : St → Prop) (c28 c29 : UInt64) (inp : Nat → UInt64) : Prop :=
  ∀ s, Inv s → s.x 28 = c28 ∧ s.x 29 = c29 ∧ (∀ i, i < c29.toNat → lbm s.m (c28.toNat + i) = inp i) ∧
    c28.toNat + c29.toNat < 2 ^ 63

theorem fin1_rd {C : List J} {q : Nat} {Inv : St → Prop} {hb : Nat} {c28 c29 : UInt64} {inp : Nat → UInt64}
    (hC : At C q rdT) (hInv : InpOK Inv c28 c29 inp) : Fin1 C q 6 Inv hb (rdF1 c29 inp) := by
  intro s1 H1 v H2 I1 z1 hR hF
  simp only [rdF1, Option.some.injEq, Prod.mk.injEq] at hF
  obtain ⟨rfl, rfl⟩ := hF
  obtain ⟨h28, h29, hin, hb'⟩ := hInv s1 I1
  obtain ⟨k, hk⟩ := rd_run s1 hC z1 (by rw [h28, h29]; exact hb')
  have ev : (if (s1.m (s1.x 31).toNat).toNat < (s1.x 29).toNat then
      lbm s1.m ((s1.x 28).toNat + (s1.m (s1.x 31).toNat).toNat) else 0) =
      (if (s1.m (s1.x 31).toNat).toNat < c29.toNat then inp (s1.m (s1.x 31).toNat).toNat else 0) := by
    rw [h29, h28]
    by_cases hi : (s1.m (s1.x 31).toNat).toNat < c29.toNat
    · simp only [hi, if_true]; rw [hin _ hi]
    · simp only [hi, if_false]
  rw [ev] at hk
  refine ⟨_, run_star hk, ?_, ?_, ?_, ?_, ?_⟩
  · simp [upd_ne]
  · simp [upd_same]
  · refine HRel_stack hR (by simp [upd_ne]) (by simp [upd_ne]; exact hR.2.2.1) ?_
    intro a h1 h2; simp only []; rw [upd_other _ _ (by have := hR.2.2.1; omega)]
  · intro r h5 h6 _ _ _; simp [upd_ne, h5, h6]
  · intro a ha _; simp only []; rw [upd_other _ _ ha]

end Templates
