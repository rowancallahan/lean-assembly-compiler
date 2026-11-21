/- E4, layer L5 (FABLE-M4): the two passes of the nano translator on Gen's words `gw Cj = Cj.map encG`, from the
per-atom facts `StepOK` (JArmStep.lean) and `e35 = candC` (JArmCand.lean).
* `Tr Cj q ts`: the translator's trace from J pc `q`: the atoms `ts` it selects (`mkAtom (candC …)`), each passing `e37`.
* `pass1`: if pass 1 (`e46`) returns a non-empty table, there is a trace, the table holds `1 + word index` at exactly
  the atom boundaries, and the word count is below 2^18. -/
import Nano.Run.JArmStep
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-- Gen's words of a J program -/
abbrev gw (Cj : List J) : Buf := Cj.map encG

/-- atoms with the dead flags off (as `natEncJ` builds them) -/
def ats (ts : List NTm) : List NAt := ts.map fun t => (⟨t, false, false⟩ : NAt)

theorem ats_cons (T : NTm) (ts : List NTm) : ats (T :: ts) = ⟨T, false, false⟩ :: ats ts := rfl

/-- the translator's trace from J pc `q` -/
def Tr (Cj : List J) : Nat → List NTm → Prop
  | q, [] => q = Cj.length
  | q, T :: ts => q < Cj.length ∧ candC (Cj.drop q) ≠ 0 ∧
      e37 (gw Cj) (bsize (gw Cj)) q.toUInt64 (candC (Cj.drop q)) ≠ 0 ∧
      mkAtom (candC (Cj.drop q)) (Cj.drop q) = some T ∧ Tr Cj (q + T.j.length) ts

theorem tU_add {a b : Nat} (h : a + b < 2 ^ 64) : a.toUInt64 + b.toUInt64 = (a + b).toUInt64 := by
  apply ArmRA.u64
  rw [UInt64.toNat_add, ArmRA.toU_toNat (by omega), ArmRA.toU_toNat (by omega), ArmRA.toU_toNat h]
  omega

theorem getD_set_same (l : List UInt64) (i : Nat) (v : UInt64) (h : i < l.length) : (l.set i v).getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne (l : List UInt64) (i j : Nat) (v : UInt64) (h : i ≠ j) : (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem bsize_gw (Cj : List J) : bsize (gw Cj) = Cj.length.toUInt64 := by simp [bsize, gw]

theorem bsize_tU (o : Buf) : bsize o = o.length.toUInt64 := rfl

theorem bset_tU (z : Buf) (q : Nat) (v : UInt64) (hq : q < 2 ^ 64) : bset z q.toUInt64 v = z.set q v := by
  unfold bset; rw [ArmRA.toU_toNat hq]

section
variable (B : JArmBits) (S : StepOK) {Cj : List J} (hJ : ∀ j ∈ Cj, JOK j) (hl : Cj.length < 2 ^ 18)
include B S hJ hl

/-- pass 1, an atom: selected, checked, emitted -/
theorem e46_s (k q : Nat) (z o : Buf) (hq : q < Cj.length) (h0 : candC (Cj.drop q) ≠ 0)
    (h37 : e37 (gw Cj) (bsize (gw Cj)) q.toUInt64 (candC (Cj.drop q)) ≠ 0) :
    e46 (k + 1) (gw Cj) (bsize (gw Cj)) q.toUInt64 z o =
      e46 k (gw Cj) (bsize (gw Cj))
        (q.toUInt64 + e36 (gw Cj) (bsize (gw Cj)) q.toUInt64 (candC (Cj.drop q)))
        (bset z q.toUInt64 (bsize o + 1))
        (e40 (gw Cj) (bsize (gw Cj)) (bset z q.toUInt64 (bsize o + 1)) o q.toUInt64 (candC (Cj.drop q))) := by
  have hi : q.toUInt64 < bsize (gw Cj) := by
    rw [bsize_gw]; exact (tU_lt (by omega) (by omega)).2 hq
  have he := e35_eq B hJ hl q (by omega)
  simp only [e46]
  rw [if_pos hi]
  simp only [he]
  rw [if_neg (by simpa using h0), if_neg (by simpa using h37)]

/-- pass 1 rejects where no atom is selected -/
theorem e46_f0 (k q : Nat) (z o : Buf) (hq : q < Cj.length) (h0 : candC (Cj.drop q) = 0) :
    (e46 (k + 1) (gw Cj) (bsize (gw Cj)) q.toUInt64 z o).1 = [] := by
  have hi : q.toUInt64 < bsize (gw Cj) := by
    rw [bsize_gw]; exact (tU_lt (by omega) (by omega)).2 hq
  have he := e35_eq B hJ hl q (by omega)
  simp only [e46]
  rw [if_pos hi]
  simp only [he, h0]
  rfl

/-- pass 1 rejects where the check fails -/
theorem e46_f37 (k q : Nat) (z o : Buf) (hq : q < Cj.length) (h0 : candC (Cj.drop q) ≠ 0)
    (h37 : e37 (gw Cj) (bsize (gw Cj)) q.toUInt64 (candC (Cj.drop q)) = 0) :
    (e46 (k + 1) (gw Cj) (bsize (gw Cj)) q.toUInt64 z o).1 = [] := by
  have hi : q.toUInt64 < bsize (gw Cj) := by
    rw [bsize_gw]; exact (tU_lt (by omega) (by omega)).2 hq
  have he := e35_eq B hJ hl q (by omega)
  simp only [e46]
  rw [if_pos hi]
  simp only [he]
  rw [if_neg (by simpa using h0), h37]
  rfl

/-- pass 1 at the end of the program -/
theorem e46_e (k : Nat) (z o : Buf) :
    e46 (k + 1) (gw Cj) (bsize (gw Cj)) (bsize (gw Cj)) z o =
      if bsize o < 262144 then (bset z (bsize (gw Cj)) (bsize o + 1), o) else (bnew, o) := by
  simp [e46]

/-- **pass 1**: a non-empty table means a trace, the boundary table and the size limit -/
theorem pass1 : ∀ (k q : Nat) (z o : Buf), q ≤ Cj.length → z.length = Cj.length + 1 → o.length ≤ 4 * q →
    (e46 k (gw Cj) (bsize (gw Cj)) q.toUInt64 z o).1 ≠ [] →
    ∃ ts, Tr Cj q ts ∧
      (e46 k (gw Cj) (bsize (gw Cj)) q.toUInt64 z o).1.length = Cj.length + 1 ∧
      (∀ p w, (p, w) ∈ bnd (ats ts) q o.length →
        (e46 k (gw Cj) (bsize (gw Cj)) q.toUInt64 z o).1.getD p 0 = (w + 1).toUInt64) ∧
      (∀ p, (∀ w, (p, w) ∉ bnd (ats ts) q o.length) →
        (e46 k (gw Cj) (bsize (gw Cj)) q.toUInt64 z o).1.getD p 0 = z.getD p 0) ∧
      o.length + alenL (ats ts) < 2 ^ 18
  | 0, q, z, o, _, _, _, h => by
    exact absurd (by simp [e46, bnew]) h
  | k + 1, q, z, o, hq, hz, ho, h => by
    by_cases hlt : q < Cj.length
    · by_cases h0 : candC (Cj.drop q) = 0
      · exact absurd (e46_f0 B S hJ hl k q z o hlt h0) h
      · by_cases h37 : e37 (gw Cj) (bsize (gw Cj)) q.toUInt64 (candC (Cj.drop q)) = 0
        · exact absurd (e46_f37 B S hJ hl k q z o hlt h0 h37) h
        · obtain ⟨T, hmk, htk, hok, -, -, hal, h36, -, h40⟩ := S _ h0 Cj hJ hl q hlt rfl h37
          have hjl : T.j.length ≤ Cj.length - q := by
            have := congrArg List.length htk
            rw [List.length_take, List.length_drop] at this
            omega
          have hjp := T.j_pos
          have es := e46_s B S hJ hl k q z o hlt h0 h37
          rw [h36, tU_add (by omega), h40 _ o, bsize_tU o, tU_succ (by omega), bset_tU z q _ (by omega)] at es
          rw [es] at h ⊢
          have hlen : (o ++ (T.a (zpi (z.set q (o.length + 1).toUInt64)) q o.length).map Nat.toUInt64).length
              = o.length + T.alen := by
            rw [List.length_append, List.length_map, NTm.a_len]
          obtain ⟨ts, tr, zl, za, zb, sz⟩ := pass1 k (q + T.j.length) (z.set q (o.length + 1).toUInt64)
            (o ++ (T.a (zpi (z.set q (o.length + 1).toUInt64)) q o.length).map Nat.toUInt64) (by omega)
            (by rw [List.length_set]; exact hz) (by rw [hlen]; omega) h
          rw [hlen] at za zb sz
          refine ⟨T :: ts, ⟨hlt, h0, h37, hmk, tr⟩, zl, ?_, ?_, ?_⟩
          · intro p w hm
            rw [ats_cons] at hm
            simp only [bnd, List.mem_cons, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩ | hm
            · rw [zb p (fun w hw => by have := (bnd_ge _ _ _ _ _ hw).1; omega)]
              exact getD_set_same _ _ _ (by omega)
            · exact za p w hm
          · intro p hp
            have hpq : q ≠ p := fun e => hp o.length (by rw [ats_cons, ← e]; simp [bnd])
            rw [zb p (fun w hw => hp w (by rw [ats_cons]; simp only [bnd, List.mem_cons]; exact Or.inr hw))]
            exact getD_set_ne _ _ _ _ hpq
          · rw [ats_cons]; simp only [alenL]; omega
    · have e : q = Cj.length := by omega
      subst e
      have ee := e46_e B S hJ hl k z o
      rw [← bsize_gw] at h ⊢
      rw [ee] at h ⊢
      by_cases hs : bsize o < 262144
      · rw [if_pos hs] at h ⊢
        have hs' : o.length < 262144 := by
          have := UInt64.lt_iff_toNat_lt.1 hs
          rw [bsize_tU, ArmRA.toU_toNat (by omega)] at this
          exact this
        rw [bsize_gw, bsize_tU o, tU_succ (by omega), bset_tU z _ _ (by omega)]
        refine ⟨[], rfl, by rw [List.length_set]; exact hz, ?_, ?_, by simp only [ats, List.map_nil, alenL]; omega⟩
        · intro p w hm
          simp only [ats, List.map_nil, bnd, List.mem_singleton, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          exact getD_set_same _ _ _ (by omega)
        · intro p hp
          have hpq : Cj.length ≠ p := fun e => hp o.length (by rw [← e]; simp [ats, bnd])
          exact getD_set_ne _ _ _ _ hpq
      · rw [if_neg hs] at h
        exact absurd rfl h

end

end JT
