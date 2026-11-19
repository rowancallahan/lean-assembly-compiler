/- Nano/V2Self/Proof/Own/OwnP26: one verify walk `o35 … 0` of a def body = `defOk`'s body result. -/
import Nano.V2Self.Proof.Own.OwnP25
namespace OwnP
open C OwnSpec ParSpec

/-- what `o35` needs: registers 1, 2, 6, 12 (body start), 13; kinds in `f`; sizes -/
def Pre (W : WCx) (s f v : Buf) (i0 : Nat) : Prop :=
  16 ≤ s.length ∧ s.length < 2 ^ 62 ∧ bget s 1 = 0 ∧ bget s 2 = u W.npw ∧ bget s 6 = u W.ns ∧ bget s 12 = u i0 ∧
  bget s 13 = u W.ps.length ∧ 2 * W.ns ≤ f.length ∧ f.length < 2 ^ 62 ∧ (∀ q < W.ns, f.getD q 0 = u (W.K.getD q 0)) ∧
  v.length < 2 ^ 62 ∧ RT W ∧ W.ns < 2 ^ 20 ∧ W.npw ≤ W.ns ∧ (∀ k ∈ W.K, k ≤ 2) ∧ W.x.length < 2 ^ 40 ∧ i0 < 2 ^ 40

def A0 (i0 ns : Nat) : AS := ⟨i0, [], List.replicate ns false, [], [], 0⟩

theorem getD_bset (s : Buf) (i : Nat) (hi : i < 2 ^ 64) (x : UInt64) (k : Nat) :
    (bset s (u i) x).getD k 0 = if i = k ∧ i < s.length then x else s.getD k 0 := by
  rw [bset_u s hi, getD_set]

theorem st0 {W : WCx} {s f v : Buf} {i0 : Nat} (hP : Pre W s f v i0) :
    St W (bset (bset (bset (bset (bset (bset (bset (bset s (u 0) (u i0)) (u 4) (u 0)) (u 5) (u 0)) (u 7) (u 0)) (u 8) (u 0))
      (u 10) (u 0)) (u 11) (u 0)) (u 9) (u 0)) (o22 16777216 f (u W.ns) (u W.ns) (u 0) (u W.ns) (u 3)) v (A0 i0 W.ns) := by
  obtain ⟨hl, hl2, h1, h2, h6, h12, h13, hf, hf2, hK, hv, hT, hns, hnpw, hK2, hx, hi0⟩ := hP
  simp only [lit] at h1 h2 h6 h13
  rw [bget_u s (by omega)] at h1 h2 h6 h13
  have z := o22_zero 16777216 f W.ns W.ns 0 W.ns (by omega) hf2 (by omega) (by omega) (by omega)
  refine ⟨⟨by simp [bset, A0]; omega, by simp [bset]; omega, fun k x hk => ?_, fun j hj => by simp [A0] at hj⟩,
    ⟨by simp [A0], by simp [A0], by rw [z.1]; simp [A0]; omega, by rw [z.1]; exact hf2, fun q hq => ?_, fun q hq => ?_,
      fun j hj => by simp [A0] at hj⟩,
    ⟨by simp [A0], hv, fun j hj => by simp [A0] at hj⟩, hT,
    ⟨hns, hnpw, hK2, hx, hi0, by simp [A0], by simp [A0], by simp [A0], by simp [A0], by simp [A0], by simp [A0]⟩⟩
  · have hk16 : k < 16 := by
      have := (List.getElem?_eq_some_iff.mp hk).1; simpa [regL_len] using this
    have hu : (u i0).toNat = i0 := u_toNat (by omega)
    simp only [List.getD_eq_getElem?_getD] at h1 h2 h6 h13
    have l0 : 0 < s.length := by omega
    have l4 : 4 < s.length := by omega
    have l5 : 5 < s.length := by omega
    have l7 : 7 < s.length := by omega
    have l8 : 8 < s.length := by omega
    have l9 : 9 < s.length := by omega
    have l10 : 10 < s.length := by omega
    have l11 : 11 < s.length := by omega
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
      k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> simp [regL, A0] at hk <;> subst hk <;> simp [bset, getD_set, hu, List.getElem?_set, show (u 0).toNat = 0 from rfl, show (u 4).toNat = 4 from rfl, show (u 5).toNat = 5 from rfl, show (u 7).toNat = 7 from rfl, show (u 8).toNat = 8 from rfl, show (u 9).toNat = 9 from rfl, show (u 10).toNat = 10 from rfl, show (u 11).toNat = 11 from rfl, l0, l4, l5, l7, l8, l9, l10, l11, h1, h2, h6, h13] <;> rfl
  · rw [z.2, if_neg (by omega)]; exact hK q hq
  · rw [z.2, if_pos (by omega)]; simp [A0, List.getD_eq_getElem?_getD, hq, b2n]; rfl

/-- a def body: a LOOP's arms, or a WF node -/
def WFB : Nd → Prop
  | .loop z s => WFN z ∧ WFN s
  | b => WFN b

theorem wfb_n {b : Nd} (hnl : ∀ z st, b ≠ .loop z st) (hb : WFB b) : WFN b := by
  cases b <;> first | exact hb | exact absurd rfl (hnl _ _)

theorem ag_b5 (s : Buf) : Ag (bset s 5 1) s := by
  refine ⟨by simp [bset], fun k hk => ?_⟩
  simp only [bset]; rw [getD_set]; simp only [show (5 : UInt64).toNat = 5 from rfl]; rw [if_neg (by omega)]

theorem ag_symm {s s' : Buf} (h : Ag s s') : Ag s' s := ⟨h.1.symm, fun k hk => (h.2 k hk).symm⟩

/-- what `o35` leaves: cursor after the body, the result entries `ks` in `v[0, |ks|)`, kinds kept, sizes -/
def Post (W : WCx) (r : Buf × (Buf × Buf)) (i1 : Nat) (ks : List Nat) : Prop :=
  16 ≤ r.1.length ∧ r.1.length < 2 ^ 62 ∧ bget r.1 0 = u i1 ∧ bget r.1 1 = 0 ∧ bget r.1 7 = u ks.length ∧
  bget r.1 13 = u W.ps.length ∧ r.2.1.length < 2 ^ 62 ∧ (∀ q < W.ns, r.2.1.getD q 0 = u (W.K.getD q 0)) ∧
  2 * W.ns ≤ r.2.1.length ∧ r.2.2.length < 2 ^ 62 ∧ (∀ j < ks.length, r.2.2.getD j 0 = u (ks.getD j 0)) ∧
  ks.length ≤ 2 ^ 24 ∧ ∀ e ∈ ks, e ≤ 1

theorem o35_ok {W : WCx} {s f v : Buf} {i0 : Nat} (hP : Pre W s f v i0) {b : Nd} (hb : WFB b) {rest : List UInt64}
    (hx : W.x.drop i0 = b.ser ++ rest) (hok : bget (o35 W.x s f v W.t 0).1 1 ≠ 1) :
    ∃ ks, rootR W.oc (List.replicate W.ns false) b = some ks ∧ Post W (o35 W.x s f v W.t 0) (i0 + b.ser.length) ks := by
  have hSt0 := st0 hP
  obtain ⟨-, -, -, -, h6, h12, -⟩ := hP
  generalize hs1 : bset (bset (bset (bset (bset (bset (bset (bset s (u 0) (u i0)) (u 4) (u 0)) (u 5) (u 0)) (u 7) (u 0))
      (u 8) (u 0)) (u 10) (u 0)) (u 11) (u 0)) (u 9) (u 0) = s1 at hSt0
  generalize hf1 : o22 16777216 f (u W.ns) (u W.ns) (u 0) (u W.ns) (u 3) = f1 at hSt0
  have e : o35 W.x s f v W.t 0 = (match run W 16777216 (s1, f1, v) with
      | (s2, (f2, v2)) => if bget s2 1 == 1 then (s2, (f2, v2)) else o15 16777216 s2 f2 v2 0 (bget s2 7)) := by
    rw [← hs1, ← hf1]; unfold o35 run; simp only [h6, h12]; rfl
  have hR : Reach W (s1, f1, v) (RootP W (A0 i0 W.ns) b) := by
    by_cases hl : ∃ z st, b = .loop z st
    · obtain ⟨z, st, rfl⟩ := hl; exact sim_rloop hb.1 hb.2 hSt0 rfl rfl rfl hx
    · have hnl : ∀ z st, b ≠ .loop z st := fun z st h => hl ⟨z, st, h⟩
      exact sim_root (wfb_n hnl hb) hnl hSt0 rfl hx
  have hok1 : bget (run W 16777216 (s1, f1, v)).1 1 ≠ 1 := by
    intro h; apply hok; rw [e]; revert h; generalize run W 16777216 (s1, f1, v) = R; obtain ⟨s2, f2, v2⟩ := R
    intro h; simp only at h ⊢; simp [h]
  obtain ⟨k, -, ⟨F', en, himp, hSk⟩, hrun⟩ := run_reach hR 16777216 hok1
  revert hSk hrun; generalize it W k (s1, f1, v) = σk; obtain ⟨sk, fk, vk⟩ := σk; intro hrun hSk
  have hfin := run_fin hSk rfl rfl (16777216 - k) (by rw [← hrun]; exact hok1)
  rw [hrun, hfin] at e
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSk
  have r := regs hS
  simp only [lit] at r
  have g1 : bget (bset sk 5 1) 1 = 0 := by rw [ag_get (ag_b5 sk) (k := 1) (by decide)]; simpa using r.2.1
  have g7 : bget (bset sk 5 1) 7 = u en.length := by
    rw [ag_get (ag_b5 sk) (k := 7) (by decide)]; simpa [A0] using r.2.2.2.2.2.2.1
  simp only [g1, g7, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false] at e
  have hag := o15_ag 16777216 (bset sk 5 1) sk fk vk 0 (u en.length) (ag_b5 sk)
  have hesl : ({ A0 i0 W.ns with i := i0 + b.ser.length, F := F', es := (A0 i0 W.ns).es ++ en, ph := 1 } : AS).es.length
      = en.length := by simp [A0]
  rcases o15_ok 16777216 _ fk vk 0 hS hF hV hB (by omega) with ⟨F'', ks, f', v', htr, ho15, hF1, hV1⟩ | herr
  · rw [hesl, show (0 : UInt64) = u 0 from rfl] at *
    rw [ho15] at hag
    simp only [A0, List.nil_append, List.drop_zero, List.take_zero] at htr hV1 hF1 hB himp
    obtain ⟨hkl, hk1⟩ := tr_len' _ _ _ _ htr
    refine ⟨ks, himp F'' ks htr, ?_⟩
    rw [e]
    obtain ⟨ha, hsnd⟩ := hag
    revert ha hsnd; generalize o15 16777216 (bset sk 5 1) fk vk (u 0) (u en.length) = R; obtain ⟨s', f'', v''⟩ := R
    intro ha hsnd; simp only [Prod.mk.injEq] at ha hsnd; obtain ⟨rfl, rfl⟩ := hsnd
    simp only [Post]
    have hl16 := hS.1
    have ag0 := ag_get ha (k := 0) (by decide)
    have ag1 := ag_get ha (k := 1) (by decide)
    have ag7 := ag_get ha (k := 7) (by decide)
    have ag13 := ag_get ha (k := 13) (by decide)
    refine ⟨by rw [ha.1]; simp [bset, A0] at hl16 ⊢; omega, by rw [ha.1]; simp [bset]; exact hS.2.1, ?_, ?_, ?_, ?_,
      hF1.2.2.2.1, hF1.2.2.2.2.1, by have := hF1.2.2.1; simp at this; omega, hV1.2.1, fun j hj => ?_, by
        have := hB.2.2.2.2.2.2.2.1; simp at this; omega, hk1⟩
    · rw [ag0]; simpa [A0, lit] using r.1
    · rw [ag1]; simpa [lit] using r.2.1
    · rw [ag7]; simpa [A0, hkl, lit] using r.2.2.2.2.2.2.1
    · rw [ag13]; simpa [lit] using r.2.2.2.2.2.2.2.2.2.2
    · have := hV1.2.2 j (by simpa using hj); simpa using this
  · exfalso; apply hok; rw [e]
    rw [hesl] at herr
    rw [ag_get hag.1 (k := 1) (by decide)]; exact herr

end OwnP
