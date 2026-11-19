/- Safe retrofit (EVS) P5: defs and calls (box B).  As EVXC with SafeX runs: the prologue's pushes (ra, s0) and the
epilogue's copy / reloads touch cells of [hb, E0) (work cells by `Lay.wok`), the epilogue's `jalr` target is the caller's
return word (base + 4·ret), the call's `jal` lands on the callee entry (inside the code, |C| < 2^18). -/
import Nano.V2Self.Proof.Machine.EVSComp
namespace Templates
open CallProbe SimW SafeRun

/-- **a def**, safe twin of `defX` -/
theorem defXS {KL : LayW} {C : List J} {f lb p nl q hb E0 : Nat} {IG : St → Prop} {Rb Wb : Nat → Prop} {Sb : SemW}
    (hIG : IGOK hb E0 IG) (hP : At C f (proA 1 f (nl - p)))
    (hB : EVHwS KL C (f + 12) lb p nl (IGp IG E0 p) hb E0 Rb Wb q Sb) (hE : At C (f + 12 + lb) (epi p q))
    (hpn : p ≤ nl) (hR : ∀ k, Rb k → k < p) (hnl : nl < 251) (hq : 8 * q < 2048) :
    DefXS KL C f p q IG hb E0 (defS p nl Sb) where
  run := fun s args H vs H' ret I0 z0 R0 hl ha hE0 hE62 hx1 hret hlo hhi hbase ha31 A0 hS => by
    unfold defS at hS
    split at hS
    rotate_left; · simp at hS
    rename_i hc
    have lt64 := (s.x 31).toNat_lt
    have top0 : (s.x 30).toNat = H.top := R0.2.2.2.2.1
    have hbt : hb ≤ H.top := R0.2.1
    have wk : ∀ a, hb ≤ a → a + 8 ≤ E0 → a % 8 = 0 → wok KL a := fun a h1 h2 h3 => ⟨by omega, by omega, h3⟩
    obtain ⟨s1, hr1, h31, h8, hx, hm1⟩ := pro_srun (K := KL) (s := s) hP (by omega) (by rw [top0]; exact hc) (by omega)
      (wk _ (by omega) (by omega) (by omega)) (wk _ (by omega) (by omega) (by omega))
    -- the frame
    let env1 : Env := fun k => s1.m (slotAddr p ((s.x 31).toNat - 16) k)
    have F1 : Frame p nl s1 env1 := by intro k hk; show s1.m (slotAddr p (s1.x 8).toNat k) = _; rw [h8]
    have O1 : FrameOK p nl s1 := ⟨by rw [h31, h8]; omega, hpn, by rw [h8]; omega⟩
    have m1 : ∀ a, a ≠ (s.x 31).toNat - 8 → a ≠ (s.x 31).toNat - 16 → s1.m a = s.m a := by
      intro a h1 h2; rw [hm1, upd_other _ _ h2, upd_other _ _ h1]
    have b1 : s1.b = s.b := hr1.star.b
    have I1 : IGp IG E0 p s1 := by
      refine ⟨hIG s s1 I0 (hx 28 (by decide) (by decide)) (hx 29 (by decide) (by decide)) b1 (fun a ha => ?_), ?_⟩
      · apply m1 <;> intro e <;> apply ha <;> have := R0.2.1 <;> omega
      · rw [h8]; omega
    have z1 : s1.x 0 = 0 := by rw [hx 0 (by decide) (by decide), z0]
    have R1 : HRel hb s1 H := HRel_stack R0 (hx 30 (by decide) (by decide)) (by rw [h31]; omega)
      (fun a _ h2 => m1 a (by omega) (by omega))
    have L1 : Lay KL hb E0 p s1 :=
      ⟨hlo, hhi, by rw [b1, hbase], by rw [h8]; omega, by rw [h31]; omega, by rw [h8]; omega⟩
    have hS1 : Sb env1 (s1.x 31).toNat H = some (vs, H') := by
      rw [h31, ← hS]; apply hB.stable; intro k hk
      have hkp := hR k hk
      simp only [env1, argEnv, hkp, if_true]
      rw [slotAddr_param hkp, m1 _ (by omega) (by omega), ← ha k hkp]; congr 1; omega
    obtain ⟨s2, env2, r2, I2, z2, p2, l2, v2, e82, F2, ag2, R2, A2, m2⟩ := hB.run s1 env1 H vs H' I1 z1 F1 O1 R1 L1 A0 hS1
    rw [h31] at p2 v2 m2
    have slot_ne : ∀ k, k < nl → slotAddr p ((s.x 31).toNat - 16) k ≠ (s.x 31).toNat - 8 ∧ slotAddr p ((s.x 31).toNat - 16) k ≠ (s.x 31).toNat - 16 ∧
        slotAddr p ((s.x 31).toNat - 16) k < (s.x 31).toNat + 8 * p := by
      intro k hk; unfold slotAddr slotOff; split <;> omega
    have s2ra : s2.m ((s.x 31).toNat - 8) = UInt64.ofNat (s.b + 4 * ret) := by
      rw [m2 _ (by omega) (fun k hk _ => by rw [h8]; exact (slot_ne k hk).1.symm), hm1, upd_other _ _ (by omega),
        upd_same, hx1]
    have s2s0 : s2.m ((s.x 31).toNat - 16) = s.x 8 := by
      rw [m2 _ (by omega) (fun k hk _ => by rw [h8]; exact (slot_ne k hk).2.1.symm), hm1, upd_same]
    have x82 : (s2.x 8).toNat = (s.x 31).toNat - 16 := by rw [e82, h8]
    have top2 : H'.top ≤ (s2.x 31).toNat := R2.2.2.1
    have sp16 : 16 ≤ (s.x 31).toNat := by have := R0.2.2.1; omega
    have sp2lo : 16 + 8 * q ≤ (s.x 31).toNat - 16 - 8 * (nl - p) := by
      have := R2.1; have := R2.2.1; have := R2.2.2.1; omega
    have hD1 : (s2.x 31).toNat + 8 * q ≤ (s2.x 8).toNat + 8 * p + 16 := by rw [p2, x82]; omega
    have hD2 : (s2.x 8).toNat + 8 * p + 16 < 2 ^ 63 := by rw [x82]; omega
    have b2 : s2.b = s.b := r2.star.b.trans b1
    have hbt2 : hb ≤ H'.top := R2.2.1
    obtain ⟨s3, hr3, b3, p3, x83, hx3, hm3⟩ := epi_srun (K := KL) s2 hE hD1 hD2 (by omega) hq
      (wk _ (by rw [x82]; omega) (by rw [x82]; omega) (by rw [x82]; omega))
      (wk _ (by rw [x82]; omega) (by rw [x82]; omega) (by rw [x82]; omega))
      (fun k hk => ⟨wk _ (by omega) (by rw [p2]; omega) (by rw [p2]; omega),
        wk _ (by rw [x82]; omega) (by rw [x82]; omega) (by rw [x82]; omega)⟩)
      ⟨ret, by
        rw [x82, show (s.x 31).toNat - 16 + 8 = (s.x 31).toNat - 8 by omega, s2ra, ← hbase]
        simp; omega⟩
    have pc3 : ((s2.m ((s2.x 8).toNat + 8)).toNat - s2.b) / 4 = ret := by
      rw [x82, show (s.x 31).toNat - 16 + 8 = (s.x 31).toNat - 8 by omega, s2ra, b2]
      have : (UInt64.ofNat (s.b + 4 * ret)).toNat = s.b + 4 * ret := by simp; omega
      rw [this]; omega
    rw [pc3] at hr3
    rw [x82, show (s.x 31).toNat - 16 + 8 * p + 16 = (s.x 31).toNat + 8 * p by omega] at hm3 p3
    have mo : ∀ a, (a + 8 * q < (s.x 31).toNat + 8 * p ∨ (s.x 31).toNat + 8 * p ≤ a) → s3.m a = s2.m a := by
      intro a ha; rw [hm3]; exact Mc_out _ _ _ q (by omega) q (Nat.le_refl _) a ha
    refine ⟨s3, ((SStarX.of hr1).trans r2).trans (SStarX.of hr3), ?_, ?_, by rw [p3], l2, ?_, ?_, ?_, A2, ?_⟩
    · apply hIG s2 s3 I2.1 (hx3 28 (by decide) (by decide) (by decide) (by decide) (by decide))
        (hx3 29 (by decide) (by decide) (by decide) (by decide) (by decide)) b3
      intro a ha; apply mo
      have := R2.2.1; omega
    · rw [hx3 0 (by decide) (by decide) (by decide) (by decide) (by decide), z2]
    · intro i hi
      rw [hm3, Mc_dest _ _ _ q (by omega) q (Nat.le_refl _) i hi, p2]
      rw [show (s.x 31).toNat - 16 - 8 * (nl - p) - 8 * q + 8 * (q - 1 - i) = (s.x 31).toNat - 16 - 8 * (nl - p) - 8 * (i + 1) by omega]
      exact v2 i (by omega)
    · rw [x83, x82, s2s0]
    · refine HRel_stack R2 (hx3 30 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [p3]; omega) ?_
      intro a _ h2; exact mo a (by omega)
    · intro a ha
      rw [mo a (Or.inr ha), m2 a (by omega) (fun k hk _ => by rw [h8]; have := (slot_ne k hk).2.2; omega)]
      exact m1 a (by omega) (by omega)

/-- **CALL**, safe twin of `callX`: the jal lands on the callee entry `f` (an Int equation, so the target is
non-negative), inside the code -/
theorem callXS {KL : LayW} {C : List J} {pc la p nl pa q f hb E0 : Nat} {IG : St → Prop} {RA WA : Nat → Prop} {SA : SemW}
    {Sd : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)} {off : Int}
    (hIG : IGOK hb E0 IG) (hA : EVHwS KL C pc la p nl (IGp IG E0 p) hb E0 RA WA pa SA)
    (hj : C[pc + la]? = some (.jal 1 off)) (hf : ((pc + la : Nat) : Int) + off = (f : Int))
    (hD : DefXS KL C f pa q IG hb E0 Sd) (hE62 : E0 < 2 ^ 62)
    (hcb : ∀ s, IG s → s.b + 4 * (pc + la + 1) < 2 ^ 64) (hfl : f < C.length) (hC18 : C.length < 2 ^ 18) :
    EVHwS KL C pc (la + 1) p nl (IGp IG E0 p) hb E0 RA WA q (callS pa SA Sd) where
  stable := fun env env' sp H h => by
    simp only [callS]; rw [hA.stable env env' sp H h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [callS, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨u, H1⟩, hSA, hSd⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, lu, v1, e81, F1, ag1, R1, A1, m1⟩ := hA.run s env H u H1 I0 z0 F0 O0 R0 L0 A0 hSA
    obtain ⟨o1, o2, o3⟩ := O0
    have sp1 : 16 ≤ (s1.x 31).toNat := hrel_sp R1
    have hpcl : pc + la < C.length := by
      rcases Nat.lt_or_ge (pc + la) C.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hj; cases hj
    have hf' : (((pc + la : Nat) : Int) + off).toNat = f := by rw [hf]; simp
    let sj := wr s1 1 (UInt64.ofNat (s1.b + 4 * (pc + la + 1)))
    have stj : step C (pc + la, s1) = some (f, sj) := by rw [s_jal hj, hf']
    have saj : SafeX KL C (pc + la, s1) := by
      simp only [SafeX, hj]; refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> omega
    have ej : sj = { s1 with x := upd s1.x 1 (UInt64.ofNat (s1.b + 4 * (pc + la + 1))) } := by simp [sj, wr]
    have jx : ∀ i, i ≠ 1 → sj.x i = s1.x i := by intro i hi; rw [ej]; simp [upd, hi]
    have jm : sj.m = s1.m := by rw [ej]
    have jb : sj.b = s1.b := by rw [ej]
    have b1 : s1.b = s.b := r1.star.b
    have L1 : Lay KL hb E0 p s1 := L0.post e81 b1 p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    have Ij : IG sj := hIG s1 sj I1.1 (jx 28 (by decide)) (jx 29 (by decide)) jb (fun a _ => by rw [jm])
    have Rj : HRel hb sj H1 := HRel_stack R1 (jx 30 (by decide)) (by rw [jx 31 (by decide)]; exact R1.2.2.1)
      (fun a _ _ => by rw [jm])
    have j31 : (sj.x 31).toNat = (s.x 31).toNat - 8 * pa := by rw [jx 31 (by decide), p1]
    have hargs : ∀ i, i < pa → sj.m ((sj.x 31).toNat + 8 * (pa - 1 - i)) = u.getD i 0 := by
      intro i hi; rw [jm, j31, show (s.x 31).toNat - 8 * pa + 8 * (pa - 1 - i) = (s.x 31).toNat - 8 * (i + 1) by omega]
      exact v1 i hi
    have htop : (sj.x 31).toNat + 8 * pa ≤ E0 := by have := I0.2; rw [j31]; omega
    have hx1 : sj.x 1 = UInt64.ofNat (sj.b + 4 * (pc + la + 1)) := by rw [ej]; simp [upd]
    have hret : sj.b + 4 * (pc + la + 1) < 2 ^ 64 := by rw [jb, b1]; exact hcb s I0.1
    have hSd' : Sd u (sj.x 31).toNat H1 = some (vs, H') := by rw [j31]; exact hSd
    have ja : (sj.x 31).toNat % 8 = 0 := by rw [jx 31 (by decide)]; exact L1.a31
    obtain ⟨s', st', I', z', p', l', v', e8', R', A', m'⟩ :=
      hD.run sj u H1 vs H' (pc + la + 1) Ij (by rw [jx 0 (by decide), z1]) Rj lu hargs htop hE62 hx1 hret L0.lo L0.hi
        (by rw [jb, b1, L0.base]) ja A1 hSd'
    rw [j31, show (s.x 31).toNat - 8 * pa + 8 * pa = (s.x 31).toNat by omega] at p' v' m'
    have x8 : s'.x 8 = s.x 8 := by rw [e8', jx 8 (by decide), e81]
    refine ⟨s', env1, r1.trans (.head saj stj st'), ⟨I', by rw [x8]; exact I0.2⟩, z', p', l', v', x8, ?_, ag1, R', A', ?_⟩
    · intro k hk
      show s'.m (slotAddr p (s'.x 8).toNat k) = env1 k
      have hk' := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk
      rw [x8, m' _ hk', jm, ← e81]; exact F1 k hk
    · intro a ha hW
      rw [m' a ha, jm]; exact m1 a ha hW

end Templates
