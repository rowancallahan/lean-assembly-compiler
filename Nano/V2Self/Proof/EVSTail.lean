/- Safe retrofit (EVS) P3: tail mode (EVXT) as `EVHtS` (Opus box E). -/
import Nano.V2Self.Proof.EVSFin
namespace Templates
open CallProbe SimW SafeRun

theorem valTS {KL : LayW} {C : List J} {pc lc p nl hb E0 w X Hd : Nat} {Inv : St → Prop} {R W : Nat → Prop} {S : SemW}
    (h : EVHwS KL C pc lc p nl Inv hb E0 R W w S) (hJ : C[pc + lc]? = some (.jal 0 ((X : Int) - ((pc + lc : Nat) : Int))))
    (hX : X < C.length) (hpc : pc + lc < C.length) (hC18 : C.length < 2 ^ 18) :
    EVHtS KL C pc p nl Inv hb E0 R W w X Hd (exitS S) where
  stable := fun env env' sp H hk => by simp only [exitS]; rw [h.stable env env' sp H hk]
  cont := fun s env H st H' _ _ _ _ _ _ _ hS => by
    simp only [exitS, Option.map_eq_some_iff] at hS
    obtain ⟨_, _, e⟩ := hS; simp at e
  exit := fun s env H vs H' I0 z0 F0 O0 R0 L0 A0 hS => by
    simp only [exitS, Option.map_eq_some_iff] at hS
    obtain ⟨⟨u, H1⟩, hS, e⟩ := hS
    simp only [Prod.mk.injEq, Sum.inl.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    obtain ⟨s', env', r, I, z, p31, l, v, e8, F, ag, hR, hA, mm⟩ := h.run s env H u H1 I0 z0 F0 O0 R0 L0 A0 hS
    have sj : step C (pc + lc, s') = some (X, wr s' 0 (UInt64.ofNat (s'.b + 4 * (pc + lc + 1)))) := by
      simp [step, hJ]; omega
    have w0 : wr s' 0 (UInt64.ofNat (s'.b + 4 * (pc + lc + 1))) = s' := by simp [wr]
    rw [w0] at sj
    have sx : SafeX KL C (pc + lc, s') := by simp only [SafeX, hJ]; simp; omega
    exact ⟨s', env', r.trans (.head sx sj (.refl _)), I, z, p31, l, v, e8, F, ag, hR, hA, mm⟩

theorem contTS {KL : LayW} {C : List J} {pc le p nl hb E0 w X Hd : Nat} {Inv : St → Prop} {R W : Nat → Prop} {S : SemW}
    (hI : InvOKH hb p Inv)
    (he : EVHwS KL C pc le p nl Inv hb E0 R W (p - 1) S) (hS : At C (pc + le) (popN p 1 (p - 1)))
    (hJ : C[pc + le + 3 * (p - 1)]? = some (.jal 0 ((Hd : Int) - ((pc + le + 3 * (p - 1) : Nat) : Int))))
    (hp : 1 ≤ p) (hpn : p ≤ nl) (hnl : nl < 251) (hHd : Hd < C.length) (hpc : pc + le + 3 * (p - 1) < C.length)
    (hC18 : C.length < 2 ^ 18) :
    EVHtS KL C pc p nl Inv hb E0 R W w X Hd (contS S) where
  stable := fun env env' sp H hk => by simp only [contS]; rw [he.stable env env' sp H hk]
  exit := fun s env H st H' _ _ _ _ _ _ _ hS => by
    simp only [contS, Option.map_eq_some_iff] at hS
    obtain ⟨_, _, e⟩ := hS; simp at e
  cont := fun s env H st H' I0 z0 F0 O0 R0 L0 A0 hS' => by
    simp only [contS, Option.map_eq_some_iff] at hS'
    obtain ⟨⟨u, H1⟩, hSV, e⟩ := hS'
    simp only [Prod.mk.injEq, Sum.inr.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    obtain ⟨s1, env1, r1, I1, z1, p1, lu, v1, e81, F1, ag1, R1, A1, m1⟩ := he.run s env H u H1 I0 z0 F0 O0 R0 L0 A0 hSV
    obtain ⟨o1, o2, o3⟩ := O0
    have lt64 := (s.x 31).toNat_lt
    have sp1 := hrel_sp R1
    have T1 : (s1.x 31).toNat + 8 * (p - 1) = (s.x 31).toNat := by rw [p1]; have := R1.2.2.1; omega
    obtain ⟨s2, r2, p2, e82, ex2, eb2, ms2, mo2⟩ := popN_run (p := p) (k0 := 1) (p - 1) (pc + le) s1 hS (by omega)
      (fun j j' hj hj' e => by have := slotAddr_inj (nl := nl) (by rw [e81]; omega) (by omega) (by omega) e; omega)
      (fun j i hj hi => by
        rw [e81]; have := slotAddr_ge (T := (s.x 31).toNat) (k := 1 + j) (nl := nl) (by omega) o2 (by omega); omega)
    have L1 : Lay KL hb E0 p s1 := L0.post e81 r1.star.b p1 (by have := R1.1; have := R1.2.1; have := R1.2.2.1; omega)
    have ss2 : SStarX KL C (pc + le, s1) (pc + le + 3 * (p - 1), s2) := SStarX.of (popN_srun (p - 1) (pc + le) s1 hS
      (by omega)
      (fun j hj => by
        have hk : 1 + j < nl := by omega
        obtain ⟨g1, g2, g3, g4⟩ := slotT_wok (k := 1 + j) L1 ⟨by rw [p1, e81]; omega, o2, by rw [e81]; omega⟩
          (by have := R1.2.1; have := R1.2.2.1; omega) hk hnl
        refine ⟨L1.wok (by have := R1.2.1; have := R1.2.2.1; omega) (by have := L0.top; omega)
          (by have := L1.a31; omega), g1, g2, g3, g4⟩)
      _ r2)
    rw [e81] at ms2 mo2
    have x31 : (s2.x 31).toNat = (s.x 31).toNat := by rw [p2, T1]
    have x8 : s2.x 8 = s.x 8 := by rw [e82, e81]
    have x30 : s2.x 30 = s1.x 30 := ex2 30 (by decide) (by decide)
    have F2 : Frame p nl s2 (setW env1 1 (p - 1) u) := by
      intro k hk
      show s2.m (slotAddr p (s2.x 8).toNat k) = setW env1 1 (p - 1) u k
      rw [x8]
      by_cases e : 1 ≤ k ∧ k < 1 + (p - 1)
      · have := ms2 (k - 1) (by omega)
        rw [show 1 + (k - 1) = k by omega] at this
        rw [this, show (s1.x 31).toNat + 8 * (p - 1 - 1 - (k - 1)) = (s.x 31).toNat - 8 * (k - 1 + 1) by omega,
          v1 (k - 1) (by omega)]
        simp [setW, e]
      · rw [mo2 _ (fun j hj h => e (by have := slotAddr_inj (nl := nl) (by omega) hk (by omega) h; omega))]
        simp only [setW, e, if_false]; rw [← e81]; exact F1 k hk
    have slot_hi : ∀ j, j < p - 1 → (s.x 31).toNat ≤ slotAddr p (s.x 8).toNat (1 + j) ∧
        slotAddr p (s.x 8).toNat (1 + j) < (s.x 8).toNat + 8 * p + 16 := fun j hj =>
      ⟨slotAddr_ge (T := (s.x 31).toNat) (k := 1 + j) (nl := nl) (by omega) o2 (by omega),
        slotAddr_lt (nl := nl) (by omega) (by omega)⟩
    have I2 : Inv s2 := by
      apply hI s1 s2 I1 (by rw [e82]) (ex2 28 (by decide) (by decide)) (ex2 29 (by decide) (by decide)) eb2
      intro a ha
      apply mo2 a; intro j hj e; apply ha; rw [e81, e]
      have hh := slot_hi j hj; have := R1.1; have := R1.2.1; have := R1.2.2.1
      exact ⟨by omega, hh.2⟩
    have z2 : s2.x 0 = 0 := by rw [ex2 0 (by decide) (by decide), z1]
    have R2 : HRel hb s2 H1 := HRel_stack R1 x30 (by rw [x31]; have := R1.2.2.1; omega) (fun a h1 h2 => by
      apply mo2 a; intro j hj e; have := slot_hi j hj; have := R1.2.2.1; omega)
    have sj : step C (pc + le + 3 * (p - 1), s2) = some (Hd, s2) := by
      simp [step, hJ, wr]; omega
    have sx : SafeX KL C (pc + le + 3 * (p - 1), s2) := by simp only [SafeX, hJ]; simp; omega
    refine ⟨s2, env1, (r1.trans ss2).trans (.head sx sj (.refl _)), I2, z2, x31, lu, x8, F2, ag1, R2, A1, ?_⟩
    intro a ha hW
    rw [mo2 a (fun j hj e => hW (1 + j) (by omega) (Or.inr ⟨by omega, by omega⟩) e)]
    exact m1 a ha (fun k hk wk => hW k hk (Or.inl wk))


end Templates
