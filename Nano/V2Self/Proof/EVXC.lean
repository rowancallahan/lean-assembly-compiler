/- Machine bridge (Opus box E): defs and calls under the heap contract.
* `IG` = the GLOBAL invariant (input registers / bytes, code-base bound …): reads only x28, x29, the code base and
  memory outside the work area [hb, E0) (`IGOK`); inside a def with p parameter words the contract invariant is
  `IGp IG E0 p` (also: the frame top s0 + 8p + 16 is at most E0), which is `InvOKH`.
* `DefX C f p q IG hb E0 Sd`: entered at word f with the p argument words on the stack (argument i at t6 + 8(p−1−i)),
  ra in x1: if `Sd args sp H` succeeds the def returns to ra with the q result words in place of the arguments, s0 kept,
  memory at or above the old argument top unchanged.
* `defX`: prologue (`proA 1 f r`, Gen's g38) ++ body (EVHw) ++ epilogue (`epi p q`) is a `DefX`.
* `callX`: argument words (EVHw p) then `jal ra f` is an EVHw q fragment of the caller. -/
import Nano.V2Self.Proof.EVXF
import Nano.V2Self.Proof.CallA
namespace Templates
open CallProbe

def IGOK (hb E0 : Nat) (IG : St → Prop) : Prop :=
  ∀ s s' : St, IG s → s'.x 28 = s.x 28 → s'.x 29 = s.x 29 → s'.b = s.b →
    (∀ a, ¬ (hb ≤ a ∧ a < E0) → s'.m a = s.m a) → IG s'

def IGp (IG : St → Prop) (E0 p : Nat) : St → Prop := fun s => IG s ∧ (s.x 8).toNat + 8 * p + 16 ≤ E0

theorem invOKH_IGp {hb E0 : Nat} {IG : St → Prop} (h : IGOK hb E0 IG) (p : Nat) :
    InvOKH hb p (IGp IG E0 p) := by
  intro s s' ⟨I, hB⟩ e8 e28 e29 eb hm
  refine ⟨h s s' I e28 e29 eb (fun a ha => hm a ?_), by rw [e8]; exact hB⟩
  intro q; exact ha ⟨q.1, by have := q.2; omega⟩

/-- the epilogue's copy touches only [D − 8q, D) -/
theorem Mc_out (m : Nat → UInt64) (T D q : Nat) (hD : 8 * q ≤ D) :
    ∀ k, k ≤ q → ∀ a, (a + 8 * k < D ∨ D ≤ a) → Mc m T D q k a = m a
  | 0, _, _, _ => rfl
  | k + 1, hk, a, ha => by
    simp only [Mc]; rw [upd_other _ _ (by omega)]; exact Mc_out m T D q hD k (by omega) a (by omega)

structure DefX (C : List J) (f p q : Nat) (IG : St → Prop) (hb E0 : Nat)
    (Sd : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)) : Prop where
  run : ∀ (s : St) (args : List UInt64) (H : Hp) (vs : List UInt64) (H' : Hp) (ret : Nat), IG s → s.x 0 = 0 →
    HRel hb s H → args.length = p → (∀ i, i < p → s.m ((s.x 31).toNat + 8 * (p - 1 - i)) = args.getD i 0) →
    (s.x 31).toNat + 8 * p ≤ E0 → E0 < 2 ^ 62 → s.x 1 = UInt64.ofNat (s.b + 4 * ret) → s.b + 4 * ret < 2 ^ 64 →
    Sd args (s.x 31).toNat H = some (vs, H') →
    ∃ s', Star C (f, s) (ret, s') ∧ IG s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat + 8 * p - 8 * q ∧
      vs.length = q ∧ (∀ i, i < q → s'.m ((s.x 31).toNat + 8 * p - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
      HRel hb s' H' ∧ ∀ a, (s.x 31).toNat + 8 * p ≤ a → s'.m a = s.m a

/-- the parameter environment of a call (locals 0: a well-scoped body never reads them before writing) -/
def argEnv (p : Nat) (args : List UInt64) : Env := fun k => if k < p then args.getD k 0 else 0

/-- the def semantics: the prologue's room check, then the body in the new frame -/
def defS (p nl : Nat) (Sb : SemW) : List UInt64 → Nat → Hp → Option (List UInt64 × Hp) :=
  fun args sp H => if H.top + 16 + 8 * (nl - p) ≤ sp then Sb (argEnv p args) (sp - 16 - 8 * (nl - p)) H else none

theorem slotAddr_param {p S0 k : Nat} (hk : k < p) : slotAddr p S0 k = S0 + 16 + 8 * (p - 1 - k) := by
  unfold slotAddr slotOff; rw [if_pos hk]; omega

/-- **a def**: prologue (r = nl − p local words), body, epilogue -/
theorem defX {C : List J} {f lb p nl q hb E0 : Nat} {IG : St → Prop} {Rb Wb : Nat → Prop} {Sb : SemW}
    (hIG : IGOK hb E0 IG) (hP : At C f (proA 1 f (nl - p)))
    (hB : EVHw C (f + 12) lb p nl (IGp IG E0 p) hb Rb Wb q Sb) (hE : At C (f + 12 + lb) (epi p q))
    (hpn : p ≤ nl) (hR : ∀ k, Rb k → k < p) :
    DefX C f p q IG hb E0 (defS p nl Sb) where
  run := fun s args H vs H' ret I0 z0 R0 hl ha hE0 hE62 hx1 hret hS => by
    unfold defS at hS
    split at hS
    rotate_left; · simp at hS
    rename_i hc
    have lt64 := (s.x 31).toNat_lt
    have top0 : (s.x 30).toNat = H.top := R0.2.2.2.2.1
    obtain ⟨s1, hr1, h31, h8, hx, hm1⟩ := pro_runA (s := s) hP (by omega) (by rw [top0]; exact hc)
    -- the frame
    let env1 : Env := fun k => s1.m (slotAddr p ((s.x 31).toNat - 16) k)
    have F1 : Frame p nl s1 env1 := by intro k hk; show s1.m (slotAddr p (s1.x 8).toNat k) = _; rw [h8]
    have O1 : FrameOK p nl s1 := ⟨by rw [h31, h8]; omega, hpn, by rw [h8]; omega⟩
    have m1 : ∀ a, a ≠ (s.x 31).toNat - 8 → a ≠ (s.x 31).toNat - 16 → s1.m a = s.m a := by
      intro a h1 h2; rw [hm1, upd_other _ _ h2, upd_other _ _ h1]
    have b1 : s1.b = s.b := (run_star hr1).b
    have I1 : IGp IG E0 p s1 := by
      refine ⟨hIG s s1 I0 (hx 28 (by decide) (by decide)) (hx 29 (by decide) (by decide)) b1 (fun a ha => ?_), ?_⟩
      · apply m1 <;> intro e <;> apply ha <;> have := R0.2.1 <;> omega
      · rw [h8]; omega
    have z1 : s1.x 0 = 0 := by rw [hx 0 (by decide) (by decide), z0]
    have R1 : HRel hb s1 H := HRel_stack R0 (hx 30 (by decide) (by decide)) (by rw [h31]; omega)
      (fun a _ h2 => m1 a (by omega) (by omega))
    have hS1 : Sb env1 (s1.x 31).toNat H = some (vs, H') := by
      rw [h31, ← hS]; apply hB.stable; intro k hk
      have hkp := hR k hk
      simp only [env1, argEnv, hkp, if_true]
      rw [slotAddr_param hkp, m1 _ (by omega) (by omega), ← ha k hkp]; congr 1; omega
    obtain ⟨s2, env2, r2, I2, z2, p2, l2, v2, e82, F2, ag2, R2, m2⟩ := hB.run s1 env1 H vs H' I1 z1 F1 O1 R1 hS1
    rw [h31] at p2 v2 m2
    -- slots are never at s0 / s0 + 8, and all lie below (s.x 31).toNat + 8p
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
    obtain ⟨s3, hr3, b3, p3, x83, hx3, hm3⟩ := epi_run s2 hE hD1 hD2
    have b2 : s2.b = s.b := r2.b.trans b1
    have pc3 : ((s2.m ((s2.x 8).toNat + 8)).toNat - s2.b) / 4 = ret := by
      rw [x82, show (s.x 31).toNat - 16 + 8 = (s.x 31).toNat - 8 by omega, s2ra, b2]
      have : (UInt64.ofNat (s.b + 4 * ret)).toNat = s.b + 4 * ret := by simp; omega
      rw [this]; omega
    rw [pc3] at hr3
    rw [x82, show (s.x 31).toNat - 16 + 8 * p + 16 = (s.x 31).toNat + 8 * p by omega] at hm3 p3
    have mo : ∀ a, (a + 8 * q < (s.x 31).toNat + 8 * p ∨ (s.x 31).toNat + 8 * p ≤ a) → s3.m a = s2.m a := by
      intro a ha; rw [hm3]; exact Mc_out _ _ _ q (by omega) q (Nat.le_refl _) a ha
    refine ⟨s3, (run_star hr1).trans (r2.trans (run_star hr3)), ?_, ?_, by rw [p3], l2, ?_, ?_, ?_, ?_⟩
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

def callS (pa : Nat) (SA : SemW) (Sd : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)) : SemW :=
  fun env sp H => (SA env sp H).bind fun r => Sd r.1 (sp - 8 * pa) r.2

/-- **CALL**: the pa argument words, then `jal ra f` into a def satisfying `DefX` -/
theorem callX {C : List J} {pc la p nl pa q f hb E0 : Nat} {IG : St → Prop} {RA WA : Nat → Prop} {SA : SemW}
    {Sd : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)} {off : Int}
    (hIG : IGOK hb E0 IG) (hA : EVHw C pc la p nl (IGp IG E0 p) hb RA WA pa SA)
    (hj : C[pc + la]? = some (.jal 1 off)) (hf : (((pc + la : Nat) : Int) + off).toNat = f)
    (hD : DefX C f pa q IG hb E0 Sd) (hE62 : E0 < 2 ^ 62)
    (hcb : ∀ s, IG s → s.b + 4 * (pc + la + 1) < 2 ^ 64) :
    EVHw C pc (la + 1) p nl (IGp IG E0 p) hb RA WA q (callS pa SA Sd) where
  stable := fun env env' sp H h => by
    simp only [callS]; rw [hA.stable env env' sp H h]
  run := fun s env H vs H' I0 z0 F0 O0 R0 hS => by
    simp only [callS, Option.bind_eq_some_iff] at hS
    obtain ⟨⟨u, H1⟩, hSA, hSd⟩ := hS
    obtain ⟨s1, env1, r1, I1, z1, p1, lu, v1, e81, F1, ag1, R1, m1⟩ := hA.run s env H u H1 I0 z0 F0 O0 R0 hSA
    obtain ⟨o1, o2, o3⟩ := O0
    have sp1 : 16 ≤ (s1.x 31).toNat := hrel_sp R1
    let sj := wr s1 1 (UInt64.ofNat (s1.b + 4 * (pc + la + 1)))
    have stj : step C (pc + la, s1) = some (f, sj) := by rw [s_jal hj, hf]
    have ej : sj = { s1 with x := upd s1.x 1 (UInt64.ofNat (s1.b + 4 * (pc + la + 1))) } := by simp [sj, wr]
    have jx : ∀ i, i ≠ 1 → sj.x i = s1.x i := by intro i hi; rw [ej]; simp [upd, hi]
    have jm : sj.m = s1.m := by rw [ej]
    have jb : sj.b = s1.b := by rw [ej]
    have b1 : s1.b = s.b := r1.b
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
    obtain ⟨s', st', I', z', p', l', v', e8', R', m'⟩ :=
      hD.run sj u H1 vs H' (pc + la + 1) Ij (by rw [jx 0 (by decide), z1]) Rj lu hargs htop hE62 hx1 hret hSd'
    rw [j31, show (s.x 31).toNat - 8 * pa + 8 * pa = (s.x 31).toNat by omega] at p' v' m'
    have x8 : s'.x 8 = s.x 8 := by rw [e8', jx 8 (by decide), e81]
    refine ⟨s', env1, ((r1.tail stj).trans st'), ⟨I', by rw [x8]; exact I0.2⟩, z', p', l', v', x8, ?_, ag1, R', ?_⟩
    · intro k hk
      show s'.m (slotAddr p (s'.x 8).toNat k) = env1 k
      have hk' := slotAddr_ge (T := (s.x 31).toNat) (by omega) o2 hk
      rw [x8, m' _ hk', jm, ← e81]; exact F1 k hk
    · intro a ha hW
      rw [m' a ha, jm]; exact m1 a ha hW

end Templates
