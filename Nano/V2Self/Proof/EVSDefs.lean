/- Safe retrofit (EVS), shared definitions (Opus box E).  The Safe twins of the contracts EVH / EVHw / EVHt / DefX:
the same statements with `SimW.SStarX KL C` runs, plus
  * `Lay KL hb E0 p s` — the per-state layout: work region [KL.lo, KL.hi) ⊇ [hb, E0) (heap … stack … frames),
    code base = KL.base, this frame's top s0 + 8p + 16 ≤ E0, t6 and s0 8-aligned.  Contracts preserve it (s0 and the
    code base are kept, t6 moves by 8w), so it is a premise of every run and needs no conclusion;
  * `HAl H` — heap image cells are 8-aligned (premise and conclusion), so heap cells read/written are work cells.
Every stack / frame / heap cell a template touches lies in [hb, E0) and is aligned, hence `wok` (`Lay.wok`).
Input bytes (RD's lbu) are work cells by the invariant: `InpW KL Inv`. -/
import Nano.V2Self.Proof.EVXC
import Nano.V2Self.Proof.EVXL
import Nano.V2Self.Proof.EVXT
import Nano.V2Self.Proof.EVXP
import Nano.V2Self.Proof.SafeRun
import Nano.V2Self.Proof.SimX
namespace Templates
open CallProbe SimW

structure Lay (KL : LayW) (hb E0 p : Nat) (s : St) : Prop where
  lo : KL.lo ≤ hb
  hi : E0 ≤ KL.hi
  base : s.b = KL.base
  top : (s.x 8).toNat + 8 * p + 16 ≤ E0
  a31 : (s.x 31).toNat % 8 = 0
  a8 : (s.x 8).toNat % 8 = 0

/-- heap image cells are aligned -/
def HAl (H : Hp) : Prop := ∀ a v, H.m a = some v → a % 8 = 0

/-- the input bytes' aligned cells are work cells (carried by the invariant) -/
def InpW (KL : LayW) (Inv : St → Prop) : Prop :=
  ∀ s, Inv s → ∀ i, i < (s.x 29).toNat → wok KL ((s.x 28).toNat + i - ((s.x 28).toNat + i) % 8)

theorem Lay.wok {KL : LayW} {hb E0 p : Nat} {s : St} (h : Lay KL hb E0 p s) {a : Nat} (h1 : hb ≤ a) (h2 : a + 8 ≤ E0)
    (h3 : a % 8 = 0) : wok KL a :=
  ⟨by have := h.lo; omega, by have := h.hi; omega, h3⟩

/-- the layout after a fragment: same s0 and code base, t6 moved by 8·w -/
theorem Lay.post {KL : LayW} {hb E0 p : Nat} {s s' : St} (h : Lay KL hb E0 p s) (e8 : s'.x 8 = s.x 8) (eb : s'.b = s.b)
    {w : Nat} (e31 : (s'.x 31).toNat = (s.x 31).toNat - 8 * w) (hw : 8 * w ≤ (s.x 31).toNat) :
    Lay KL hb E0 p s' where
  lo := h.lo
  hi := h.hi
  base := by rw [eb, h.base]
  top := by rw [e8]; exact h.top
  a31 := by rw [e31]; have := h.a31; omega
  a8 := by rw [e8]; exact h.a8

theorem Lay.post' {KL : LayW} {hb E0 p : Nat} {s s' : St} (h : Lay KL hb E0 p s) (e8 : s'.x 8 = s.x 8) (eb : s'.b = s.b)
    (e31 : (s'.x 31).toNat = (s.x 31).toNat) : Lay KL hb E0 p s' :=
  h.post (w := 0) e8 eb (by rw [e31]; omega) (by omega)

/-- **EVHw, safe**: as `EVHw` with a SafeX run; premises `Lay`, `HAl H`; conclusion `HAl H'` -/
structure EVHwS (KL : LayW) (C : List J) (pc len p nl : Nat) (Inv : St → Prop) (hb E0 : Nat) (R W : Nat → Prop)
    (w : Nat) (S : SemW) : Prop where
  run : ∀ (s : St) (env : Env) (H : Hp) (vs : List UInt64) (H' : Hp), Inv s → s.x 0 = 0 → Frame p nl s env →
    FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → HAl H → S env (s.x 31).toNat H = some (vs, H') →
    ∃ s' env', SStarX KL C (pc, s) (pc + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧
      (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
      vs.length = w ∧ (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧ HRel hb s' H' ∧ HAl H' ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  stable : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H

/-- **EVH, safe** (one word) -/
structure EVHS (KL : LayW) (C : List J) (pc len p nl : Nat) (Inv : St → Prop) (hb E0 : Nat) (R W : Nat → Prop)
    (S : Env → Nat → Hp → Option (UInt64 × Hp)) : Prop where
  run : ∀ (s : St) (env : Env) (H : Hp) (v : UInt64) (H' : Hp), Inv s → s.x 0 = 0 → Frame p nl s env →
    FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → HAl H → S env (s.x 31).toNat H = some (v, H') →
    ∃ s' env', SStarX KL C (pc, s) (pc + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
      s'.m ((s.x 31).toNat - 8) = v ∧ s'.x 8 = s.x 8 ∧ Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧
      HRel hb s' H' ∧ HAl H' ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  stable : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H

/-- **EVHt, safe** (tail mode: exit to X, or CONTINUE to Hd) -/
structure EVHtS (KL : LayW) (C : List J) (pc p nl : Nat) (Inv : St → Prop) (hb E0 : Nat) (R W : Nat → Prop)
    (w X Hd : Nat) (S : SemT) : Prop where
  exit : ∀ (s : St) (env : Env) (H : Hp) (vs : List UInt64) (H' : Hp), Inv s → s.x 0 = 0 → Frame p nl s env →
    FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → HAl H → S env (s.x 31).toNat H = some (.inl vs, H') →
    ∃ s' env', SStarX KL C (pc, s) (X, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
      vs.length = w ∧ (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧ HRel hb s' H' ∧ HAl H' ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  cont : ∀ (s : St) (env : Env) (H : Hp) (st : List UInt64) (H' : Hp), Inv s → s.x 0 = 0 → Frame p nl s env →
    FrameOK p nl s → HRel hb s H → Lay KL hb E0 p s → HAl H → S env (s.x 31).toNat H = some (.inr st, H') →
    ∃ s' env', SStarX KL C (pc, s) (Hd, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat ∧
      st.length = p - 1 ∧ s'.x 8 = s.x 8 ∧ Frame p nl s' (setW env' 1 (p - 1) st) ∧ (∀ k, ¬ W k → env' k = env k) ∧
      HRel hb s' H' ∧ HAl H' ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → (W k ∨ (1 ≤ k ∧ k < p)) → a ≠ slotAddr p (s.x 8).toNat k) →
        s'.m a = s.m a
  stable : ∀ env env' sp H, (∀ k, R k → env k = env' k) → S env sp H = S env' sp H

/-- **DefX, safe**: at the call (t6 = args top, ra = return word), the work region holds [hb, E0), the code base is
KL.base, t6 is aligned; ra is base + 4·ret (so the epilogue's `jalr` is safe) -/
structure DefXS (KL : LayW) (C : List J) (f p q : Nat) (IG : St → Prop) (hb E0 : Nat)
    (Sd : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)) : Prop where
  run : ∀ (s : St) (args : List UInt64) (H : Hp) (vs : List UInt64) (H' : Hp) (ret : Nat), IG s → s.x 0 = 0 →
    HRel hb s H → args.length = p → (∀ i, i < p → s.m ((s.x 31).toNat + 8 * (p - 1 - i)) = args.getD i 0) →
    (s.x 31).toNat + 8 * p ≤ E0 → E0 < 2 ^ 62 → s.x 1 = UInt64.ofNat (s.b + 4 * ret) → s.b + 4 * ret < 2 ^ 64 →
    KL.lo ≤ hb → E0 ≤ KL.hi → s.b = KL.base → (s.x 31).toNat % 8 = 0 → HAl H →
    Sd args (s.x 31).toNat H = some (vs, H') →
    ∃ s', SStarX KL C (f, s) (ret, s') ∧ IG s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat + 8 * p - 8 * q ∧
      vs.length = q ∧ (∀ i, i < q → s'.m ((s.x 31).toNat + 8 * p - 8 * (i + 1)) = vs.getD i 0) ∧ s'.x 8 = s.x 8 ∧
      HRel hb s' H' ∧ HAl H' ∧ ∀ a, (s.x 31).toNat + 8 * p ≤ a → s'.m a = s.m a

/-! ## forgetting safety -/

theorem _root_.SimW.SStarX.star {KL : LayW} {C : List J} {a b : Nat × St} (h : SStarX KL C a b) : Star C a b := by
  induction h with
  | refl => exact .refl _
  | head _ st _ ih => exact (Star.one st).trans ih

end Templates
