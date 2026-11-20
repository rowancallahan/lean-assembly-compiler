/- Codegen templates beyond the expression leaves (Astra-11, Opus box): IF (value mode).  Fragments are specified by
the value contract `PV`: with n words of stack room the code at [pc, pc+len) pushes ONE word `V s`, keeps s0 (x8),
t5 (x30) and every cell at or above the old t6; `V` only depends on s0 and the cells at or above t6 (`stable`).
The IF layout is Gen's (g36 visit + g37 items 3/4/5): A; B; pop2 (ld t1,0(t6); ld t0,8(t6); t6 += 16);
beq/bltu t0,t1,+8; jal ELSE; T; jal END; ELSE: E; END. -/
import Nano.V2Self.Proof.Machine.Call

namespace Templates
open CallProbe

structure PV (C : List J) (pc len n : Nat) (V : St → UInt64) : Prop where
  run : ∀ s : St, (s.x 30).toNat + 8 * n ≤ (s.x 31).toNat → (s.x 31).toNat < 2 ^ 62 →
    ∃ s', Star C (pc, s) (pc + len, s') ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
      s'.m ((s.x 31).toNat - 8) = V s ∧ s'.x 8 = s.x 8 ∧ s'.x 30 = s.x 30 ∧
      ∀ a, (s.x 31).toNat ≤ a → s'.m a = s.m a
  stable : ∀ s s' : St, s'.x 8 = s.x 8 → (∀ a, (s.x 31).toNat ≤ a → s'.m a = s.m a) → V s' = V s

theorem At.sub {C pos l} (h : At C pos l) {i} (hi : i < l.length) {x} (hx : l[i]? = some x) : C[pos + i]? = some x := by
  rw [h.at i hi, hx]

/-- the IF head after both operands: pop2, `beq t0, t1, +2`, `jal 0 (lt+2)` -/
def ifHead (lt : Nat) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 16, .beq 5 6 2, .jal 0 ((lt : Int) + 2)]

/-- the IF head after both operands: pop2, `beq t0, t1, +2`, `jal 0 (lt+2)` -/
def ifHeadLt (lt : Nat) : List J := [.ld 6 31 0, .ld 5 31 8, .addi 31 31 16, .bltu 5 6 2, .jal 0 ((lt : Int) + 2)]

/-! ## frames and the environment contract (for LET) -/

/-- slot k of a def with p parameter words: params above s0 (`s0 + 16 + 8(p−1−k)`), locals below (`s0 − 8(k−p+1)`) -/
def slotOff (p k : Nat) : Int := if k < p then 8 * ((p - 1 - k : Nat) : Int) + 16 else -(8 * ((k - p + 1 : Nat) : Int))
def slotAddr (p S0 k : Nat) : Nat := ((S0 : Int) + slotOff p k).toNat

/-- the frame holds `env` in its `nl` slots -/
def Frame (p nl : Nat) (s : St) (env : Nat → UInt64) : Prop :=
  ∀ k, k < nl → s.m (slotAddr p (s.x 8).toNat k) = env k

/-- the frame sits between t6 and the caller's stack: locals above t6, s0 large enough -/
def FrameOK (p nl : Nat) (s : St) : Prop :=
  (s.x 31).toNat + 8 * (nl - p) ≤ (s.x 8).toNat ∧ p ≤ nl ∧ (s.x 8).toNat + 8 * p + 16 < 2 ^ 62

theorem slotAddr_ge {p nl S0 T k} (h : T + 8 * (nl - p) ≤ S0) (hp : p ≤ nl) (hk : k < nl) : T ≤ slotAddr p S0 k := by
  unfold slotAddr slotOff; split <;> omega

theorem slotAddr_inj {p nl S0 k k'} (h : 8 * (nl - p) ≤ S0) (hk : k < nl) (hk' : k' < nl)
    (e : slotAddr p S0 k = slotAddr p S0 k') : k = k' := by
  unfold slotAddr slotOff at e; split at e <;> split at e <;> omega

theorem slotAddr_lt {p nl S0 k} (h : 8 * (nl - p) ≤ S0) (hk : k < nl) : slotAddr p S0 k < S0 + 8 * p + 16 := by
  unfold slotAddr slotOff; split <;> omega

/-- the ENVIRONMENT contract: the fragment pushes `V env`, where `V` reads only the slots in `R`; it may write the frame
slots in `W` (its own lets) and nothing else at or above t6; s0 and t5 are kept; x0 = 0 and the invariant `Inv` (the
input / heap / input-register facts a leaf's value depends on) are kept -/
structure EV (C : List J) (pc len n p nl : Nat) (Inv : St → Prop) (R W : Nat → Prop) (V : (Nat → UInt64) → UInt64) : Prop where
  run : ∀ (s : St) (env : Nat → UInt64), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s →
    (s.x 30).toNat + 8 * n ≤ (s.x 31).toNat →
    ∃ s' env', Star C (pc, s) (pc + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 ∧
      s'.m ((s.x 31).toNat - 8) = V env ∧ s'.x 8 = s.x 8 ∧ s'.x 30 = s.x 30 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  stable : ∀ env env', (∀ k, R k → env k = env' k) → V env = V env'

/-- pop the top word into slot k (`g26`, w = 1) -/
def popSlot (p k : Nat) : List J := [.ld 5 31 0, .addi 31 31 8, .sd 5 8 (slotOff p k)]

/-- `Inv` reads only s0, x28, x29, t5 and memory outside the stack/frame block [t5, frame top) -/
def InvOK (p : Nat) (Inv : St → Prop) : Prop :=
  ∀ s s' : St, Inv s → s'.x 8 = s.x 8 → s'.x 28 = s.x 28 → s'.x 29 = s.x 29 → s'.x 30 = s.x 30 →
    (∀ a, ¬ ((s.x 30).toNat ≤ a ∧ a < (s.x 8).toNat + 8 * p + 16) → s'.m a = s.m a) → Inv s'

/-! ## popping w words into consecutive slots (`g26`: top → slot k0+w−1, …, deepest → slot k0) -/
def popN (p k0 : Nat) : Nat → List J
  | 0 => []
  | w + 1 => popSlot p (k0 + w) ++ popN p k0 w

theorem popN_len (p k0 : Nat) : ∀ w, (popN p k0 w).length = 3 * w
  | 0 => rfl
  | w + 1 => by simp [popN, popSlot, popN_len p k0 w]; omega

/-- one pop: the top word goes to slot k, t6 += 8 (t0 clobbered) -/
theorem popSlot_run {C : List J} {pc p k : Nat} (s : St) (hS : At C pc (popSlot p k))
    (hlt : (s.x 31).toNat + 8 < 2 ^ 64) :
    run C 3 (pc, s) = some (pc + 3, ⟨upd (upd s.x 5 (s.m (s.x 31).toNat)) 31 (UInt64.ofNat ((s.x 31).toNat + 8)),
      upd s.m (slotAddr p (s.x 8).toNat k) (s.m (s.x 31).toNat), s.b, s.wk⟩) := by
  have c0 := hS.at 0 (by simp [popSlot]); have c1 := hS.at 1 (by simp [popSlot]); have c2 := hS.at 2 (by simp [popSlot])
  simp [popSlot] at c0 c1 c2
  have ea0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have ea8 : ea (upd s.x 5 (s.m (s.x 31).toNat) 31) 8 = (s.x 31).toNat + 8 := by simp [ea, upd]; omega
  have eaK : ∀ v w, ea (upd (upd s.x 5 v) 31 w 8) (slotOff p k) = slotAddr p (s.x 8).toNat k := by
    intro v w; simp [ea, upd, slotAddr]
  simp [run, step, c0, c1, c2, wr, ea0, ea8, eaK, upd_other _ _ (show (5:Nat) ≠ 31 by decide), upd_same]

/-- **pop w words into slots k0 … k0+w−1** (word at t6 + 8i goes to slot k0 + w − 1 − i) -/
theorem popN_run {C : List J} {p k0 : Nat} : ∀ (w pc : Nat) (s : St), At C pc (popN p k0 w) →
    (s.x 31).toNat + 8 * w < 2 ^ 63 →
    (∀ j j', j < w → j' < w → slotAddr p (s.x 8).toNat (k0 + j) = slotAddr p (s.x 8).toNat (k0 + j') → j = j') →
    (∀ j i, j < w → i < w → slotAddr p (s.x 8).toNat (k0 + j) ≠ (s.x 31).toNat + 8 * i) →
    ∃ s', run C (3 * w) (pc, s) = some (pc + 3 * w, s') ∧ (s'.x 31).toNat = (s.x 31).toNat + 8 * w ∧
      s'.x 8 = s.x 8 ∧ (∀ r, r ≠ 5 → r ≠ 31 → s'.x r = s.x r) ∧ s'.b = s.b ∧
      (∀ j, j < w → s'.m (slotAddr p (s.x 8).toNat (k0 + j)) = s.m ((s.x 31).toNat + 8 * (w - 1 - j))) ∧
      ∀ a, (∀ j, j < w → a ≠ slotAddr p (s.x 8).toNat (k0 + j)) → s'.m a = s.m a
  | 0, pc, s, _, _, _, _ => ⟨s, by simp [run], by simp, rfl, fun _ _ _ => rfl, rfl, fun j h => absurd h (by omega),
      fun _ _ => rfl⟩
  | w + 1, pc, s, hC, hlt, hinj, hdis => by
    have hC' : At C pc (popSlot p (k0 + w) ++ popN p k0 w) := hC
    have A1 : At C pc (popSlot p (k0 + w)) := hC'.left
    have A2 : At C (pc + 3) (popN p k0 w) := by have := hC'.right; simpa [popSlot] using this
    have r1 := popSlot_run (k := k0 + w) s A1 (by omega)
    generalize hs1 : (⟨upd (upd s.x 5 (s.m (s.x 31).toNat)) 31 (UInt64.ofNat ((s.x 31).toNat + 8)),
      upd s.m (slotAddr p (s.x 8).toNat (k0 + w)) (s.m (s.x 31).toNat), s.b, s.wk⟩ : St) = s1 at r1
    have t1 : (s1.x 31).toNat = (s.x 31).toNat + 8 := by subst hs1; simp [upd]; omega
    have x81 : s1.x 8 = s.x 8 := by subst hs1; simp [upd]
    have m1 : ∀ a, s1.m a = if a = slotAddr p (s.x 8).toNat (k0 + w) then s.m (s.x 31).toNat else s.m a := by
      intro a; subst hs1; simp [upd]
    obtain ⟨s', r', p', e8', ex', eb', ms', mo'⟩ := popN_run w (pc + 3) s1 A2 (by rw [t1]; omega)
      (fun j j' hj hj' e => hinj j j' (by omega) (by omega) (by rw [x81] at e; exact e))
      (fun j i hj hi => by rw [x81, t1]; have := hdis j (i + 1) (by omega) (by omega); omega)
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show 3 * (w + 1) = 3 + 3 * w by omega, run_add r1, r']; congr 2; omega
    · rw [p', t1]; omega
    · rw [e8', x81]
    · intro r h5 h31; rw [ex' r h5 h31]; subst hs1; simp [upd, h5, h31]
    · rw [eb']; subst hs1; rfl
    · intro j hj
      rw [x81] at ms' mo'
      by_cases hjw : j = w
      · subst hjw
        rw [mo' _ (fun j' hj' e => by have := hinj j j' (by omega) (by omega) e; omega), m1, if_pos rfl]
        congr 1; omega
      · rw [ms' j (by omega), t1, m1, if_neg (by have := hdis w (w - j) (by omega) (by omega); omega)]
        congr 1; omega
    · intro a ha
      rw [x81] at mo'
      rw [mo' a (fun j hj => ha j (by omega)), m1, if_neg (ha w (by omega))]

/-! ## multi-word values (PAIR, LET of width w, CONTINUE's state) -/

/-- the w-word ENVIRONMENT contract: pushes `V env` (length w; component i at old t6 − 8(i+1)) -/
structure EVw (C : List J) (pc len n p nl : Nat) (Inv : St → Prop) (R W : Nat → Prop) (w : Nat)
    (V : (Nat → UInt64) → List UInt64) : Prop where
  vlen : ∀ env, (V env).length = w
  run : ∀ (s : St) (env : Nat → UInt64), Inv s → s.x 0 = 0 → Frame p nl s env → FrameOK p nl s →
    (s.x 30).toNat + 8 * n ≤ (s.x 31).toNat →
    ∃ s' env', Star C (pc, s) (pc + len, s') ∧ Inv s' ∧ s'.x 0 = 0 ∧ (s'.x 31).toNat = (s.x 31).toNat - 8 * w ∧
      (∀ i, i < w → s'.m ((s.x 31).toNat - 8 * (i + 1)) = (V env).getD i 0) ∧ s'.x 8 = s.x 8 ∧ s'.x 30 = s.x 30 ∧
      Frame p nl s' env' ∧ (∀ k, ¬ W k → env' k = env k) ∧
      ∀ a, (s.x 31).toNat ≤ a → (∀ k, k < nl → W k → a ≠ slotAddr p (s.x 8).toNat k) → s'.m a = s.m a
  stable : ∀ env env', (∀ k, R k → env k = env' k) → V env = V env'

theorem getD_app_l (a b : List UInt64) (i : Nat) (h : i < a.length) : (a ++ b).getD i 0 = a.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_app_r (a b : List UInt64) (i : Nat) (h : a.length ≤ i) : (a ++ b).getD i 0 = b.getD (i - a.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- slots k0, k0+1, … get the words of `vs` -/
def setSlots (env : Nat → UInt64) (k0 : Nat) (vs : List UInt64) : Nat → UInt64 :=
  fun k => if k0 ≤ k ∧ k < k0 + vs.length then vs.getD (k - k0) 0 else env k

end Templates
