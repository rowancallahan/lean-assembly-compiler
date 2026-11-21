/- Machine bridge (Opus box E): defs and calls, shared definitions.
* `IG` = the GLOBAL invariant (input registers / bytes, code-base bound …): reads only x28, x29, the code base and
  memory outside the work area [hb, E0) (`IGOK`); inside a def with p parameter words the contract invariant is
  `IGp IG E0 p` (also: the frame top s0 + 8p + 16 is at most E0), which is `InvOKH` (`invOKH_IGp`).
* semantics `defS`, `callS`, `argEnv`; helpers `Mc_out`, `slotAddr_param`.
The def contract and the run theorems are `DefXS` (EVSDefs.lean), `defXS` / `callXS` (EVSCall.lean). -/
import Nano.Run.EVXF
import Nano.Run.CallA
namespace Templates
open CallProbe

def IGOK (hb E0 : Nat) (IG : St → Prop) : Prop :=
  ∀ s s' : St, IG s → s'.x 28 = s.x 28 → s'.x 29 = s.x 29 → s'.b = s.b → s'.ly = s.ly →
    (∀ a, ¬ (hb ≤ a ∧ a < E0) → s'.m a = s.m a) → IG s'

def IGp (IG : St → Prop) (E0 p : Nat) : St → Prop := fun s => IG s ∧ (s.x 8).toNat + 8 * p + 16 ≤ E0

theorem invOKH_IGp {hb E0 : Nat} {IG : St → Prop} (h : IGOK hb E0 IG) (p : Nat) :
    InvOKH hb p (IGp IG E0 p) := by
  intro s s' ⟨I, hB⟩ e8 e28 e29 eb ew hm
  refine ⟨h s s' I e28 e29 eb ew (fun a ha => hm a ?_), by rw [e8]; exact hB⟩
  intro q; exact ha ⟨q.1, by have := q.2; omega⟩

/-- the epilogue's copy touches only [D − 8q, D) -/
theorem Mc_out (m : Nat → UInt64) (T D q : Nat) (hD : 8 * q ≤ D) :
    ∀ k, k ≤ q → ∀ a, (a + 8 * k < D ∨ D ≤ a) → Mc m T D q k a = m a
  | 0, _, _, _ => rfl
  | k + 1, hk, a, ha => by
    simp only [Mc]; rw [upd_other _ _ (by omega)]; exact Mc_out m T D q hD k (by omega) a (by omega)

/-- the parameter environment of a call (locals 0: a well-scoped body never reads them before writing) -/
def argEnv (p : Nat) (args : List UInt64) : Env := fun k => if k < p then args.getD k 0 else 0

/-- the def semantics: the prologue's room check, then the body in the new frame -/
def defS (p nl : Nat) (Sb : SemW) : List UInt64 → Nat → Hp → Option (List UInt64 × Hp) :=
  fun args sp H => if H.top + 16 + 8 * (nl - p) ≤ sp then Sb (argEnv p args) (sp - 16 - 8 * (nl - p)) H else none

theorem slotAddr_param {p S0 k : Nat} (hk : k < p) : slotAddr p S0 k = S0 + 16 + 8 * (p - 1 - k) := by
  unfold slotAddr slotOff; rw [if_pos hk]; omega

def callS (pa : Nat) (SA : SemW) (Sd : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)) : SemW :=
  fun env sp H => (SA env sp H).bind fun r => Sd r.1 (sp - 8 * pa) r.2

end Templates
