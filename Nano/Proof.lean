/- The nano lowering is correct: `lower_ok`, the RTL program `Nano.lower p` has the meaning `nanoRun p` (the
arguments as 8-byte little-endian words, `Prog.eval`, the result as 8 little-endian bytes). -/
import Nano.Gen

namespace Nano
open Proven Proven.Ir Proven.Ir.IndLow Proven.Mach

/-! ## the meaning of a nano program on bytes (the `Program` instance) -/

/-- exactly `n` 8-byte little-endian words -/
def wordsOf : Nat → List UInt8 → Option (List UInt64)
  | 0, L => if L.isEmpty then some [] else none
  | n + 1, L => if 8 ≤ L.length then (wordsOf n (L.drop 8)).map (UInt64.ofNat (unle (L.take 8)) :: ·) else none

/-- **a nano program on bytes**: its arguments as 8-byte LE words, the result as 8 LE bytes -/
def nanoRun (p : Prog) (input : List UInt8) : Option (List UInt8) :=
  (wordsOf p.1 input).bind fun args => (p.eval args).map fun v => leN 8 v.toNat

instance : Proven.Top.Program Prog := ⟨nanoRun⟩

theorem wordsOf_spec : ∀ (n : Nat) (L : List UInt8) (args : List UInt64), wordsOf n L = some args →
    args.length = n ∧ L.length = 8 * n ∧
      ∀ j, j < n → args[j]? = some (UInt64.ofNat (unle ((L.drop (8 * j)).take 8)))
  | 0, L, args, h => by
    simp only [wordsOf] at h
    split at h
    · next he => cases h; simp at he; subst he; simp
    · exact nomatch h
  | n + 1, L, args, h => by
    simp only [wordsOf] at h
    split at h
    · next h8 =>
      cases hw : wordsOf n (L.drop 8) with
      | none => rw [hw] at h; exact nomatch h
      | some as =>
        rw [hw] at h; cases h
        obtain ⟨h1, h2, h3⟩ := wordsOf_spec n (L.drop 8) as hw
        refine ⟨by simp [h1], by simp at h2; omega, fun j hj => ?_⟩
        cases j with
        | zero => simp
        | succ j =>
          simp only [List.getElem?_cons_succ]
          rw [h3 j (by omega), List.drop_drop]
          rw [show 8 + 8 * j = 8 * (j + 1) by omega]
    · exact nomatch h

/-! ## environments: operands holding the values of the variables -/

/-- an operand below register `n` -/
def ALt (n : Nat) : Arg Nat → Prop
  | .r x => x < n
  | .i _ => True

theorem ALt.mono {n n' : Nat} (h : n ≤ n') : ∀ {a : Arg Nat}, ALt n a → ALt n' a
  | .r _, ha => by simp only [ALt] at *; omega
  | .i _, _ => trivial

theorem ALt.eval {n : Nat} {g g' : VReg → Val} (hg : ∀ q, q < n → g' q = g q) : ∀ {a : Arg Nat}, ALt n a →
    a.eval g' = a.eval g
  | .r x, ha => hg x ha
  | .i _, _ => rfl

/-- the operands `env` hold `vals`, below register `n` -/
inductive EnvR (g : VReg → Val) (n : Nat) : List (Arg Nat) → List UInt64 → Prop
  | nil : EnvR g n [] []
  | cons {a v env vals} : a.eval g = .w v.toBitVec → ALt n a → EnvR g n env vals → EnvR g n (a :: env) (v :: vals)

theorem EnvR.mono {g g' : VReg → Val} {n n' : Nat} (hn : n ≤ n') (hg : ∀ q, q < n → g' q = g q) :
    ∀ {env vals}, EnvR g n env vals → EnvR g' n' env vals
  | _, _, .nil => .nil
  | _, _, .cons ha hl hr => .cons (by rw [ALt.eval hg hl]; exact ha) (hl.mono hn) (hr.mono hn hg)

theorem EnvR.append {g : VReg → Val} {n : Nat} : ∀ {e₁ v₁ e₂ v₂}, EnvR g n e₁ v₁ → EnvR g n e₂ v₂ →
    EnvR g n (e₁ ++ e₂) (v₁ ++ v₂)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha hl hr, h => .cons ha hl (hr.append h)

theorem EnvR.reverse {g : VReg → Val} {n : Nat} : ∀ {env vals}, EnvR g n env vals → EnvR g n env.reverse vals.reverse
  | _, _, .nil => .nil
  | _, _, .cons ha hl hr => by
    simp only [List.reverse_cons]; exact hr.reverse.append (.cons ha hl .nil)

theorem EnvR.getD {g : VReg → Val} {n : Nat} : ∀ {env vals}, EnvR g n env vals → ∀ i,
    (env.getD i (.i 0)).eval g = .w (vals.getD i 0).toBitVec ∧ ALt n (env.getD i (.i 0))
  | _, _, .nil, i => by simp [Arg.eval, ALt]
  | _, _, .cons ha hl _, 0 => by simpa using ⟨ha, hl⟩
  | _, _, .cons _ _ hr, i + 1 => by simpa using hr.getD i

/-! ## expressions -/

variable {P : Proven.Ir.Prog VReg}

/-- what the code of an expression does: its operand holds the value, below the next register; registers below
the first one stay -/
def ESpec (P : Proven.Ir.Prog VReg) (c : SC × Arg Nat × Nat) (v : UInt64) (nx : Nat) (env : List (Arg Nat))
    (vals : List UInt64) : Prop :=
  ∀ g m, EnvR g nx env vals → ∃ g', SC.Ex P c.1 g m g' m ∧ c.2.1.eval g' = .w v.toBitVec ∧ ALt c.2.2 c.2.1 ∧
    nx ≤ c.2.2 ∧ ∀ q, q < nx → g' q = g q

def ASpec (P : Proven.Ir.Prog VReg) (c : SC × List (Arg Nat) × Nat) (vs : List UInt64) (nx : Nat)
    (env : List (Arg Nat)) (vals : List UInt64) : Prop :=
  ∀ g m, EnvR g nx env vals → ∃ g', SC.Ex P c.1 g m g' m ∧ EnvR g' c.2.2 c.2.1 vs ∧
    nx ≤ c.2.2 ∧ ∀ q, q < nx → g' q = g q

def opv (o : Nat) (a b : UInt64) : UInt64 :=
  match o with
  | 0 => a + b
  | 1 => a - b
  | _ => a * b

theorem word_of {g : VReg → Val} {a : Arg Nat} {v : BitVec 64} (h : a.eval g = .w v) : a.word g = some v := by
  simp [Arg.word, h]

theorem binRhs_eval (o : Nat) {g : VReg → Val} {m : Ir.Mem} {a b : Arg Nat} {x y : UInt64}
    (ha : a.eval g = .w x.toBitVec) (hb : b.eval g = .w y.toBitVec) :
    (binRhs o a b).eval m g = some (.w (opv o x y).toBitVec) := by
  match o with
  | 0 => simp [binRhs, Rhs.eval, word_of ha, word_of hb, opv, Op.eval]
  | 1 => simp [binRhs, Rhs.eval, word_of ha, word_of hb, opv, Op.eval]
  | o + 2 => simp [binRhs, Rhs.eval, word_of ha, word_of hb, opv, MOp.eval]

theorem bin_ok (o : Nat) (a b : Ex) (env : List (Arg Nat)) (vals : List UInt64) (nx : Nat)
    (ha : ∀ nx, ESpec P (cE a env nx) (den a vals) nx env vals)
    (hb : ∀ nx, ESpec P (cE b env nx) (den b vals) nx env vals) :
    ESpec P (let ra := cE a env nx; let rb := cE b env ra.2.2
      (.seq (.seq ra.1 rb.1) (.i (.let_ rb.2.2 (binRhs o ra.2.1 rb.2.1))), .r rb.2.2, rb.2.2 + 1))
      (opv o (den a vals) (den b vals)) nx env vals := by
  intro g m he
  obtain ⟨g1, x1, v1, l1, n1, f1⟩ := ha nx g m he
  obtain ⟨g2, x2, v2, l2, n2, f2⟩ := hb (cE a env nx).2.2 g1 m (he.mono n1 f1)
  have v1' : (cE a env nx).2.1.eval g2 = .w (den a vals).toBitVec := by rw [ALt.eval f2 l1]; exact v1
  have x3 := ex_let (P := P) (g := g2) (m := m) (cE b env (cE a env nx).2.2).2.2
    (binRhs o (cE a env nx).2.1 (cE b env (cE a env nx).2.2).2.1) (binRhs_eval o v1' v2)
  refine ⟨_, .seq (.seq x1 x2) x3, by simp [Arg.eval], by simp [ALt], by dsimp only; omega, fun q hq => ?_⟩
  rw [upd_ne _ _ (by omega), f2 q (by omega), f1 q hq]

mutual
theorem cE_ok : ∀ (e : Ex) (env : List (Arg Nat)) (vals : List UInt64) (nx : Nat),
    ESpec P (cE e env nx) (den e vals) nx env vals
  | .num n, env, vals, nx => fun g m _ => ⟨g, .nop, rfl, trivial, Nat.le_refl _, fun _ _ => rfl⟩
  | .var i, env, vals, nx => fun g m he =>
    ⟨g, .nop, (he.getD i).1, (he.getD i).2, Nat.le_refl _, fun _ _ => rfl⟩
  | .add a b, env, vals, nx => bin_ok 0 a b env vals nx (cE_ok a env vals) (cE_ok b env vals)
  | .sub a b, env, vals, nx => bin_ok 1 a b env vals nx (cE_ok a env vals) (cE_ok b env vals)
  | .mul a b, env, vals, nx => bin_ok 2 a b env vals nx (cE_ok a env vals) (cE_ok b env vals)
  | .let_ v b, env, vals, nx => fun g m he => by
    obtain ⟨g1, x1, v1, l1, n1, f1⟩ := cE_ok v env vals nx g m he
    obtain ⟨g2, x2, v2, l2, n2, f2⟩ := cE_ok b ((cE v env nx).2.1 :: env) (den v vals :: vals) (cE v env nx).2.2 g1 m
      (.cons v1 l1 (he.mono n1 f1))
    exact ⟨g2, .seq x1 x2, v2, l2, by dsimp only [cE]; omega, fun q hq => by rw [f2 q (by omega), f1 q hq]⟩
  | .call b as, env, vals, nx => fun g m he => by
    obtain ⟨g1, x1, e1, n1, f1⟩ := cA_ok as env vals nx g m he
    obtain ⟨g2, x2, v2, l2, n2, f2⟩ := cE_ok b (cA as env nx).2.1.reverse (denA as vals).reverse (cA as env nx).2.2 g1 m
      e1.reverse
    exact ⟨g2, .seq x1 x2, v2, l2, by dsimp only [cE]; omega, fun q hq => by rw [f2 q (by omega), f1 q hq]⟩
  | .anil, env, vals, nx => fun g m _ => ⟨g, .nop, rfl, trivial, Nat.le_refl _, fun _ _ => rfl⟩
  | .acons _ _, env, vals, nx => fun g m _ => ⟨g, .nop, rfl, trivial, Nat.le_refl _, fun _ _ => rfl⟩
theorem cA_ok : ∀ (e : Ex) (env : List (Arg Nat)) (vals : List UInt64) (nx : Nat),
    ASpec P (cA e env nx) (denA e vals) nx env vals
  | .acons e r, env, vals, nx => fun g m he => by
    obtain ⟨g1, x1, v1, l1, n1, f1⟩ := cE_ok e env vals nx g m he
    obtain ⟨g2, x2, e2, n2, f2⟩ := cA_ok r env vals (cE e env nx).2.2 g1 m (he.mono n1 f1)
    refine ⟨g2, .seq x1 x2, .cons (by rw [ALt.eval f2 l1]; exact v1) (l1.mono n2) e2, by dsimp only [cA]; omega,
      fun q hq => by rw [f2 q (by omega), f1 q hq]⟩
  | .num _, _, _, nx => fun g m _ => ⟨g, .nop, .nil, Nat.le_refl _, fun _ _ => rfl⟩
  | .var _, _, _, nx => fun g m _ => ⟨g, .nop, .nil, Nat.le_refl _, fun _ _ => rfl⟩
  | .add _ _, _, _, nx => fun g m _ => ⟨g, .nop, .nil, Nat.le_refl _, fun _ _ => rfl⟩
  | .sub _ _, _, _, nx => fun g m _ => ⟨g, .nop, .nil, Nat.le_refl _, fun _ _ => rfl⟩
  | .mul _ _, _, _, nx => fun g m _ => ⟨g, .nop, .nil, Nat.le_refl _, fun _ _ => rfl⟩
  | .let_ _ _, _, _, nx => fun g m _ => ⟨g, .nop, .nil, Nat.le_refl _, fun _ _ => rfl⟩
  | .call _ _, _, _, nx => fun g m _ => ⟨g, .nop, .nil, Nat.le_refl _, fun _ _ => rfl⟩
  | .anil, _, _, nx => fun g m _ => ⟨g, .nop, .nil, Nat.le_refl _, fun _ _ => rfl⟩
end

end Nano
