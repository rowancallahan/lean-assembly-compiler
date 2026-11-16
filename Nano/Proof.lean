/- The nano lowering is correct: `lower_ok`, the RTL program `Nano.lower p` has the meaning `nanoRun p` (the
arguments as 8-byte little-endian words, `Prog.eval`, the result as 8 little-endian bytes). -/
import Nano.GenIR

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
      (.seq (.seq ra.1 rb.1) (.i (.let_ nx (binRhs o ra.2.1 rb.2.1))), .r nx, nx + 1))
      (opv o (den a vals) (den b vals)) nx env vals := by
  intro g m he
  obtain ⟨g1, x1, v1, l1, n1, f1⟩ := ha nx g m he
  obtain ⟨g2, x2, v2, l2, n2, f2⟩ := hb (cE a env nx).2.2 g1 m (he.mono n1 f1)
  have v1' : (cE a env nx).2.1.eval g2 = .w (den a vals).toBitVec := by rw [ALt.eval f2 l1]; exact v1
  have x3 := ex_let (P := P) (g := g2) (m := m) nx
    (binRhs o (cE a env nx).2.1 (cE b env (cE a env nx).2.2).2.1) (binRhs_eval o v1' v2)
  refine ⟨_, .seq (.seq x1 x2) x3, by simp [Arg.eval], by simp [ALt], by dsimp only; omega, fun q hq => ?_⟩
  rw [upd_ne _ _ (show (q : Nat) ≠ nx by omega), f2 q (by omega), f1 q hq]

/-- the value of `b` moved into `nx` -/
theorem mv_ok {g g2 : VReg → Val} {m : Ir.Mem} {nx : Nat} {c : SC} (x : SC.Ex P c g m g2 m) {xb : Arg Nat}
    {v : UInt64} (hv : xb.eval g2 = .w v.toBitVec) (f : ∀ q, q < nx → g2 q = g q) :
    ∃ g', SC.Ex P (.seq c (.i (.let_ nx (.arg xb)))) g m g' m ∧ (Arg.r nx).eval g' = .w v.toBitVec ∧
      ALt (nx + 1) (.r nx) ∧ nx ≤ nx + 1 ∧ ∀ q, q < nx → g' q = g q :=
  ⟨_, .seq x (ex_let nx (.arg xb) (v := .w v.toBitVec) (by simp [Rhs.eval, hv])), by simp [Arg.eval],
    by simp [ALt], by omega, fun q hq => by rw [upd_ne _ _ (show (q : Nat) ≠ nx by omega), f q hq]⟩

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
    exact mv_ok (.seq x1 x2) v2 fun q hq => by rw [f2 q (by omega), f1 q hq]
  | .call b as, env, vals, nx => fun g m he => by
    obtain ⟨g1, x1, e1, n1, f1⟩ := cA_ok as env vals nx g m he
    obtain ⟨g2, x2, v2, l2, n2, f2⟩ := cE_ok b (cA as env nx).2.1.reverse (denA as vals).reverse (cA as env nx).2.2 g1 m
      e1.reverse
    exact mv_ok (.seq x1 x2) v2 fun q hq => by rw [f2 q (by omega), f1 q hq]
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

namespace Nano
open Proven Proven.Ir Proven.Ir.IndLow Proven.Mach

variable {P : Proven.Ir.Prog VReg}

/-! ## the parameters -/

theorem ofNat_bv (x : Nat) : (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := rfl

/-- **the parameters** are loaded into `10 + j` -/
theorem ldArgs_ok {n : Nat} (input : List UInt8) (args : List UInt64) (hw : wordsOf n input = some args)
    (hI : input.length ≤ 2 ^ 20) : ∀ k, k ≤ n → ∀ g : VReg → Val, g 0 = .p 0 0 →
    ∃ g', SC.Ex P (ldArgs k) g (Ir.Mem.init input) g' (Ir.Mem.init input) ∧
      (∀ j, j < k → g' (10 + j) = .w (args.getD j 0).toBitVec) ∧
      (∀ q, q < 10 → q ≠ 3 → q ≠ 5 → q ≠ 6 → g' q = g q)
  | 0, _, g, _ => ⟨g, .nop, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl⟩
  | k + 1, hk, g, h0 => by
    obtain ⟨hal, hil, h3⟩ := wordsOf_spec _ _ _ hw
    obtain ⟨g1, x1, r1, f1⟩ := ldArgs_ok input args hw hI k (by omega) g h0
    have x2 := ex_setK (P := P) g1 (Ir.Mem.init input) 3 (BitVec.ofNat 64 (8 * k))
    generalize hL : (input.drop (8 * k)).take 8 = L
    have hLl : L.length = 8 := by rw [← hL]; simp; omega
    obtain ⟨g3, x3, v3, f3⟩ := rd8_ok (P := P) (inp := 0) (cur := 3) (d := 10 + k) (t1 := 5) (t2 := 6)
      (show (10 + k : Nat) ≠ 5 by omega) (show (10 + k : Nat) ≠ 6 by omega) (by decide) (by decide) (by decide)
      (by decide) (by decide) (show (0 : Nat) ≠ 10 + k by omega) (show (3 : Nat) ≠ 10 + k by omega)
      (m := Ir.Mem.init input) (c := 8 * k) L hLl
      (fun i hi => by
        rw [← List.getElem?_eq_getElem, ← hL]
        simp [Ir.Mem.init, List.getElem?_drop, hi])
      (by omega) (g := upd g1 3 (.w (BitVec.ofNat 64 (8 * k))))
      (by rw [upd_ne _ _ (by decide), f1 0 (by decide) (by decide) (by decide) (by decide), h0]) (upd_same _ _ _)
    refine ⟨g3, .seq x1 (.seq x2 x3), fun j hj => ?_, fun q hq a b c => ?_⟩
    · by_cases hjk : j = k
      · subst hjk
        rw [v3, List.getD_eq_getElem?_getD, h3 j (by omega), hL]; rfl
      · rw [f3 _ (show (10 + j : Nat) ≠ 10 + k by omega) (show (10 + j : Nat) ≠ 5 by omega)
          (show (10 + j : Nat) ≠ 6 by omega), upd_ne _ _ (show (10 + j : Nat) ≠ 3 by omega), r1 j (by omega)]
    · rw [f3 _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le hq (Nat.le_add_right 10 k))) b c, upd_ne _ _ a, f1 q hq a b c]

/-- the parameter environment -/
theorem argEnv_ok {n : Nat} {g : VReg → Val} {args : List UInt64} (hl : args.length = n)
    (hr : ∀ j, j < n → g (10 + j) = .w (args.getD j 0).toBitVec) : EnvR g (10 + n) (argEnv n) args.reverse := by
  have : ∀ k, k ≤ n → EnvR g (10 + n) ((List.range k).map fun j => Arg.r (10 + j)) (args.take k) := by
    intro k
    induction k with
    | zero => intro _; exact .nil
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.take_add_one, List.getElem?_eq_getElem (by omega)]
      refine (ih (by omega)).append (.cons ?_ (by simp [ALt]; omega) .nil)
      show g (10 + k) = _
      rw [hr k (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  have h := (this n (Nat.le_refl _)).reverse
  rw [← hl, List.take_length, hl] at h
  exact h

/-! ## the program -/

theorem mapM_some' (L : List UInt8) : (L.map some).mapM id = some L := mapM_some L

/-- **the lowering is correct**: on every input of the program, the RTL program's meaning is the program's output -/
theorem lower_ok (p : Prog) (input out : List UInt8) (h : nanoRun p input = some out) (hI : input.length ≤ 2 ^ 20) :
    (lower p).meaning input = some out := by
  unfold nanoRun at h
  cases hw : wordsOf p.1 input with
  | none => rw [hw] at h; exact nomatch h
  | some args =>
  rw [hw] at h
  obtain ⟨hal, hil, h3⟩ := wordsOf_spec _ _ _ hw
  have hout : out = leN 8 (den p.2 args.reverse).toNat := by
    simp [Prog.eval, hal] at h; exact h.symm
  subst hout
  generalize hP : lower p = P
  have hP0 : P.funcs[0]? = some (mkFunc [0, 1, 2] [0, 1, 2] 1 [(0, mainTC p)]) := by rw [← hP]; rfl
  have hmain : P.main = 0 := by rw [← hP]; rfl
  generalize hF : mkFunc [0, 1, 2] [0, 1, 2] 1 [(0, mainTC p)] = F at hP0
  obtain ⟨nl', okm⟩ := mkFunc_region (params := [0, 1, 2]) (ps := [0, 1, 2]) (nl := 1)
    (rs := [(0, mainTC p)]) (by simp) (by simp) 0 (by simp)
  rw [hF] at okm
  simp only [List.getElem_cons_zero, if_true] at okm
  generalize hg0 : setMany (fun _ => Val.w 0) [0, 1, 2] [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0] = g0
  have g00 : g0 0 = .p 0 0 := by rw [← hg0]; simp [setMany, upd]
  have g02 : g0 2 = .p 1 0 := by rw [← hg0]; simp [setMany, upd]
  obtain ⟨g1, x1, r1, f1⟩ := ldArgs_ok (P := P) input args hw hI p.1 (Nat.le_refl _) g0 g00
  obtain ⟨g2, x2, v2, -, n2, f2⟩ := cE_ok (P := P) p.2 (argEnv p.1) args.reverse (10 + p.1) g1 (Ir.Mem.init input)
    (argEnv_ok hal r1)
  generalize hy : (den p.2 args.reverse) = y at v2
  have x3 := ex_let (P := P) (g := g2) (m := Ir.Mem.init input) 7 (.arg (cE p.2 (argEnv p.1) (10 + p.1)).2.1)
    (v := .w y.toBitVec) (by simp [Rhs.eval, v2])
  have g32 : upd g2 7 (.w y.toBitVec) 2 = .p 1 0 := by
    rw [upd_ne _ _ (by decide), f2 2 (by omega), f1 2 (by decide) (by decide) (by decide) (by decide), g02]
  obtain ⟨g4, x4⟩ := wout_loop (P := P) y.toBitVec 8 0 (by omega) (upd g2 7 (.w y.toBitVec)) (Ir.Mem.init input)
    (upd_same _ _ _) g32 (by simp [Ir.Mem.init])
  generalize hmF : ({ Ir.Mem.init input with out := ((leN 8 y.toBitVec.toNat).take (0 + 8)).map some } : Ir.Mem) = mF
    at x4
  have oF : mF.out = (leN 8 y.toNat).map some := by
    rw [← hmF]; simp only [Nat.zero_add]; rw [List.take_of_length_le (by simp [leN_length])]; rfl
  -- the run
  have xM : TC.Ex P F (mainTC p) g0 (Ir.Mem.init input) (.ret [] mF) := by
    simp only [mainTC, SC.seqs]
    exact .seq (.seq x1 (.seq x2 (.seq x3 x4))) .ret
  obtain ⟨l', pc', g', B, rvs, hR, hB, hk, ht, hv⟩ := flatT_ok hP0 _ xM _ okm
  have hFe : F.entry = 0 := by rw [← hF]; rfl
  have hFp : F.params = [0, 1, 2] := by rw [← hF]; rfl
  have hinit : init P input = ⟨[⟨0, 0, 0, g0, []⟩], Ir.Mem.init input, []⟩ := by
    unfold init; rw [hmain, hP0]; dsimp only; rw [hFe, hFp, hg0]
  obtain ⟨ev', hst⟩ := hR [] [] []
  have hdone : step P ⟨[⟨0, l', pc', g', []⟩], mF, ev'⟩ = .done ⟨rvs.map (Arg.eval g'), mF, ev'⟩ := by
    unfold step; simp only [hP0, hB, hk, ht, termStep]
  obtain ⟨n, hn⟩ := Star.run hst hdone
  have hres := Prog.result_eq (P := P) (input := input) ⟨n, by rw [hinit]; exact hn⟩
  show (P.result input).bind (fun r => r.mem.output) = _
  rw [hres]
  simp only [Option.bind_some, Ir.Mem.output, oF, mapM_some]

end Nano
