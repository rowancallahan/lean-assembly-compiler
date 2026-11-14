/- Instruction selection: `SExp` (and through it `Exp`) to IR code over VIRTUAL registers (`Nat`):
variable `i` is virtual register `i` (`< 8`), temporary `k` is `32 + k`.

The selection does, at the tree level: operands in place (a variable or constant is used directly, never
copied into a temporary), results written straight to their destination, constants as immediate operands,
comparison/branch fusion (`tst`: a comparison used as a condition becomes the branch condition, no 0/1 value),
and `ite` as a conditional assignment (a forward branch over the assignment) instead of a mask sequence.

`gen e = (into, tst)`: `into d k` is code for `d := e` using temporaries `≥ k`; `tst k` is code and a test
equivalent to `e ≠ 0`. -/
import Compiler.Opt.IR
import Spec.ArrCode

namespace Proven.Mach.Sel
open IR

/-- selection's expressions: a variable is either register-resident (`var i`, virtual register `i < 32`)
or slot-resident (`slot j`, frame slot `j`) -/
inductive SExp where
  | var (i : Fin 32)
  | slot (j : Nat)
  | const (c : BitVec 64)
  | bin (op : Op) (a b : SExp)
  | ite (c a b : SExp)

def SExp.denote (env : Fin 32 → BitVec 64) (sv : Nat → BitVec 64) : SExp → BitVec 64
  | .var i => env i
  | .slot j => sv j
  | .const c => c
  | .bin op a b => op.eval (a.denote env sv) (b.denote env sv)
  | .ite c a b => if c.denote env sv = 0 then b.denote env sv else a.denote env sv

/-- temporary `k` -/
def tk (k : Nat) : Nat := 32 + k

def leaf : SExp → Option (Arg Nat)
  | .var i => some (.r i.val)
  | .const c => some (.i c)
  | _ => none

def cmpOf : Op → Option Cond
  | .ult => some .ltu
  | .slt => some .lt
  | .eq => some .eq
  | _ => none

/-- `e` reads virtual register `x` -/
def uses : SExp → Nat → Bool
  | .var i, x => decide (i.val = x)
  | .const _, _ => false
  | .slot _, _ => false
  | .bin _ a b, x => uses a x || uses b x
  | .ite c a b, x => uses c x || uses a x || uses b x

/-- `e` reads slot `j` -/
def usesS : SExp → Nat → Bool
  | .slot i, j => decide (i = j)
  | .var _, _ => false
  | .const _, _ => false
  | .bin _ a b, x => usesS a x || usesS b x
  | .ite c a b, x => usesS c x || usesS a x || usesS b x

def argUses : Arg Nat → Nat → Bool
  | .r y, x => decide (y = x)
  | .i _, _ => false

def tstUses (t : Tst Nat) (x : Nat) : Bool := argUses t.a x || argUses t.b x

def isVar : SExp → Nat → Bool
  | .var i, x => decide (i.val = x)
  | _, _ => false

/-- an operand: a leaf in place, otherwise computed into temporary `k` by `code`;
returns (code, operand, next free temporary) -/
def opnd (e : SExp) (k : Nat) (code : Code Nat) : Code Nat × Arg Nat × Nat :=
  match leaf e with
  | some a => (.skip, a, k)
  | none => (code, .r (tk k), k + 1)

def ops2 (a b : SExp) (ia ib : Nat → Nat → Code Nat) (k : Nat) : Code Nat × Arg Nat × Arg Nat × Nat :=
  ((opnd a k (ia (tk k) k)).1.seq (opnd b (opnd a k (ia (tk k) k)).2.2
      (ib (tk (opnd a k (ia (tk k) k)).2.2) (opnd a k (ia (tk k) k)).2.2)).1,
   (opnd a k (ia (tk k) k)).2.1,
   (opnd b (opnd a k (ia (tk k) k)).2.2 (ib (tk (opnd a k (ia (tk k) k)).2.2) (opnd a k (ia (tk k) k)).2.2)).2.1,
   (opnd b (opnd a k (ia (tk k) k)).2.2 (ib (tk (opnd a k (ia (tk k) k)).2.2) (opnd a k (ia (tk k) k)).2.2)).2.2)

/-- `d := if T then a else b` -/
def iteCode (T : Code Nat × Tst Nat × Nat) (a b : SExp) (ia ib : Nat → Nat → Code Nat) (d : Nat) : Code Nat :=
  if isVar a d = true then .seq T.1 (.when T.2.1.neg (ib d T.2.2))
  else if isVar b d = true then .seq T.1 (.when T.2.1 (ia d T.2.2))
  else if (tstUses T.2.1 d || uses a d) = false then .seq T.1 (.seq (ib d T.2.2) (.when T.2.1 (ia d T.2.2)))
  else .seq T.1 (.seq (ib (tk T.2.2) (T.2.2 + 1)) (.seq (.when T.2.1 (ia (tk T.2.2) (T.2.2 + 1)))
    (.ins (.set d (.r (tk T.2.2))))))

/-- a value in temporary `k` as a test -/
def tstOf (c : Code Nat) (k : Nat) : Code Nat × Tst Nat × Nat := (c, ⟨.ne, .r (tk k), .i 0⟩, k + 1)

def gen : SExp → (Nat → Nat → Code Nat) × (Nat → Code Nat × Tst Nat × Nat)
  | .var i => (fun d _ => if i.val = d then .skip else .ins (.set d (.r i.val)),
      fun k => (.skip, ⟨.ne, .r i.val, .i 0⟩, k))
  | .slot j => (fun d _ => .ins (.ldS d j), fun k => tstOf (.ins (.ldS (tk k) j)) k)
  | .const c => (fun d _ => .ins (.set d (.i c)), fun k => (.skip, ⟨.ne, .i c, .i 0⟩, k))
  | .bin op a b =>
      (fun d k => (ops2 a b (gen a).1 (gen b).1 k).1.seq
          (.ins (.bin op d (ops2 a b (gen a).1 (gen b).1 k).2.1 (ops2 a b (gen a).1 (gen b).1 k).2.2.1)),
       fun k => match cmpOf op with
        | some cnd => ((ops2 a b (gen a).1 (gen b).1 k).1,
            ⟨cnd, (ops2 a b (gen a).1 (gen b).1 k).2.1, (ops2 a b (gen a).1 (gen b).1 k).2.2.1⟩,
            (ops2 a b (gen a).1 (gen b).1 k).2.2.2)
        | none => tstOf ((ops2 a b (gen a).1 (gen b).1 k).1.seq
            (.ins (.bin op (tk k) (ops2 a b (gen a).1 (gen b).1 k).2.1 (ops2 a b (gen a).1 (gen b).1 k).2.2.1))) k)
  | .ite c a b =>
      (fun d k => iteCode ((gen c).2 k) a b (gen a).1 (gen b).1 d,
       fun k => tstOf (iteCode ((gen c).2 k) a b (gen a).1 (gen b).1 (tk k)) k)

/-- code for `d := e`, temporaries `≥ k` -/
def into (e : SExp) (d : Nat) (k : Nat) : Code Nat := (gen e).1 d k
/-- code and test for `e ≠ 0` -/
def tst (e : SExp) (k : Nat) : Code Nat × Tst Nat × Nat := (gen e).2 k

/-- `e` as a short-circuit conjunction `c ≠ 0 ∧ a ≠ 0` -/
def cond2 : SExp → Option (SExp × SExp)
  | .ite c a (.const z) => if z = 0 then some (c, a) else none
  | _ => none

theorem cond2_eq : ∀ {e c a : SExp}, cond2 e = some (c, a) → e = .ite c a (.const 0)
  | .ite c' a' (.const z), c, a, h => by
    simp only [cond2] at h
    by_cases hz : z = 0
    · rw [if_pos hz] at h; cases h; rw [hz]
    · rw [if_neg hz] at h; exact nomatch h
  | .ite _ _ (.var _), _, _, h => nomatch h
  | .ite _ _ (.slot _), _, _, h => nomatch h
  | .ite _ _ (.bin _ _ _), _, _, h => nomatch h
  | .ite _ _ (.ite _ _ _), _, _, h => nomatch h
  | .var _, _, _, h => nomatch h
  | .slot _, _, _, h => nomatch h
  | .const _, _, _, h => nomatch h
  | .bin _ _ _, _, _, h => nomatch h

/-- loop code for `while e do body` -/
def loopCode (e : SExp) (body : Code Nat) : Code Nat :=
  match cond2 e with
  | some (c, a) => .loop2 (tst c 0).1 (tst c 0).2.1 (tst a 0).1 (tst a 0).2.1 body
  | none => .loop (tst e 0).1 (tst e 0).2.1 body

/-! ## Correctness -/

variable (ram : Nat → Prop) (fp : Nat) (env : Fin 32 → BitVec 64) (sv : Nat → BitVec 64)

/-- slot `j` holds `sv j` (and may be read) -/
def Slot (m : Mem) (j : Nat) : Prop :=
  fp % 8 = 0 ∧ (∀ i, i < 8 → ram (fp + 8 * (j + 1) + i)) ∧ bytes m (fp + 8 * (j + 1)) 8 = (le8 (sv j)).map some

/-- the registers `e` reads hold the environment -/
def Agree (e : SExp) (σ : St Nat) : Prop :=
  (∀ i : Fin 32, uses e i.val = true → σ.reg i.val = env i) ∧ ∀ j, usesS e j = true → Slot ram fp sv σ.mem j

/-- memory and registers below `n` unchanged -/
def Frame (n : Nat) (σ σ' : St Nat) : Prop := σ'.mem = σ.mem ∧ ∀ x, x < n → σ'.reg x = σ.reg x

/-- `c` sets `d` to `v`, changing otherwise only temporaries `≥ k` -/
def IntoSpec (c : Code Nat) (d : Nat) (k : Nat) (σ : St Nat) (v : BitVec 64) : Prop :=
  ∃ σ', Exec ram fp c σ σ' ∧ σ'.reg d = v ∧ σ'.mem = σ.mem ∧ ∀ x, x ≠ d → x < 32 + k → σ'.reg x = σ.reg x

def argBelow (a : Arg Nat) (n : Nat) : Prop := ∀ x, argUses a x = true → x < n
def tstBelow (t : Tst Nat) (n : Nat) : Prop := ∀ x, tstUses t x = true → x < n

/-- `T` tests `v ≠ 0`, changing only temporaries `≥ k`; its operands live below its next free temporary -/
def TstSpec (T : Code Nat × Tst Nat × Nat) (k : Nat) (σ : St Nat) (v : BitVec 64) : Prop :=
  ∃ σ', Exec ram fp T.1 σ σ' ∧ T.2.1.eval σ'.reg = !decide (v = 0) ∧ Frame (32 + k) σ σ' ∧
    tstBelow T.2.1 (32 + T.2.2) ∧ k ≤ T.2.2

variable {ram fp env sv}

theorem Frame.refl (n : Nat) (σ : St Nat) : Frame n σ σ := ⟨rfl, fun _ _ => rfl⟩

theorem Frame.trans {n m : Nat} {σ₁ σ₂ σ₃ : St Nat} (h₁ : Frame n σ₁ σ₂) (h₂ : Frame m σ₂ σ₃) (hnm : n ≤ m) :
    Frame n σ₁ σ₃ := ⟨h₂.1.trans h₁.1, fun x hx => (h₂.2 x (by omega)).trans (h₁.2 x hx)⟩

theorem Agree.frame {e : SExp} {σ σ' : St Nat} {n : Nat} (h : Agree ram fp env sv e σ) (f : Frame (32 + n) σ σ') :
    Agree ram fp env sv e σ' := ⟨fun i hi => (f.2 i.val (by omega)).trans (h.1 i hi), fun j hj => by rw [f.1]; exact h.2 j hj⟩

theorem or_false2 {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

theorem argEval_congr {a : Arg Nat} {σ σ' : Regs Nat} (h : ∀ x, argUses a x = true → σ' x = σ x) :
    a.eval σ' = a.eval σ := by
  cases a with
  | r y => exact h y (decide_eq_true rfl)
  | i c => rfl

theorem tstEval_congr {t : Tst Nat} {σ σ' : Regs Nat} (h : ∀ x, tstUses t x = true → σ' x = σ x) :
    t.eval σ' = t.eval σ := by
  unfold Tst.eval
  rw [argEval_congr (a := t.a) fun x hx => h x (by unfold tstUses; rw [hx]; rfl),
    argEval_congr (a := t.b) fun x hx => h x (by unfold tstUses; rw [hx, Bool.or_true])]

theorem upd_same (σ : Regs Nat) (d : Nat) (v : BitVec 64) : upd σ d v d = v := ite_pos rfl
theorem upd_other (σ : Regs Nat) {d x : Nat} (v : BitVec 64) (h : x ≠ d) : upd σ d v x = σ x := ite_neg h

theorem cmp_eval {op : Op} {cnd : Cond} (h : cmpOf op = some cnd) (x y : BitVec 64) :
    cnd.eval x y = !decide (op.eval x y = 0) := by
  cases op <;> simp [cmpOf] at h <;> (subst h; simp only [Cond.eval, Op.eval]; split <;> simp_all)

theorem nz_false {v : BitVec 64} (h : v = 0) : (!decide (v = 0)) = false := by rw [decide_eq_true h]; rfl
theorem nz_true {v : BitVec 64} (h : ¬v = 0) : (!decide (v = 0)) = true := by rw [decide_eq_false h]; rfl

theorem ne0_eval (σ : Regs Nat) (x : Nat) : (⟨.ne, .r x, .i 0⟩ : Tst Nat).eval σ = !decide (σ x = 0) := rfl

/-- an operand from the `into` specification of its expression -/
theorem opnd_ok {e : SExp} {ie : Nat → Nat → Code Nat} {k : Nat} {σ : St Nat}
    (hi : IntoSpec ram fp (ie (tk k) k) (tk k) k σ (e.denote env sv)) (ha : Agree ram fp env sv e σ) :
    ∃ σ', Exec ram fp (opnd e k (ie (tk k) k)).1 σ σ' ∧ (opnd e k (ie (tk k) k)).2.1.eval σ'.reg = e.denote env sv ∧
      Frame (32 + k) σ σ' ∧ argBelow (opnd e k (ie (tk k) k)).2.1 (32 + (opnd e k (ie (tk k) k)).2.2) ∧
      k ≤ (opnd e k (ie (tk k) k)).2.2 := by
  have gen : leaf e = none → ∃ σ', Exec ram fp (ie (tk k) k) σ σ' ∧ (Arg.r (tk k)).eval σ'.reg = e.denote env sv ∧
      Frame (32 + k) σ σ' ∧ argBelow (.r (tk k)) (32 + (k + 1)) ∧ k ≤ k + 1 := fun _ => by
    obtain ⟨σ', hx, hv, hm, hf⟩ := hi
    refine ⟨σ', hx, hv, ⟨hm, fun x hx => hf x (by unfold tk; omega) hx⟩, fun x hx => ?_, by omega⟩
    have := of_decide_eq_true hx; unfold tk at this; omega
  cases e with
  | var i =>
    refine ⟨σ, .skip, ha.1 i (decide_eq_true rfl), Frame.refl _ _, fun x hx => ?_, Nat.le_refl _⟩
    have := of_decide_eq_true hx; show x < 32 + k; omega
  | const c => exact ⟨σ, .skip, rfl, Frame.refl _ _, fun x hx => (Bool.false_ne_true hx).elim, Nat.le_refl _⟩
  | slot j => exact gen rfl
  | bin op a b => exact gen rfl
  | ite c a b => exact gen rfl

theorem agree_bin {op : Op} {a b : SExp} {σ : St Nat} (h : Agree ram fp env sv (.bin op a b) σ) :
    Agree ram fp env sv a σ ∧ Agree ram fp env sv b σ :=
  ⟨⟨fun i hi => h.1 i (by simp only [uses, hi, Bool.true_or]), fun j hj => h.2 j (by simp only [usesS, hj, Bool.true_or])⟩,
   ⟨fun i hi => h.1 i (by simp only [uses, hi, Bool.or_true]), fun j hj => h.2 j (by simp only [usesS, hj, Bool.or_true])⟩⟩

theorem agree_ite {c a b : SExp} {σ : St Nat} (h : Agree ram fp env sv (.ite c a b) σ) :
    Agree ram fp env sv c σ ∧ Agree ram fp env sv a σ ∧ Agree ram fp env sv b σ :=
  ⟨⟨fun i hi => h.1 i (by simp only [uses, hi, Bool.true_or]),
    fun j hj => h.2 j (by simp only [usesS, hj, Bool.true_or])⟩,
   ⟨fun i hi => h.1 i (by simp only [uses, hi, Bool.true_or, Bool.or_true]),
    fun j hj => h.2 j (by simp only [usesS, hj, Bool.true_or, Bool.or_true])⟩,
   ⟨fun i hi => h.1 i (by simp only [uses, hi, Bool.or_true]),
    fun j hj => h.2 j (by simp only [usesS, hj, Bool.or_true])⟩⟩

theorem ops2_ok {a b : SExp} {ia ib : Nat → Nat → Code Nat} {k : Nat} {σ : St Nat}
    (ha : ∀ k σ, Agree ram fp env sv a σ → IntoSpec ram fp (ia (tk k) k) (tk k) k σ (a.denote env sv))
    (hb : ∀ k σ, Agree ram fp env sv b σ → IntoSpec ram fp (ib (tk k) k) (tk k) k σ (b.denote env sv))
    (ga : Agree ram fp env sv a σ) (gb : Agree ram fp env sv b σ) :
    ∃ σ', Exec ram fp (ops2 a b ia ib k).1 σ σ' ∧ (ops2 a b ia ib k).2.1.eval σ'.reg = a.denote env sv ∧
      (ops2 a b ia ib k).2.2.1.eval σ'.reg = b.denote env sv ∧ Frame (32 + k) σ σ' ∧
      argBelow (ops2 a b ia ib k).2.1 (32 + (ops2 a b ia ib k).2.2.2) ∧
      argBelow (ops2 a b ia ib k).2.2.1 (32 + (ops2 a b ia ib k).2.2.2) ∧ k ≤ (ops2 a b ia ib k).2.2.2 := by
  obtain ⟨σ₁, x₁, v₁, f₁, b₁, k₁⟩ := opnd_ok (ha k σ ga) ga
  obtain ⟨σ₂, x₂, v₂, f₂, b₂, k₂⟩ := opnd_ok (hb _ σ₁ (gb.frame f₁)) (gb.frame f₁)
  refine ⟨σ₂, .seq x₁ x₂, ?_, v₂, f₁.trans f₂ (Nat.add_le_add_left k₁ 32), fun x hx => ?_, b₂, Nat.le_trans k₁ k₂⟩
  · rw [← v₁]; exact argEval_congr fun x hx => f₂.2 x (b₁ x hx)
  · have := b₁ x hx; show x < 32 + _; simp only [ops2]; omega

theorem tstOf_ok {c : Code Nat} {k : Nat} {σ : St Nat} {v : BitVec 64} (h : IntoSpec ram fp c (tk k) k σ v) :
    TstSpec ram fp (tstOf c k) k σ v := by
  obtain ⟨σ', hx, hv, hm, hf⟩ := h
  refine ⟨σ', hx, by rw [← hv]; rfl, ⟨hm, fun x hx => hf x (by unfold tk; omega) hx⟩, fun x hx => ?_, by
    show k ≤ k + 1; omega⟩
  have : tk k = x := by
    simp only [tstOf, tstUses, argUses, Bool.or_false] at hx; exact of_decide_eq_true hx
  show x < 32 + (k + 1); unfold tk at this; omega

theorem iteCode_ok {T : Code Nat × Tst Nat × Nat} {c a b : SExp} {ia ib : Nat → Nat → Code Nat} {d : Nat} {k : Nat}
    {σ : St Nat} (hT : TstSpec ram fp T k σ (c.denote env sv))
    (ha : ∀ d k σ, Agree ram fp env sv a σ → IntoSpec ram fp (ia d k) d k σ (a.denote env sv))
    (hb : ∀ d k σ, Agree ram fp env sv b σ → IntoSpec ram fp (ib d k) d k σ (b.denote env sv))
    (ga : Agree ram fp env sv a σ) (gb : Agree ram fp env sv b σ) :
    IntoSpec ram fp (iteCode T a b ia ib d) d k σ (if c.denote env sv = 0 then b.denote env sv else a.denote env sv) := by
  obtain ⟨σ₁, x₁, v₁, f₁, b₁, k₁⟩ := hT
  unfold iteCode
  have var_of : ∀ {e : SExp} {σ₀ : St Nat}, isVar e d = true → Agree ram fp env sv e σ₀ → σ₀.reg d = e.denote env sv := by
    intro e σ₀ h g
    cases e with
    | var i => have e : i.val = d := of_decide_eq_true h; subst e; exact g.1 i (decide_eq_true rfl)
    | slot _ => exact nomatch h
    | const _ => exact nomatch h
    | bin _ _ _ => exact nomatch h
    | ite _ _ _ => exact nomatch h
  by_cases h0 : isVar a d = true
  · rw [ite_pos h0]
    by_cases hc : c.denote env sv = 0
    · rw [ite_pos hc]
      obtain ⟨σ₂, x₂, v₂, m₂, f₂⟩ := hb d T.2.2 σ₁ (gb.frame f₁)
      refine ⟨σ₂, .seq x₁ (.whenT (by rw [Tst.eval_neg, v₁, nz_false hc]; rfl) x₂), v₂, m₂.trans f₁.1,
        fun x hd hx => ?_⟩
      rw [f₂ x hd (by omega), f₁.2 x hx]
    · rw [ite_neg hc]
      exact ⟨σ₁, .seq x₁ (.whenF (by rw [Tst.eval_neg, v₁, nz_true hc]; rfl)), var_of h0 (ga.frame f₁), f₁.1,
        fun x _ hx => f₁.2 x hx⟩
  rw [ite_neg h0]
  by_cases h1 : isVar b d = true
  · rw [ite_pos h1]
    by_cases hc : c.denote env sv = 0
    · rw [ite_pos hc]
      replace v₁ := v₁.trans (nz_false hc)
      exact ⟨σ₁, .seq x₁ (.whenF v₁), var_of h1 (gb.frame f₁), f₁.1, fun x _ hx => f₁.2 x hx⟩
    · rw [ite_neg hc]
      obtain ⟨σ₂, x₂, v₂, m₂, f₂⟩ := ha d T.2.2 σ₁ (ga.frame f₁)
      refine ⟨σ₂, .seq x₁ (.whenT (v₁.trans (nz_true hc)) x₂), v₂, m₂.trans f₁.1, fun x hd hx => ?_⟩
      rw [f₂ x hd (by omega), f₁.2 x hx]
  · rw [ite_neg h1]
    by_cases h2 : (tstUses T.2.1 d || uses a d) = false
    · rw [ite_pos h2]
      obtain ⟨hu, hua⟩ := or_false2 h2
      obtain ⟨σ₂, x₂, v₂, m₂, f₂⟩ := hb d T.2.2 σ₁ (gb.frame f₁)
      have t₂ : T.2.1.eval σ₂.reg = T.2.1.eval σ₁.reg := tstEval_congr fun x hx =>
        f₂ x (fun e => by subst e; rw [hu] at hx; exact nomatch hx) (b₁ x hx)
      by_cases hc : c.denote env sv = 0
      · rw [ite_pos hc]
        replace v₁ := v₁.trans (nz_false hc)
        exact ⟨σ₂, .seq x₁ (.seq x₂ (.whenF (t₂.trans v₁))), v₂, m₂.trans f₁.1, fun x hd hx => by
          rw [f₂ x hd (by omega), f₁.2 x hx]⟩
      · rw [ite_neg hc]
        have ga₂ : Agree ram fp env sv a σ₂ := ⟨fun i hi => by
          rw [f₂ i.val (fun e => by rw [e, hua] at hi; exact nomatch hi) (by omega)]
          exact (ga.frame f₁).1 i hi, fun j hj => by rw [m₂]; exact (ga.frame f₁).2 j hj⟩
        obtain ⟨σ₃, x₃, v₃, m₃, f₃⟩ := ha d T.2.2 σ₂ ga₂
        refine ⟨σ₃, .seq x₁ (.seq x₂ (.whenT (t₂.trans (v₁.trans (nz_true hc))) x₃)), v₃, m₃.trans (m₂.trans f₁.1),
          fun x hd hx => ?_⟩
        rw [f₃ x hd (by omega), f₂ x hd (by omega), f₁.2 x hx]
    · rw [ite_neg h2]
      obtain ⟨σ₂, x₂, v₂, m₂, f₂⟩ := hb (tk T.2.2) (T.2.2 + 1) σ₁ (gb.frame f₁)
      have lt : ∀ x, x < 32 + T.2.2 → x ≠ tk T.2.2 ∧ x < 32 + (T.2.2 + 1) := fun x hx => by unfold tk; omega
      have t₂ : T.2.1.eval σ₂.reg = T.2.1.eval σ₁.reg := tstEval_congr fun x hx =>
        f₂ x (lt x (b₁ x hx)).1 (lt x (b₁ x hx)).2
      by_cases hc : c.denote env sv = 0
      · rw [ite_pos hc]
        replace v₁ := v₁.trans (nz_false hc)
        refine ⟨⟨upd σ₂.reg d (σ₂.reg (tk T.2.2)), σ₂.mem⟩, .seq x₁ (.seq x₂ (.seq (.whenF (t₂.trans v₁))
          (.ins .set))), ?_, m₂.trans f₁.1, fun x hd hx => ?_⟩
        · show upd σ₂.reg d _ d = _; rw [upd_same, v₂]
        · show upd σ₂.reg d _ x = _
          rw [upd_other _ _ hd, f₂ x (lt x (by omega)).1 (lt x (by omega)).2, f₁.2 x hx]
      · rw [ite_neg hc]
        have ga₂ : Agree ram fp env sv a σ₂ := ⟨fun i hi => by
          rw [f₂ i.val (lt _ (by omega)).1 (lt _ (by omega)).2]; exact (ga.frame f₁).1 i hi,
          fun j hj => by rw [m₂]; exact (ga.frame f₁).2 j hj⟩
        obtain ⟨σ₃, x₃, v₃, m₃, f₃⟩ := ha (tk T.2.2) (T.2.2 + 1) σ₂ ga₂
        refine ⟨⟨upd σ₃.reg d (σ₃.reg (tk T.2.2)), σ₃.mem⟩, .seq x₁ (.seq x₂ (.seq (.whenT (t₂.trans (v₁.trans (nz_true hc))) x₃) (.ins .set))), ?_, m₃.trans (m₂.trans f₁.1), fun x hd hx => ?_⟩
        · show upd σ₃.reg d _ d = _; rw [upd_same, v₃]
        · show upd σ₃.reg d _ x = _
          rw [upd_other _ _ hd, f₃ x (lt x (by omega)).1 (lt x (by omega)).2,
            f₂ x (lt x (by omega)).1 (lt x (by omega)).2, f₁.2 x hx]

/-- **Selection is correct** (both components of `gen`). -/
theorem gen_ok : ∀ e : SExp,
    (∀ d k σ, Agree ram fp env sv e σ → IntoSpec ram fp ((gen e).1 d k) d k σ (e.denote env sv)) ∧
    (∀ k σ, Agree ram fp env sv e σ → TstSpec ram fp ((gen e).2 k) k σ (e.denote env sv))
  | .var i => by
    refine ⟨fun d k σ hg => ?_, fun k σ hg => ⟨σ, .skip, ?_, Frame.refl _ _, fun x hx => ?_, Nat.le_refl _⟩⟩
    · simp only [gen]
      by_cases h : i.val = d
      · rw [ite_pos h]; exact ⟨σ, .skip, h ▸ hg.1 i (decide_eq_true rfl), rfl, fun _ _ _ => rfl⟩
      · rw [ite_neg h]
        exact ⟨_, .ins .set, (upd_same _ _ _).trans (hg.1 i (decide_eq_true rfl)), rfl,
          fun x hx _ => upd_other _ _ hx⟩
    · simp only [gen, ne0_eval, SExp.denote]; rw [hg.1 i (decide_eq_true rfl)]; rfl
    · have : i.val = x := by
        simp only [gen, tstUses, argUses, Bool.or_false] at hx; exact of_decide_eq_true hx
      show x < 32 + k; omega
  | .slot j => by
    have into : ∀ d k σ, Agree ram fp env sv (.slot j) σ → IntoSpec ram fp ((gen (.slot j)).1 d k) d k σ
        ((SExp.slot j).denote env sv) := fun d k σ hg => by
      obtain ⟨hal, hra, hb⟩ := hg.2 j (decide_eq_true rfl)
      exact ⟨_, .ins (.ldS hal hra hb), upd_same _ _ _, rfl, fun x hx _ => upd_other _ _ hx⟩
    exact ⟨into, fun k σ hg => tstOf_ok (into (tk k) k σ hg)⟩
  | .const c => ⟨fun d k σ _ => ⟨_, .ins .set, upd_same _ _ _, rfl, fun x hx _ => upd_other _ _ hx⟩,
      fun k σ _ => ⟨σ, .skip, rfl, Frame.refl _ _, fun x hx => (Bool.false_ne_true hx).elim, Nat.le_refl _⟩⟩
  | .bin op a b => by
    have iha := gen_ok a
    have ihb := gen_ok b
    have into : ∀ d k σ, Agree ram fp env sv (.bin op a b) σ → IntoSpec ram fp ((gen (.bin op a b)).1 d k) d k σ
        ((SExp.bin op a b).denote env sv) := fun d k σ hg => by
      obtain ⟨ga, gb⟩ := agree_bin hg
      obtain ⟨σ₁, x₁, va, vb, f₁, _, _, _⟩ := ops2_ok (k := k) (fun k σ => iha.1 (tk k) k σ)
        (fun k σ => ihb.1 (tk k) k σ) ga gb
      refine ⟨_, .seq x₁ (.ins .bin), ?_, f₁.1, fun x hd hx => ?_⟩
      · show upd σ₁.reg d _ d = _; rw [upd_same, va, vb]; rfl
      · show upd σ₁.reg d _ x = _; rw [upd_other _ _ hd, f₁.2 x hx]
    refine ⟨into, fun k σ hg => ?_⟩
    simp only [gen]
    cases hc : cmpOf op with
    | none => exact tstOf_ok (into (tk k) k σ hg)
    | some cnd =>
      obtain ⟨ga, gb⟩ := agree_bin hg
      obtain ⟨σ₁, x₁, va, vb, f₁, ba, bb, kk⟩ := ops2_ok (k := k) (fun k σ => iha.1 (tk k) k σ)
        (fun k σ => ihb.1 (tk k) k σ) ga gb
      refine ⟨σ₁, x₁, ?_, f₁, fun x hx => ?_, kk⟩
      · show cnd.eval _ _ = _; rw [va, vb]; exact cmp_eval hc _ _
      · simp only [tstUses] at hx
        cases h : argUses (ops2 a b (gen a).1 (gen b).1 k).2.1 x
        · rw [h, Bool.false_or] at hx; exact bb x hx
        · exact ba x h
  | .ite c a b => by
    have ihc := gen_ok c
    have iha := gen_ok a
    have ihb := gen_ok b
    have into : ∀ d k σ, Agree ram fp env sv (.ite c a b) σ → IntoSpec ram fp ((gen (.ite c a b)).1 d k) d k σ
        ((SExp.ite c a b).denote env sv) := fun d k σ hg => by
      obtain ⟨gc, ga, gb⟩ := agree_ite hg
      exact iteCode_ok (ihc.2 k σ gc) iha.1 ihb.1 ga gb
    exact ⟨into, fun k σ hg => tstOf_ok (into (tk k) k σ hg)⟩

theorem into_ok (e : SExp) (d : Nat) (k : Nat) (σ : St Nat) (h : Agree ram fp env sv e σ) :
    IntoSpec ram fp (into e d k) d k σ (e.denote env sv) := (gen_ok e).1 d k σ h

theorem tst_ok (e : SExp) (k : Nat) (σ : St Nat) (h : Agree ram fp env sv e σ) :
    TstSpec ram fp (tst e k) k σ (e.denote env sv) := (gen_ok e).2 k σ h

/-- the loop exits when the condition is zero (`R`: what the loop preserves; implied by `Frame 8`) -/
theorem loopCode_exit {e : SExp} {body : Code Nat} {σ : St Nat} (hg : Agree ram fp env sv e σ) (h0 : e.denote env sv = 0) :
    ∃ σ', Exec ram fp (loopCode e body) σ σ' ∧ Frame 32 σ σ' := by
  unfold loopCode
  cases hc : cond2 e with
  | none =>
    obtain ⟨σ₁, x₁, t₁, f₁, _, _⟩ := tst_ok (ram := ram) e 0 σ hg
    exact ⟨σ₁, .loopF x₁ (t₁.trans (nz_false h0)), f₁⟩
  | some ca =>
    obtain ⟨c, a⟩ := ca
    have he := cond2_eq hc
    subst he
    obtain ⟨gc, ga, _⟩ := agree_ite hg
    obtain ⟨σ₁, x₁, t₁, f₁, _, _⟩ := tst_ok (ram := ram) c 0 σ gc
    by_cases hc0 : c.denote env sv = 0
    · exact ⟨σ₁, .loop2A x₁ (t₁.trans (nz_false hc0)), f₁⟩
    · obtain ⟨σ₂, x₂, t₂, f₂, _, _⟩ := tst_ok (ram := ram) a 0 σ₁ (ga.frame f₁)
      have ha0 : a.denote env sv = 0 := by simpa only [SExp.denote, if_neg hc0] using h0
      exact ⟨σ₂, .loop2B x₁ (t₁.trans (nz_true hc0)) x₂ (t₂.trans (nz_false ha0)), f₁.trans f₂ (Nat.le_refl _)⟩

/-- one iteration when the condition is nonzero -/
theorem loopCode_iter {e : SExp} {body : Code Nat} {σ : St Nat} (hg : Agree ram fp env sv e σ) (h0 : e.denote env sv ≠ 0) :
    ∃ σ₁, Frame 32 σ σ₁ ∧ ∀ σ₂ σ₃, Exec ram fp body σ₁ σ₂ → Exec ram fp (loopCode e body) σ₂ σ₃ →
      Exec ram fp (loopCode e body) σ σ₃ := by
  unfold loopCode
  cases hc : cond2 e with
  | none =>
    obtain ⟨σ₁, x₁, t₁, f₁, _, _⟩ := tst_ok (ram := ram) e 0 σ hg
    exact ⟨σ₁, f₁, fun σ₂ σ₃ xb xl => .loopT x₁ (t₁.trans (nz_true h0)) xb xl⟩
  | some ca =>
    obtain ⟨c, a⟩ := ca
    have he := cond2_eq hc
    subst he
    obtain ⟨gc, ga, _⟩ := agree_ite hg
    obtain ⟨σ₁, x₁, t₁, f₁, _, _⟩ := tst_ok (ram := ram) c 0 σ gc
    have hc0 : ¬c.denote env sv = 0 := fun h => h0 (by simp only [SExp.denote, if_pos h])
    obtain ⟨σ₂, x₂, t₂, f₂, _, _⟩ := tst_ok (ram := ram) a 0 σ₁ (ga.frame f₁)
    have ha0 : ¬a.denote env sv = 0 := fun h => h0 (by simp only [SExp.denote, if_neg hc0]; exact h)
    exact ⟨σ₂, f₁.trans f₂ (Nat.le_refl _), fun σ₃ σ₄ xb xl =>
      .loop2T x₁ (t₁.trans (nz_true hc0)) x₂ (t₂.trans (nz_true ha0)) xb xl⟩

/-! ## `AExp` (8 register-resident variables) -/

def ofA : AExp → SExp
  | .var i => .var ⟨i.val, by omega⟩
  | .const c => .const c
  | .bin op a b => .bin op (ofA a) (ofA b)
  | .ite c a b => .ite (ofA c) (ofA a) (ofA b)

/-- an `AEnv` on the 32 virtual variable registers -/
def envA (env : AEnv) : Fin 32 → BitVec 64 := fun i => if h : i.val < 8 then env ⟨i.val, h⟩ else 0

theorem ofA_denote (env : AEnv) (sv : Nat → BitVec 64) : ∀ e : AExp, (ofA e).denote (envA env) sv = e.denote env
  | .var i => by simp only [ofA, SExp.denote, AExp.denote, envA]; rw [dite_pos' i.2]
  | .const _ => rfl
  | .bin op a b => by simp only [ofA, SExp.denote, AExp.denote, ofA_denote env sv a, ofA_denote env sv b]
  | .ite c a b => by
    simp only [ofA, SExp.denote, AExp.denote, ofA_denote env sv c, ofA_denote env sv a, ofA_denote env sv b]

theorem usesS_ofA : ∀ (e : AExp) (j : Nat), usesS (ofA e) j = false
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .bin _ a b, j => by simp only [ofA, usesS, usesS_ofA a j, usesS_ofA b j, Bool.or_false]
  | .ite c a b, j => by simp only [ofA, usesS, usesS_ofA c j, usesS_ofA a j, usesS_ofA b j, Bool.or_false]

theorem uses_ofA_lt : ∀ (e : AExp) (x : Nat), uses (ofA e) x = true → x < 8
  | .var i, x, h => by have e : i.val = x := of_decide_eq_true h; omega
  | .const _, _, h => nomatch h
  | .bin _ a b, x, h => by
    simp only [ofA, uses, Bool.or_eq_true] at h
    exact h.elim (uses_ofA_lt a x) (uses_ofA_lt b x)
  | .ite c a b, x, h => by
    simp only [ofA, uses, Bool.or_eq_true] at h
    exact h.elim (fun h => h.elim (uses_ofA_lt c x) (uses_ofA_lt a x)) (uses_ofA_lt b x)

/-- the variables `e` reads hold `env` -/
theorem agreeA {env : AEnv} (e : AExp) {σ : St Nat}
    (h : ∀ i : Fin 8, uses (ofA e) i.val = true → σ.reg i.val = env i) : Agree ram fp (envA env) sv (ofA e) σ :=
  ⟨fun i hi => by
    have h8 := uses_ofA_lt e i.val hi
    unfold envA; rw [dite_pos' h8]; exact h ⟨i.val, h8⟩ hi,
   fun j hj => by rw [usesS_ofA] at hj; exact nomatch hj⟩

end Proven.Mach.Sel
