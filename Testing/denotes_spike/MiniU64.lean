/- MiniU64: grows MiniDenotes (same copied `Expr`, `natLitToConstructor`, `push`, `Denotes` rules bvar/const/app/natLit;
see MiniDenotes.lean for line refs) towards UInt64.  No imports.  Model facts are HYPOTHESES, in the shape of
BridgeU64.lean (Nat binders, `UInt64.ofNat`, `% 2^64`, `Nat.beq`/`Nat.ble`+`cond`).  `pt` (the `Fin.mk` bound proof) is
a constant `cval "pt"` (proof irrelevance abstracted).  `ite R (c = true) inst t e` is abstracted to a single head
applied to `a b t e` (as `iteEq` in MiniDenotes).  Features, each a sorry-free theorem:
  1 `u64_lit_denotes`   2 `u64_add/sub/mul/and/or/xor/shl/shr_denotes`   3 `u64_beq_denotes`
  4 `u64_ite_beq_denotes`, `u64_ite_lt_denotes`   5 `u64_denotes` (all together, induction). -/
namespace MiniU64

inductive Literal | natVal (n : Nat)

inductive Expr
  | bvar (i : Nat)
  | const (n : String)
  | app (f a : Expr)
  | lit (l : Literal)

def natLitToConstructor (n : Nat) : Expr :=
  match n with
  | 0 => .const "Nat.zero"
  | k + 1 => .app (.const "Nat.succ") (.lit (.natVal k))

variable {V : Type} (app : V → V → V)

inductive Denotes (cval : String → V) : (Nat → V) → Expr → V → Prop
  | bvar {ρ i} : Denotes cval ρ (.bvar i) (ρ i)
  | const {ρ n} : Denotes cval ρ (.const n) (cval n)
  | app {ρ f a F X} : Denotes cval ρ f F → Denotes cval ρ a X → Denotes cval ρ (.app f a) (app F X)
  | natLit {ρ n X} : Denotes cval ρ (natLitToConstructor n) X → Denotes cval ρ (.lit (.natVal n)) X

def enc (cval : String → V) : Nat → V
  | 0 => cval "Nat.zero"
  | n + 1 => app (cval "Nat.succ") (enc cval n)

theorem lit_denotes (cval : String → V) (ρ : Nat → V) :
    ∀ n, Denotes app cval ρ (.lit (.natVal n)) (enc app cval n)
  | 0 => .natLit .const
  | n + 1 => .natLit (.app .const (lit_denotes cval ρ n))

/-! ## bridge facts (Nat-level; copied from BridgeU64.lean) -/
local notation "U" => (18446744073709551616 : Nat)

theorem br_add : ∀ a b : Nat, UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) :=
  fun a b => (UInt64.ofNat_add a b).symm
theorem br_mul : ∀ a b : Nat, UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) :=
  fun a b => (UInt64.ofNat_mul a b).symm
theorem br_sub : ∀ a b : Nat, UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a + (U * b - b)) := by
  intro a b
  have h1 : a + (U * b - b) = (a + U * b) - b := by omega
  have h2 : ∀ k : Nat, UInt64.ofNat (a + U * k) = UInt64.ofNat a := by
    intro k
    rw [← UInt64.ofNat_mod_size (x := a + _), ← UInt64.ofNat_mod_size (x := a)]
    congr 1
    exact Nat.add_mul_mod_self_left a _ k
  rw [h1, UInt64.ofNat_sub (by omega), h2]
theorem br_and : ∀ a b : Nat, UInt64.ofNat a &&& UInt64.ofNat b = UInt64.ofNat (a &&& b) :=
  fun a b => (UInt64.ofNat_and a b).symm
theorem br_or : ∀ a b : Nat, UInt64.ofNat a ||| UInt64.ofNat b = UInt64.ofNat (a ||| b) :=
  fun a b => (UInt64.ofNat_or a b).symm
theorem br_xor : ∀ a b : Nat, UInt64.ofNat a ^^^ UInt64.ofNat b = UInt64.ofNat (a ^^^ b) :=
  fun a b => (UInt64.ofNat_xor a b).symm
theorem br_shl : ∀ a b : Nat, UInt64.ofNat a <<< UInt64.ofNat b = UInt64.ofNat (a <<< (b % 64)) := by
  intro a b
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_shiftLeft]
  simp [Nat.shiftLeft_eq, Nat.mod_mul_mod]
theorem br_shr : ∀ a b : Nat, UInt64.ofNat a >>> UInt64.ofNat b = UInt64.ofNat ((a % U) >>> (b % 64)) := by
  intro a b
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_shiftRight]
  simp
  refine (Nat.mod_eq_of_lt ?_).symm
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
theorem br_beq64 : ∀ a b : Nat, (UInt64.ofNat a == UInt64.ofNat b) = Nat.beq (a % U) (b % U) := by
  intro a b
  show decide (UInt64.ofNat a = UInt64.ofNat b) = _
  rw [Bool.eq_iff_iff]
  simp [← UInt64.toNat_inj]
theorem br_lt64 : ∀ (R : Type) (a b : Nat) (t e : R),
    @ite R (UInt64.ofNat a < UInt64.ofNat b) (UInt64.decLt (UInt64.ofNat a) (UInt64.ofNat b)) t e =
    cond (Nat.ble (a % U + 1) (b % U)) t e := by
  intro R a b t e
  have h : (UInt64.ofNat a < UInt64.ofNat b) ↔ Nat.ble (a % U + 1) (b % U) = true := by
    simp [UInt64.lt_iff_toNat_lt, Nat.ble_eq, Nat.succ_le_iff]
  cases hb : Nat.ble (a % U + 1) (b % U)
  · rw [hb] at h; exact ite_eq_right_iff.2 (fun hl => by simp_all)
  · rw [hb] at h; exact (if_pos (h.2 rfl))
theorem u_surj (x : UInt64) : ∃ a, x = UInt64.ofNat a := ⟨x.toNat, (UInt64.ofNat_toNat).symm⟩

/-! ## 1. UInt64 literals -/
/-- the expression for a UInt64 literal: `UInt64.ofBitVec (BitVec.ofFin (Fin.mk 2^64 n pt))` with Nat literals inside -/
def lit64 (n : Nat) : Expr :=
  .app (.const "UInt64.ofBitVec") (.app (.const "BitVec.ofFin")
    (.app (.app (.app (.const "Fin.mk") (.lit (.natVal U))) (.lit (.natVal n))) (.const "pt")))

/-- the set-level encoding of a UInt64 -/
def encU (cval : String → V) (x : UInt64) : V :=
  app (cval "UInt64.ofBitVec") (app (cval "BitVec.ofFin")
    (app (app (app (cval "Fin.mk") (enc app cval U)) (enc app cval x.toNat)) (cval "pt")))

theorem u64_lit_denotes (cval : String → V) (ρ : Nat → V) (x : UInt64) :
    Denotes app cval ρ (lit64 x.toNat) (encU app cval x) :=
  .app .const (.app .const (.app (.app (.app .const (lit_denotes app cval ρ U)) (lit_denotes app cval ρ x.toNat)) .const))

/-! ## 2. binary UInt64 ops -/
theorem lift2 (f : V) (g : Nat → Nat → Nat) (op : UInt64 → UInt64 → UInt64) (cval : String → V)
    (hbr : ∀ a b, op (UInt64.ofNat a) (UInt64.ofNat b) = UInt64.ofNat (g a b))
    (hnat : ∀ a b, app (app f (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat (g a b))) :
    ∀ x y, app (app f (encU app cval x)) (encU app cval y) = encU app cval (op x y) := by
  intro x y
  obtain ⟨a, rfl⟩ := u_surj x
  obtain ⟨b, rfl⟩ := u_surj y
  rw [hbr]; exact hnat a b

theorem binop_denotes (cval : String → V) (ρ : Nat → V) (name : String) (op : UInt64 → UInt64 → UInt64)
    (hop : ∀ x y, app (app (cval name) (encU app cval x)) (encU app cval y) = encU app cval (op x y))
    {ta tb : Expr} {x y : UInt64}
    (ha : Denotes app cval ρ ta (encU app cval x)) (hb : Denotes app cval ρ tb (encU app cval y)) :
    Denotes app cval ρ (.app (.app (.const name) ta) tb) (encU app cval (op x y)) := by
  have := Denotes.app (Denotes.app (Denotes.const (n := name)) ha) hb
  rwa [hop] at this

section ops
variable (cval : String → V) (ρ : Nat → V) {ta tb : Expr} {x y : UInt64}
  (ha : Denotes app cval ρ ta (encU app cval x)) (hb : Denotes app cval ρ tb (encU app cval y))
include ha hb

theorem u64_add_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.add") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat (a + b))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.add") ta) tb) (encU app cval (x + y)) :=
  binop_denotes app cval ρ _ _ (lift2 app _ _ _ cval br_add h) ha hb

theorem u64_sub_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.sub") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat (a + (U * b - b)))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.sub") ta) tb) (encU app cval (x - y)) :=
  binop_denotes app cval ρ _ _ (lift2 app _ _ _ cval br_sub h) ha hb

theorem u64_mul_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.mul") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat (a * b))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.mul") ta) tb) (encU app cval (x * y)) :=
  binop_denotes app cval ρ _ _ (lift2 app _ _ _ cval br_mul h) ha hb

theorem u64_and_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.land") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat (a &&& b))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.land") ta) tb) (encU app cval (x &&& y)) :=
  binop_denotes app cval ρ _ _ (lift2 app _ _ _ cval br_and h) ha hb

theorem u64_or_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.lor") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat (a ||| b))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.lor") ta) tb) (encU app cval (x ||| y)) :=
  binop_denotes app cval ρ _ _ (lift2 app _ _ _ cval br_or h) ha hb

theorem u64_xor_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.xor") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat (a ^^^ b))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.xor") ta) tb) (encU app cval (x ^^^ y)) :=
  binop_denotes app cval ρ _ _ (lift2 app _ _ _ cval br_xor h) ha hb

theorem u64_shl_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.shiftLeft") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat (a <<< (b % 64)))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.shiftLeft") ta) tb) (encU app cval (x <<< y)) :=
  binop_denotes app cval ρ _ _ (lift2 app _ _ _ cval br_shl h) ha hb

theorem u64_shr_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.shiftRight") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encU app cval (UInt64.ofNat ((a % U) >>> (b % 64)))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.shiftRight") ta) tb) (encU app cval (x >>> y)) :=
  binop_denotes app cval ρ _ _ (lift2 app _ _ _ cval br_shr h) ha hb

/-! ## 3. `==` as a Bool-valued term -/
def encB (cval : String → V) (b : Bool) : V := cval (if b then "Bool.true" else "Bool.false")

theorem u64_beq_denotes
    (h : ∀ a b : Nat, app (app (cval "UInt64.beq") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) =
      encB cval (Nat.beq (a % U) (b % U))) :
    Denotes app cval ρ (.app (.app (.const "UInt64.beq") ta) tb) (encB cval (x == y)) := by
  have := Denotes.app (Denotes.app (Denotes.const (n := "UInt64.beq")) ha) hb
  obtain ⟨a, rfl⟩ := u_surj x
  obtain ⟨b, rfl⟩ := u_surj y
  rwa [h, ← br_beq64] at this

/-! ## 4. `ite` on `==` and on `<` (one head applied to `a b t e`) -/
theorem u64_ite_beq_denotes {tt te : Expr} {T E : V}
    (h : ∀ (a b : Nat) (t e : V), app (app (app (app (cval "iteBeq64") (encU app cval (UInt64.ofNat a)))
      (encU app cval (UInt64.ofNat b))) t) e = cond (Nat.beq (a % U) (b % U)) t e)
    (ht : Denotes app cval ρ tt T) (he : Denotes app cval ρ te E) :
    Denotes app cval ρ (.app (.app (.app (.app (.const "iteBeq64") ta) tb) tt) te)
      (if (x == y) = true then T else E) := by
  have := Denotes.app (Denotes.app (Denotes.app (Denotes.app (Denotes.const (n := "iteBeq64")) ha) hb) ht) he
  obtain ⟨a, rfl⟩ := u_surj x
  obtain ⟨b, rfl⟩ := u_surj y
  rw [h, ← br_beq64] at this
  cases hc : (UInt64.ofNat a == UInt64.ofNat b) <;> simp only [hc, cond, Bool.false_eq_true, ite_false, ite_true] at this ⊢ <;> exact this

theorem u64_ite_lt_denotes {tt te : Expr} {T E : V}
    (h : ∀ (a b : Nat) (t e : V), app (app (app (app (cval "iteLt64") (encU app cval (UInt64.ofNat a)))
      (encU app cval (UInt64.ofNat b))) t) e = cond (Nat.ble (a % U + 1) (b % U)) t e)
    (ht : Denotes app cval ρ tt T) (he : Denotes app cval ρ te E) :
    Denotes app cval ρ (.app (.app (.app (.app (.const "iteLt64") ta) tb) tt) te)
      (if x < y then T else E) := by
  have := Denotes.app (Denotes.app (Denotes.app (Denotes.app (Denotes.const (n := "iteLt64")) ha) hb) ht) he
  obtain ⟨a, rfl⟩ := u_surj x
  obtain ⟨b, rfl⟩ := u_surj y
  rw [h, ← br_lt64] at this
  exact this
end ops

/-! ## 5. everything together: a UInt64 language, evaluator = emitted-term denotation -/
inductive T
  | lit (x : UInt64)
  | add (a b : T) | sub (a b : T) | mul (a b : T) | land (a b : T) | lor (a b : T) | xor (a b : T)
  | shl (a b : T) | shr (a b : T)
  | iteBeq (a b t e : T) | iteLt (a b t e : T)

def eval : T → UInt64
  | .lit x => x
  | .add a b => eval a + eval b
  | .sub a b => eval a - eval b
  | .mul a b => eval a * eval b
  | .land a b => eval a &&& eval b
  | .lor a b => eval a ||| eval b
  | .xor a b => eval a ^^^ eval b
  | .shl a b => eval a <<< eval b
  | .shr a b => eval a >>> eval b
  | .iteBeq a b t e => if (eval a == eval b) = true then eval t else eval e
  | .iteLt a b t e => if eval a < eval b then eval t else eval e

def bin (n : String) (a b : Expr) : Expr := .app (.app (.const n) a) b
def tr : T → Expr
  | .lit x => lit64 x.toNat
  | .add a b => bin "UInt64.add" (tr a) (tr b)
  | .sub a b => bin "UInt64.sub" (tr a) (tr b)
  | .mul a b => bin "UInt64.mul" (tr a) (tr b)
  | .land a b => bin "UInt64.land" (tr a) (tr b)
  | .lor a b => bin "UInt64.lor" (tr a) (tr b)
  | .xor a b => bin "UInt64.xor" (tr a) (tr b)
  | .shl a b => bin "UInt64.shiftLeft" (tr a) (tr b)
  | .shr a b => bin "UInt64.shiftRight" (tr a) (tr b)
  | .iteBeq a b t e => .app (.app (bin "iteBeq64" (tr a) (tr b)) (tr t)) (tr e)
  | .iteLt a b t e => .app (.app (bin "iteLt64" (tr a) (tr b)) (tr t)) (tr e)

/-- the model facts, Nat-level shapes as in BridgeU64 -/
structure Facts (cval : String → V) : Prop where
  add : ∀ a b : Nat, app (app (cval "UInt64.add") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) = encU app cval (UInt64.ofNat (a + b))
  sub : ∀ a b : Nat, app (app (cval "UInt64.sub") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) = encU app cval (UInt64.ofNat (a + (U * b - b)))
  mul : ∀ a b : Nat, app (app (cval "UInt64.mul") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) = encU app cval (UInt64.ofNat (a * b))
  land : ∀ a b : Nat, app (app (cval "UInt64.land") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) = encU app cval (UInt64.ofNat (a &&& b))
  lor : ∀ a b : Nat, app (app (cval "UInt64.lor") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) = encU app cval (UInt64.ofNat (a ||| b))
  xor : ∀ a b : Nat, app (app (cval "UInt64.xor") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) = encU app cval (UInt64.ofNat (a ^^^ b))
  shl : ∀ a b : Nat, app (app (cval "UInt64.shiftLeft") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) = encU app cval (UInt64.ofNat (a <<< (b % 64)))
  shr : ∀ a b : Nat, app (app (cval "UInt64.shiftRight") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b)) = encU app cval (UInt64.ofNat ((a % U) >>> (b % 64)))
  iteBeq : ∀ (a b : Nat) (t e : V), app (app (app (app (cval "iteBeq64") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b))) t) e = cond (Nat.beq (a % U) (b % U)) t e
  iteLt : ∀ (a b : Nat) (t e : V), app (app (app (app (cval "iteLt64") (encU app cval (UInt64.ofNat a))) (encU app cval (UInt64.ofNat b))) t) e = cond (Nat.ble (a % U + 1) (b % U)) t e

/-- **UInt64 theorem**: the evaluator's value is what the emitted term denotes. -/
theorem u64_denotes (cval : String → V) (ρ : Nat → V) (F : Facts app cval) :
    ∀ e, Denotes app cval ρ (tr e) (encU app cval (eval e)) := by
  intro e
  induction e with
  | lit x => exact u64_lit_denotes app cval ρ x
  | add a b iha ihb => exact u64_add_denotes app cval ρ iha ihb F.add
  | sub a b iha ihb => exact u64_sub_denotes app cval ρ iha ihb F.sub
  | mul a b iha ihb => exact u64_mul_denotes app cval ρ iha ihb F.mul
  | land a b iha ihb => exact u64_and_denotes app cval ρ iha ihb F.land
  | lor a b iha ihb => exact u64_or_denotes app cval ρ iha ihb F.lor
  | xor a b iha ihb => exact u64_xor_denotes app cval ρ iha ihb F.xor
  | shl a b iha ihb => exact u64_shl_denotes app cval ρ iha ihb F.shl
  | shr a b iha ihb => exact u64_shr_denotes app cval ρ iha ihb F.shr
  | iteBeq a b t e iha ihb iht ihe =>
    have := u64_ite_beq_denotes app cval ρ iha ihb F.iteBeq iht ihe
    simp only [eval]
    split <;> rename_i hc <;> simp only [hc, ite_true, ite_false] at this <;> exact this
  | iteLt a b t e iha ihb iht ihe =>
    have := u64_ite_lt_denotes app cval ρ iha ihb F.iteLt iht ihe
    simp only [eval]
    split <;> rename_i hc <;> simp only [hc, ite_true, ite_false] at this <;> exact this

end MiniU64

#print axioms MiniU64.u64_lit_denotes
#print axioms MiniU64.u64_add_denotes
#print axioms MiniU64.u64_sub_denotes
#print axioms MiniU64.u64_mul_denotes
#print axioms MiniU64.u64_and_denotes
#print axioms MiniU64.u64_or_denotes
#print axioms MiniU64.u64_xor_denotes
#print axioms MiniU64.u64_shl_denotes
#print axioms MiniU64.u64_shr_denotes
#print axioms MiniU64.u64_beq_denotes
#print axioms MiniU64.u64_ite_beq_denotes
#print axioms MiniU64.u64_ite_lt_denotes
#print axioms MiniU64.u64_denotes
