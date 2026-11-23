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

