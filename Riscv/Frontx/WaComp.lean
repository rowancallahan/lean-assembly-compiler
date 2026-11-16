/- Word arrays (NOTES section 20): the compiler from `WA` (`WaLang.lean`) to the middle layer
`Proven.Mach.BStmt` and its correctness, part 1: locations, the representation relation, expressions.

Machine variables: `0` input base, `1` input length, `2` word block base, `3` output base (the
`Implements1` convention of `implements1_of_execOW`); everything the compiler allocates is `≥ 4`.
A slot of the environment has a `Loc`: its variable `v` (a scalar's value, an array's size) and, for an
array, where the elements are: the input block (`inp`, bytes, read only) or the words `off ..` of the word
block (`wheap[0]`, every element one 64-bit word, `cap` words at most; `none`: up to the end of the block).
An expression is compiled to statements leaving its value in a target variable `d`, with temporaries
`d + 1, d + 2, ...` (three-address code; nothing below `d` is written). -/
import Riscv.Frontx.WaLang
import Compiler.BLang

namespace Proven.WA
open Proven Proven.Frontx

abbrev MB := Proven.Mach.BExp
abbrev MS := Proven.Mach.BStmt
abbrev MSt := Proven.Mach.BState

structure Loc where
  v : Nat
  inp : Bool := false
  off : Nat := 0
  cap : Option Nat := none
  deriving DecidableEq, Repr

instance : Inhabited Loc := ⟨⟨0, false, 0, none⟩⟩

/-! ## Machine operations -/

def Ty.mask : Ty → Option (BitVec 64)
  | .u8 => some 0xff#64 | .u16 => some 0xffff#64 | .u32 => some 0xffffffff#64 | _ => none

def Ty.bits : Ty → Nat | .u8 => 8 | .u16 => 16 | .u32 => 32 | _ => 64

def mkMask (t : Ty) (e : MB) : MB := match t.mask with | some m => .bin .and e (.const m) | none => e

def Op2.sup : Op2 → Ty → Bool
  | .add, t | .sub, t => t != .bool
  | .and, t | .or, t | .xor, t | .shr, t | .shl, t => t != .bool && t != .int
  | .mul, t | .div, t | .mod, t => t != .bool
  | .band, .bool | .bor, .bool => true
  | _, _ => false

/-- multiply / divide / remainder: compiled to the M-extension statement `BStmt.mop` (`mStmt`, `WaExp.lean`) -/
def Op2.isM : Op2 → Bool | .mul | .div | .mod => true | _ => false

/-- further run-time conditions: a `Nat` shift amount below 64 (`x <<< y = x * 2 ^ y` mod `2 ^ 64` is the machine's
`sll` only then) -/
def Op2.side : (o : Op2) → (t : Ty) → t.T → t.T → Prop
  | .shl, .nat, _, y => @LT.lt Nat _ y 64
  | _, _, _, _ => True

/-- operations whose `Nat` / `Int` operands must be exact (`< 2 ^ 64`, resp. `-2 ^ 63 ≤ x < 2 ^ 63`): not
homomorphic mod `2 ^ 64` (`Int` `-` is) -/
def Op2.exact : Op2 → Ty → Bool
  | .sub, .int => false
  | .sub, _ | .shr, _ | .div, _ | .mod, _ => true
  | _, _ => false

/-- `a &&& b`, folded when both are constants -/
def band : MB → MB → MB
  | .const x, .const y => .const (x &&& y)
  | a, b => .bin .and a b

theorem band_denote (env : Mach.BEnv) (a b : MB) : (band a b).denote env = Mach.BExp.denote env (.bin .and a b) := by
  unfold band; split <;> rfl

def mop : Op2 → Ty → MB → MB → MB
  | .add, t, a, b => mkMask t (.bin .add a b)
  | .sub, .nat, a, b => .ite (.bin .ult a b) (.const 0) (.bin .sub a b)
  | .sub, t, a, b => mkMask t (.bin .sub a b)
  | .and, _, a, b | .band, _, a, b => .bin .and a b
  | .or, _, a, b | .bor, _, a, b => .bin .or a b
  | .xor, _, a, b => .bin .xor a b
  | .shl, t, a, b => mkMask t (.bin .shl a (band b (.const (BitVec.ofNat 64 (t.bits - 1)))))
  | .shr, .nat, a, b => .ite (.bin .ult b (.const 64)) (.bin .lshr a b) (.const 0)
  | .shr, t, a, b => .bin .lshr a (band b (.const (BitVec.ofNat 64 (t.bits - 1))))
  | _, _, a, _ => a

def Cmp.sup : Cmp → Ty → Bool
  | .eq, _ | .ne, _ => true
  | _, t => t != .bool

/-- comparisons; `Int` ones signed (`slt`) -/
def mcmp (t : Ty) : Cmp → MB → MB → MB
  | .eq, a, b => .bin .eq a b
  | .ne, a, b => .bin .xor (.bin .eq a b) (.const 1)
  | .lt, a, b => .bin (if t = .int then .slt else .ult) a b
  | .le, a, b => .bin .xor (.bin (if t = .int then .slt else .ult) b a) (.const 1)

def cast.sup : Ty → Ty → Bool
  | .bool, t | t, .bool => t == .bool
  | .int, t | t, .int => t == .nat
  | .nat, .nat => false
  | s, t => s != t

def mcast : Ty → Ty → MB → MB
  | .bool, .bool, a => .bin .xor a (.const 1)
  | .int, .nat, a => .ite (.bin .slt a (.const 0)) (.const 0) a
  | .nat, t, a => mkMask t a
  | s, t, a => if s.bits ≤ t.bits then a else mkMask t a

/-! ## Representation -/

/-- element `j` of an array as a machine word -/
def AK.w (k : AK) (a : k.T) (j : Nat) : BitVec 64 := k.el.rep (AK.get k a j)

/-- the work words `W` / input bytes `I` hold array `a` at `l` -/
def AR (I : List (BitVec 8)) (W : List (BitVec 64)) (k : AK) (l : Loc) (a : k.T) : Prop :=
  if l.inp then AK.size k a ≤ I.length ∧ ∀ j, j < AK.size k a → (I[j]?).map (·.setWidth 64) = some (AK.w k a j)
  else l.off + AK.size k a ≤ W.length ∧ W.length < 2 ^ 32 ∧ (∀ c, l.cap = some c → AK.size k a ≤ c) ∧
    ∀ j, j < AK.size k a → W[l.off + j]? = some (AK.w k a j)

def SR (σ : MSt) : (s : Sl) → Loc → s.T → Prop
  | .sc t, l, x => σ.env l.v = t.rep x
  | .ar k, l, a => σ.env l.v = rN (AK.size k a) ∧ AK.size k a < 2 ^ 32 ∧
      AR (σ.heap.getD 0 []) (σ.wheap.getD 0 []) k l a

/-- every slot is represented -/
def Rel : (Γ : List Sl) → List Loc → Vals Γ → MSt → Prop
  | [], _, _, _ => True
  | s :: Γ, L, v, σ => SR σ s (L.headD default) v.1 ∧ Rel Γ L.tail v.2 σ

def Mem.loc {Γ : List Sl} {s : Sl} (m : Mem Γ s) (L : List Loc) : Loc := L.getD m.idx default

theorem Rel.get : ∀ {Γ : List Sl} {L : List Loc} {v : Vals Γ} {σ : MSt} {s : Sl} (m : Mem Γ s),
    Rel Γ L v σ → SR σ s (m.loc L) (m.get v)
  | _ :: _, L, _, _, _, .hd, h => by
    cases L <;> exact h.1
  | _ :: _, L, _, _, _, .tl m, h => by
    cases L with
    | nil => have := Rel.get m h.2; cases m <;> exact this
    | cons l L => exact Rel.get m h.2

/-- the variables of the slots -/
def vsOf (L : List Loc) : List Nat := L.map (·.v)

theorem SR.frame {σ σ' : MSt} {s : Sl} {l : Loc} {x : s.T} (h : SR σ s l x) (hv : σ'.env l.v = σ.env l.v)
    (hh : σ'.heap = σ.heap) (hw : σ'.wheap = σ.wheap) : SR σ' s l x := by
  cases s with
  | sc t => show σ'.env l.v = _; rw [hv]; exact h
  | ar k => show σ'.env l.v = _ ∧ _ ∧ AR (σ'.heap.getD 0 []) (σ'.wheap.getD 0 []) k l x
            rw [hv, hh, hw]; exact h

theorem Rel.frame : ∀ {Γ : List Sl} {L : List Loc} {v : Vals Γ} {σ σ' : MSt}, Rel Γ L v σ →
    (∀ l ∈ L, σ'.env l.v = σ.env l.v) → σ'.heap = σ.heap → σ'.wheap = σ.wheap → Γ.length ≤ L.length →
    Rel Γ L v σ'
  | [], _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _, _, _, hl => by simp at hl
  | _ :: _, l :: L, _, _, _, h, hv, hh, hw, hl =>
    ⟨SR.frame h.1 (hv l (List.mem_cons_self ..)) hh hw,
      Rel.frame h.2 (fun l' h' => hv l' (List.mem_cons_of_mem _ h')) hh hw (by simp at hl ⊢; omega)⟩

/-! ## Operation lemmas: the machine word of each result -/

def Ty.small : (t : Ty) → t.T → Prop
  | .nat, x => @LT.lt Nat _ x (2 ^ 64)
  | .int, x => @LE.le Int _ (-2 ^ 63) x ∧ @LT.lt Int _ x (2 ^ 63)
  | _, _ => True

/-- run-time condition of a cast: `Int.toNat` reads the sign, so the operand in range -/
def cast.side : (s t : Ty) → s.T → Prop
  | .int, .nat, x => @LE.le Int _ (-2 ^ 63) x ∧ @LT.lt Int _ x (2 ^ 63)
  | _, _, _ => True


theorem r8_shl' (a b : UInt8) :
    r8 (a <<< b) = (r8 a <<< ((r8 b &&& 7#64).toNat % 64)) &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq
  have h : (r8 b &&& 7#64).toNat = b.toNat % 2 ^ 3 := by
    rw [BitVec.toNat_and, r8_nat]; exact Nat.and_two_pow_sub_one_eq_mod _ 3
  rw [and_mask8, BitVec.toNat_shiftLeft, h, r8_nat, r8_nat, UInt8.toNat_shiftLeft]
  have : b.toNat % 2 ^ 3 % 64 = b.toNat % 8 := by omega
  rw [this, Nat.mod_mod_of_dvd _ (by decide)]
theorem r64_nat (a : UInt64) : (r64 a).toNat = a.toNat := rfl
theorem r64_shl' (a b : UInt64) : r64 (a <<< b) = r64 a <<< ((r64 b &&& 63#64).toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  have h : (r64 b &&& 63#64).toNat = b.toNat % 2 ^ 6 := by
    rw [BitVec.toNat_and, r64_nat]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
  rw [BitVec.toNat_shiftLeft, h, r64_nat, r64_nat, UInt64.toNat_shiftLeft]
  have : b.toNat % 2 ^ 6 % 64 = b.toNat % 64 := by omega
  rw [this]
theorem r64_shr' (a b : UInt64) : r64 (a >>> b) = r64 a >>> ((r64 b &&& 63#64).toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  have h : (r64 b &&& 63#64).toNat = b.toNat % 2 ^ 6 := by
    rw [BitVec.toNat_and, r64_nat]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
  rw [BitVec.toNat_ushiftRight, h, r64_nat, r64_nat, UInt64.toNat_shiftRight]
  have : b.toNat % 2 ^ 6 % 64 = b.toNat % 64 := by omega
  rw [this]
theorem rN_xor (a b : Nat) : rN (a ^^^ b) = rN a ^^^ rN b := by
  apply BitVec.eq_of_toNat_eq; simp [rN, Nat.xor_mod_two_pow]
theorem rN_subI {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (if (if rN x < rN y then 1#64 else 0#64) = 0#64 then rN x - rN y else 0#64) = rN (x - y) := by
  rw [rN_sub' hx hy]; simp only [rN_lt hx hy]; by_cases h : x < y <;> simp [h]
theorem rN_shrI {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (if (if rN y < 64#64 then 1#64 else 0#64) = 0#64 then 0#64 else rN x >>> ((rN y).toNat % 64)) = rN (x >>> y) := by
  rw [show (64#64) = rN 64 from rfl, rN_toNat hy]; simp only [rN_lt hy (by decide : 64 < 2 ^ 64)]
  by_cases h : y < 64
  · simp [h, Nat.mod_eq_of_lt h, rN_shr hx]
  · simp only [h, if_false, if_true]
    apply BitVec.eq_of_toNat_eq
    simp only [rN, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have : x / 2 ^ y = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

macro "wa_op_close" : tactic => `(tactic| first
  | rfl
  | (simp only [r8_add, r16_add, r32_add, r64_add, rN_add, r8_sub, r16_sub, r32_sub, r64_sub, r8_and, r16_and,
      r32_and, r64_and, rN_and, r8_or, r16_or, r32_or, r64_or, rN_or, r8_xor, r16_xor, r32_xor, r64_xor, rN_xor,
      r8_shl', r16_shl, r32_shl, r64_shl', r8_shr, r16_shr, r32_shr, r64_shr', rI_add, rI_sub]; done)
  | exact rN_subI (by assumption) (by assumption)
  | (cases ‹_ ∧ _›; exact rN_subI (by assumption) (by assumption))
  | (cases ‹_ ∧ _›; exact rN_shrI (by assumption) (by assumption))

  | (cases ‹Bool› <;> cases ‹Bool› <;> rfl))
theorem rN_shlI {x y : Nat} (hy : y < 64) : rN x <<< ((rN y &&& 63#64).toNat % 64) = rN (x <<< y) := by
  have h : (rN y &&& 63#64).toNat = y := by
    rw [BitVec.toNat_and, rN_toNat (by omega)]
    show y &&& (2 ^ 6 - 1) = y
    rw [Nat.and_two_pow_sub_one_eq_mod _ 6]; omega
  rw [h, Nat.mod_eq_of_lt hy]
  apply BitVec.eq_of_toNat_eq; simp [rN, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

theorem mop_ok (o : Op2) (t : Ty) (env : Mach.BEnv) (a b : MB) (x y : t.T)
    (ha : a.denote env = t.rep x) (hb : b.denote env = t.rep y) (hs : o.sup t = true) (hm : o.isM = false)
    (hx : o.exact t = true → t.small x ∧ t.small y) (hside : o.side t x y) :
    (mop o t a b).denote env = t.rep (o.den t x y) := by
  cases o <;> cases t <;> (try (exfalso; revert hs; decide)) <;> (try (exfalso; revert hm; decide)) <;>
    simp only [Op2.side] at hside <;> simp only [Op2.exact, Ty.small, forall_const] at hx <;>
    simp only [mop, mkMask, Ty.mask, Op2.den, Ty.rep, Mach.BExp.denote, band_denote, Op.eval, ha, hb, Ty.bits,
      Nat.reduceSub] <;>
    first | exact rN_shlI hside | wa_op_close

theorem r16_of64' (a : UInt64) : r16 a.toUInt16 = r64 a &&& 0xffff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask16, r16_nat, UInt64.toNat_toUInt16]; rfl
theorem rB_inj (a b : Bool) : (rB a = rB b) = (a = b) := by cases a <;> cases b <;> decide

theorem ite_rB (p : Prop) [Decidable p] (b : Bool) (h : p ↔ b = true) : (if p then 1#64 else 0#64) = rB b := by
  by_cases hp : p
  · rw [if_pos hp, (h.1 hp)]; rfl
  · have : b = false := by cases b <;> simp_all
    rw [if_neg hp, this]; rfl
theorem ite_rB' (p : Prop) [Decidable p] (b : Bool) (h : p ↔ b = false) :
    (if p then 1#64 else 0#64) ^^^ 1#64 = rB b := by
  by_cases hp : p
  · rw [if_pos hp, (h.1 hp)]; rfl
  · have : b = true := by cases b <;> simp_all
    rw [if_neg hp, this]; rfl

macro "wa_cmp_close" : tactic => `(tactic| first
  | (apply ite_rB; simp only [r8_inj, r16_inj, r32_inj, r64_inj, rB_inj, r8_lt, r16_lt, r32_lt, r64_lt, beq_iff_eq,
      decide_eq_true_eq]; done)
  | (apply ite_rB'; simp only [r8_inj, r16_inj, r32_inj, r64_inj, rB_inj, r8_lt, r16_lt, r32_lt, r64_lt,
      bne_eq_false_iff_eq, decide_eq_false_iff_not, UInt8.not_le, UInt16.not_le, UInt32.not_le, UInt64.not_le]; done)
  | (apply ite_rB; obtain ⟨h1, h2⟩ := ‹_ ∧ _›
     simp only [rN_inj h1 h2, rN_lt h1 h2, beq_iff_eq, decide_eq_true_eq]; done)
  | (apply ite_rB'; obtain ⟨h1, h2⟩ := ‹_ ∧ _›
     simp only [rN_inj h1 h2, rN_lt h2 h1, bne_eq_false_iff_eq, decide_eq_false_iff_not, Nat.not_le]; done)
  | (apply ite_rB; obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ‹_ ∧ _›
     simp only [rI_inj h1 h2 h3 h4, rI_slt h1 h2 h3 h4, beq_iff_eq, decide_eq_true_eq, if_true]; done)
  | (apply ite_rB'; obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ‹_ ∧ _›
     simp only [rI_inj h1 h2 h3 h4, rI_slt h3 h4 h1 h2, bne_eq_false_iff_eq, decide_eq_false_iff_not, Int.not_le,
       decide_eq_true_eq, if_true]; done))

theorem mcmp_ok (o : Cmp) (t : Ty) (env : Mach.BEnv) (a b : MB) (x y : t.T)
    (ha : a.denote env = t.rep x) (hb : b.denote env = t.rep y) (hs : o.sup t = true)
    (hx : t.small x ∧ t.small y) :
    (mcmp t o a b).denote env = rB (o.den t x y) := by
  cases o <;> cases t <;> (try (exfalso; revert hs; decide)) <;> simp only [Ty.small] at hx <;>
    simp only [mcmp, Cmp.den, Ty.rep, Mach.BExp.denote, Op.eval, ha, hb] <;> wa_cmp_close

theorem r16_toNat' (a : UInt16) : rN a.toNat = r16 a := by
  apply BitVec.eq_of_toNat_eq; have := a.toNat_lt; rw [r16_nat]; simp [rN]
theorem r64_toNat' (a : UInt64) : rN a.toNat = r64 a := r64_toNat a
theorem toNat_castI {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) :
    (if (if (rI x).slt 0#64 = true then 1#64 else 0#64) = 0#64 then rI x else 0#64) = rN x.toNat := by
  rw [rN_toNatI h1 h2]; by_cases h : (rI x).slt 0#64 = true <;> simp [h]
theorem mcast_ok (s t : Ty) (env : Mach.BEnv) (a : MB) (x : s.T)
    (ha : a.denote env = s.rep x) (hs : cast.sup s t = true) (hx : cast.side s t x) :
    (mcast s t a).denote env = t.rep (WA.cast s t x) := by
  cases s <;> cases t <;> (try (exfalso; revert hs; decide)) <;>
    simp only [mcast, mkMask, Ty.mask, Ty.bits, WA.cast, Ty.rep, Mach.BExp.denote, Op.eval, ha, Nat.reduceLeDiff,
      if_true, if_false] <;>
    first
    | (simp only [r8_toNat, r16_toNat', r32_toNat, r64_toNat', r8_ofNatU, r16_ofNatU, r32_ofNatU, r64_ofNatU,
        r16_of8, r32_of8, r64_of8, r32_of16, r64_of16, r64_of32, r8_of16, r8_of32, r8_of64, r16_of32, r16_of64',
        r32_of64]; done)
    | (cases x <;> rfl)
    | (simp only [cast.side] at hx; exact toNat_castI hx.1 hx.2)
    | (exact (rI_ofNat x).symm)

end Proven.WA
