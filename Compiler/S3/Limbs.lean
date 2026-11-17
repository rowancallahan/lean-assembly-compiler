/- **`Nat` as limbs** (opt-in, `Testing/notes/S3_REC.md` §7).

A natural number is the list of its base-`2^32` digits, least significant first, each in a 64-bit word, canonical
(no zero top limb): `toLimbs`.  As an S3 value that is a `List UInt64` (`.c 0 []` / `.c 1 [.w limb, rest]`), so the
`Nat` operations are ordinary Lean functions over `List UInt64` (`add`, `sub`, `mul`, `beq`, `blt`, `ble`, …),
compiled through S3 like any other function, each with ONE lemma `op (toLimbs a) (toLimbs b) = toLimbs (a op b)`.

Every operation reads a limb as its low 32 bits (`lv`), so the lemmas need no invariant on their inputs: they hold
for every list (`ofLimbs` reads any list), and the results are canonical (`norm`).  32-bit digits in 64-bit words keep
every intermediate sum and product of two digits inside a word.

The encoding `encNatL` (`Enc Nat` through `toLimbs`) is NOT an instance: `s3_compileL` makes it one for the program it
generates, so the unary `Nat` of `s3_compile` is unchanged. -/
import Compiler.S3.Cert

namespace Proven.S3.Limbs
set_option autoImplicit false

/-! ## the representation (proof-only) -/

/-- the value of a limb: the low 32 bits of its word -/
def lv (x : UInt64) : Nat := x.toNat % 4294967296

/-- the number a limb list stands for (any list) -/
def ofLimbs : List UInt64 → Nat
  | [] => 0
  | x :: l => lv x + 4294967296 * ofLimbs l

/-- the canonical limbs of a number -/
def toLimbs (n : Nat) : List UInt64 :=
  if n = 0 then [] else UInt64.ofNat (n % 4294967296) :: toLimbs (n / 4294967296)
termination_by n
decreasing_by omega

theorem toLimbs_eq (n : Nat) : toLimbs n =
    if n = 0 then [] else UInt64.ofNat (n % 4294967296) :: toLimbs (n / 4294967296) := by
  rw [toLimbs]

@[simp] theorem toLimbs_zero : toLimbs 0 = [] := by rw [toLimbs_eq]; simp

theorem lv_ofNat (n : Nat) : lv (UInt64.ofNat (n % 4294967296)) = n % 4294967296 := by
  unfold lv
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (a := n % 4294967296) (by omega)]
  omega

theorem ofLimbs_toLimbs (n : Nat) : ofLimbs (toLimbs n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [toLimbs_eq]
    by_cases h : n = 0
    · simp [h, ofLimbs]
    · rw [if_neg h, ofLimbs, lv_ofNat, ih _ (by omega)]
      omega

@[simp] theorem lv_and (x : UInt64) : lv (x &&& 4294967295) = lv x := by
  unfold lv
  rw [UInt64.toNat_and, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem and_toNat (x : UInt64) : (x &&& 4294967295).toNat = lv x := by
  unfold lv
  rw [UInt64.toNat_and, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem lv_lt (x : UInt64) : lv x < 4294967296 := Nat.mod_lt _ (by decide)

theorem lv_of_lt (x : UInt64) (h : x.toNat < 4294967296) : lv x = x.toNat := Nat.mod_eq_of_lt h

theorem shr_toNat (x : UInt64) : (x >>> 32).toNat = x.toNat / 4294967296 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl

theorem toNat_lt (x : UInt64) : x.toNat < 18446744073709551616 := x.toNat_lt

/-! ## canonical form -/

/-- the canonical form: every limb masked, zero top limbs dropped -/
def norm : List UInt64 → List UInt64
  | [] => []
  | x :: l => match norm l with
    | [] => if x &&& 4294967295 == 0 then [] else [x &&& 4294967295]
    | y :: r => (x &&& 4294967295) :: y :: r

theorem toLimbs_cons (x : Nat) (n : Nat) (hx : x < 4294967296) (h : ¬ (x = 0 ∧ n = 0)) :
    toLimbs (x + 4294967296 * n) = UInt64.ofNat x :: toLimbs n := by
  rw [toLimbs_eq, if_neg (by omega)]
  congr 2
  · congr 1; omega
  · congr 1; omega

theorem ofNat_lv (x : UInt64) : UInt64.ofNat (lv x) = x &&& 4294967295 := by
  apply UInt64.toNat_inj.mp
  rw [and_toNat, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans (lv_lt x) (by decide))

/-- **`norm` is `toLimbs ∘ ofLimbs`** -/
theorem norm_eq : ∀ l : List UInt64, norm l = toLimbs (ofLimbs l)
  | [] => by simp [norm, ofLimbs]
  | x :: l => by
    have ih := norm_eq l
    simp only [norm, ofLimbs]
    split
    · next h =>
      rw [h] at ih
      have h0 : ofLimbs l = 0 := by
        have := congrArg ofLimbs ih; rw [ofLimbs_toLimbs] at this; simp [ofLimbs] at this; omega
      rw [h0]
      by_cases hx : lv x = 0
      · have : (x &&& 4294967295 == 0) = true := by
          rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [and_toNat, hx]; rfl
        rw [if_pos this, hx]; simp
      · have : (x &&& 4294967295 == 0) = false := by
          rw [beq_eq_false_iff_ne]; intro e; apply hx; have := congrArg UInt64.toNat e; rw [and_toNat] at this
          simpa using this
        rw [if_neg (by simp [this]), Nat.mul_zero, Nat.add_zero, toLimbs_eq, if_neg hx]
        rw [Nat.mod_eq_of_lt (lv_lt x), Nat.div_eq_of_lt (lv_lt x), toLimbs_zero, ofNat_lv]
    · next y r h =>
      rw [h] at ih
      have hn : ofLimbs l ≠ 0 := by intro e; rw [e, toLimbs_zero] at ih; exact nomatch ih
      rw [toLimbs_cons _ _ (lv_lt x) (by omega), ofNat_lv, ← ih]

/-! ## addition -/

/-- `a + b + c` digit by digit (`c` a carry below `2^32`) -/
def addC : List UInt64 → List UInt64 → UInt64 → List UInt64
  | [], [], c => [c]
  | x :: a, [], c => let s := (x &&& 4294967295) + (c &&& 4294967295); (s &&& 4294967295) :: addC a [] (s >>> 32)
  | [], y :: b, c => let s := (y &&& 4294967295) + (c &&& 4294967295); (s &&& 4294967295) :: addC [] b (s >>> 32)
  | x :: a, y :: b, c =>
    let s := (x &&& 4294967295) + (y &&& 4294967295) + (c &&& 4294967295)
    (s &&& 4294967295) :: addC a b (s >>> 32)

theorem add_toNat (x y : UInt64) (h : x.toNat + y.toNat < 18446744073709551616) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

theorem ofLimbs_addC : ∀ (a b : List UInt64) (c : UInt64), ofLimbs (addC a b c) = ofLimbs a + ofLimbs b + lv c
  | [], [], c => by simp [addC, ofLimbs]
  | x :: a, [], c => by
    have hx := lv_lt x; have hc := lv_lt c
    have hs : ((x &&& 4294967295) + (c &&& 4294967295)).toNat = lv x + lv c := by
      rw [add_toNat _ _ (by rw [and_toNat, and_toNat]; omega), and_toNat, and_toNat]
    simp only [addC, ofLimbs]
    rw [ofLimbs_addC a [] _, lv_and]
    unfold lv at *; rw [hs, shr_toNat, hs]; simp only [ofLimbs] at *; omega
  | [], y :: b, c => by
    have hy := lv_lt y; have hc := lv_lt c
    have hs : ((y &&& 4294967295) + (c &&& 4294967295)).toNat = lv y + lv c := by
      rw [add_toNat _ _ (by rw [and_toNat, and_toNat]; omega), and_toNat, and_toNat]
    simp only [addC, ofLimbs]
    rw [ofLimbs_addC [] b _, lv_and]
    unfold lv at *; rw [hs, shr_toNat, hs]; simp only [ofLimbs] at *; omega
  | x :: a, y :: b, c => by
    have hx := lv_lt x; have hy := lv_lt y; have hc := lv_lt c
    have hs : ((x &&& 4294967295) + (y &&& 4294967295) + (c &&& 4294967295)).toNat = lv x + lv y + lv c := by
      rw [add_toNat _ _ (by rw [add_toNat _ _ (by rw [and_toNat, and_toNat]; omega), and_toNat, and_toNat, and_toNat]; omega),
        add_toNat _ _ (by rw [and_toNat, and_toNat]; omega), and_toNat, and_toNat, and_toNat]
    simp only [addC, ofLimbs]
    rw [ofLimbs_addC a b _, lv_and]
    unfold lv at *; rw [hs, shr_toNat, hs]; omega

/-- **`Nat.add`** on limbs -/
def add (a b : List UInt64) : List UInt64 := norm (addC a b 0)

theorem add_eq (a b : List UInt64) : add a b = toLimbs (ofLimbs a + ofLimbs b) := by
  rw [add, norm_eq, ofLimbs_addC]; rfl

theorem add_toLimbs (a b : Nat) : add (toLimbs a) (toLimbs b) = toLimbs (a + b) := by
  rw [add_eq, ofLimbs_toLimbs, ofLimbs_toLimbs]

/-! ## comparisons -/

/-- `omega` after `Bool` equations are propositions -/
macro "bomega" : tactic => `(tactic| ((try rw [Bool.eq_iff_iff]) <;> (try simp only [Bool.or_eq_true, Bool.and_eq_true,
  decide_eq_true_eq]) <;> omega))

/-- the order of the numbers: `0` equal, `1` less, `2` greater (the high digits decide, so the recursive call
comes first) -/
def cmpC : List UInt64 → List UInt64 → UInt64
  | [], [] => 0
  | x :: a, [] => let r := cmpC a []; if r == 0 then (if (x &&& 4294967295) == 0 then 0 else 2) else r
  | [], y :: b => let r := cmpC [] b; if r == 0 then (if (y &&& 4294967295) == 0 then 0 else 1) else r
  | x :: a, y :: b =>
    let r := cmpC a b
    if r == 0 then
      (if (x &&& 4294967295) < (y &&& 4294967295) then 1 else if (y &&& 4294967295) < (x &&& 4294967295) then 2 else 0)
    else r

theorem and_beq (x y : UInt64) : ((x &&& 4294967295) == (y &&& 4294967295)) = decide (lv x = lv y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, and_toNat, and_toNat]

theorem and_lt (x y : UInt64) : ((x &&& 4294967295) < (y &&& 4294967295)) ↔ lv x < lv y := by
  rw [UInt64.lt_iff_toNat_lt, and_toNat, and_toNat]

theorem and_beq0 (x : UInt64) : ((x &&& 4294967295) == 0) = decide (lv x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, and_toNat]; rfl

theorem lt0_and (y : UInt64) : (0 < (y &&& 4294967295)) ↔ 0 < lv y := by
  rw [UInt64.lt_iff_toNat_lt, and_toNat]; rfl

/-- close an equation of `if`s over words `0`/`1`/`2` by the order facts -/
macro "cmp_close" : tactic => `(tactic| (repeat' split) <;> (try simp only [beq_iff_eq, decide_eq_true_eq] at *) <;>
  first | rfl | (exfalso; omega) | (simp at * <;> omega) | (exfalso; simp at * <;> omega))

theorem cmpC_eq : ∀ (a b : List UInt64),
    cmpC a b = if ofLimbs a < ofLimbs b then 1 else if ofLimbs a = ofLimbs b then 0 else 2
  | [], [] => by simp [cmpC, ofLimbs]
  | x :: a, [] => by
    rw [cmpC, cmpC_eq a [], and_beq0]
    have := lv_lt x
    simp only [ofLimbs] at *
    cmp_close
  | [], y :: b => by
    rw [cmpC, cmpC_eq [] b, and_beq0]
    have := lv_lt y
    simp only [ofLimbs] at *
    cmp_close
  | x :: a, y :: b => by
    rw [cmpC, cmpC_eq a b]
    have := lv_lt x; have := lv_lt y
    simp only [ofLimbs, and_lt] at *
    cmp_close

/-- **`Nat.blt`** on limbs -/
def blt (a b : List UInt64) : Bool := cmpC a b == 1
/-- **`Nat.ble`** on limbs -/
def ble (a b : List UInt64) : Bool := !(cmpC a b == 2)

theorem blt_eq (a b : List UInt64) : blt a b = decide (ofLimbs a < ofLimbs b) := by
  rw [blt, cmpC_eq]; by_cases h1 : ofLimbs a < ofLimbs b <;> simp [h1]; split <;> decide

theorem blt_toLimbs (a b : Nat) : blt (toLimbs a) (toLimbs b) = Nat.blt a b := by
  rw [blt_eq, ofLimbs_toLimbs, ofLimbs_toLimbs, Bool.eq_iff_iff, Nat.blt_eq]; simp

theorem ble_toLimbs (a b : Nat) : ble (toLimbs a) (toLimbs b) = Nat.ble a b := by
  rw [ble, cmpC_eq, ofLimbs_toLimbs, ofLimbs_toLimbs, Bool.eq_iff_iff, Nat.ble_eq]
  by_cases h1 : a < b
  · simp [h1]; omega
  by_cases h2 : a = b
  · simp [h2]
  · simp [h1, h2]; omega

/-- equality of the numbers -/
def eqC : List UInt64 → List UInt64 → Bool
  | [], [] => true
  | x :: a, [] => (x &&& 4294967295) == 0 && eqC a []
  | [], y :: b => (y &&& 4294967295) == 0 && eqC [] b
  | x :: a, y :: b => (x &&& 4294967295) == (y &&& 4294967295) && eqC a b

theorem eqC_eq : ∀ (a b : List UInt64), eqC a b = decide (ofLimbs a = ofLimbs b)
  | [], [] => by simp [eqC, ofLimbs]
  | x :: a, [] => by
    rw [eqC, eqC_eq a [], and_beq0]; have := lv_lt x; simp [ofLimbs] <;> bomega
  | [], y :: b => by
    rw [eqC, eqC_eq [] b, and_beq0]; have := lv_lt y; simp [ofLimbs] <;> bomega
  | x :: a, y :: b => by
    rw [eqC, eqC_eq a b, and_beq]; have := lv_lt x; have := lv_lt y; simp [ofLimbs] <;> bomega

/-- **`Nat.beq`** on limbs -/
def beq (a b : List UInt64) : Bool := eqC a b

theorem beq_toLimbs (a b : Nat) : beq (toLimbs a) (toLimbs b) = Nat.beq a b := by
  rw [beq, eqC_eq, ofLimbs_toLimbs, ofLimbs_toLimbs, Bool.eq_iff_iff, Nat.beq_eq]; simp

/-! ## subtraction -/

/-- `a - b - c` digit by digit (`c` a borrow, `0` or `1`), when it is not negative -/
def subC : List UInt64 → List UInt64 → UInt64 → List UInt64
  | [], [], _ => []
  | x :: a, [], c =>
    let d := (x &&& 4294967295) + 4294967296 - (c &&& 1)
    (d &&& 4294967295) :: subC a [] ((d >>> 32) ^^^ 1)
  | [], y :: b, c =>
    let d := 4294967296 - (y &&& 4294967295) - (c &&& 1)
    (d &&& 4294967295) :: subC [] b ((d >>> 32) ^^^ 1)
  | x :: a, y :: b, c =>
    let d := (x &&& 4294967295) + 4294967296 - (y &&& 4294967295) - (c &&& 1)
    (d &&& 4294967295) :: subC a b ((d >>> 32) ^^^ 1)

theorem sub_toNat (x y : UInt64) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)

theorem and1_toNat (c : UInt64) : (c &&& 1).toNat = c.toNat % 2 := by
  rw [UInt64.toNat_and, show (1 : UInt64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- one digit of a subtraction: `d = lx + 2^32 - ly - c`, its digit and the next borrow -/
theorem subDigit (lx ly c : UInt64) (hx : lx.toNat < 4294967296) (hy : ly.toNat < 4294967296) (hc : c.toNat < 2) :
    (lx + 4294967296 - ly - c).toNat = lx.toNat + 4294967296 - ly.toNat - c.toNat ∧
    ((lx + 4294967296 - ly - c) >>> 32 ^^^ 1).toNat % 2 =
      (if ly.toNat + c.toNat ≤ lx.toNat then 0 else 1) := by
  have h1 : (lx + 4294967296).toNat = lx.toNat + 4294967296 := add_toNat _ _ (by simp; omega)
  have h2 : (lx + 4294967296 - ly).toNat = lx.toNat + 4294967296 - ly.toNat := by
    rw [sub_toNat _ _ (by omega), h1]
  have h3 : (lx + 4294967296 - ly - c).toNat = lx.toNat + 4294967296 - ly.toNat - c.toNat := by
    rw [sub_toNat _ _ (by omega), h2]
  refine ⟨h3, ?_⟩
  rw [UInt64.toNat_xor, shr_toNat, h3]
  show (_ ^^^ 1) % 2 = _
  have hq : (lx.toNat + 4294967296 - ly.toNat - c.toNat) / 4294967296 = (if ly.toNat + c.toNat ≤ lx.toNat then 1 else 0) := by
    split <;> omega
  rw [hq]; split <;> rfl

def hd : List UInt64 → UInt64
  | [] => 0
  | x :: _ => x
def tl : List UInt64 → List UInt64
  | [] => []
  | _ :: l => l

theorem ofLimbs_hd_tl (l : List UInt64) : ofLimbs l = lv (hd l) + 4294967296 * ofLimbs (tl l) := by
  cases l <;> simp [ofLimbs, hd, tl, lv]

theorem tl_len (n : Nat) (a b : List UInt64) (hn : a.length + b.length ≤ n + 1) (h : ¬ (a = [] ∧ b = [])) :
    (tl a).length + (tl b).length ≤ n := by
  cases a <;> cases b <;> simp_all [tl] <;> omega

theorem subC_step (a b : List UInt64) (c : UInt64) (h : ¬ (a = [] ∧ b = [])) :
    subC a b c = (((hd a &&& 4294967295) + 4294967296 - (hd b &&& 4294967295) - (c &&& 1)) &&& 4294967295) ::
      subC (tl a) (tl b) (((hd a &&& 4294967295) + 4294967296 - (hd b &&& 4294967295) - (c &&& 1)) >>> 32 ^^^ 1) := by
  match a, b with
  | [], [] => simp at h
  | x :: a, [] => simp [subC, hd, tl]
  | [], y :: b => simp [subC, hd, tl]
  | x :: a, y :: b => simp [subC, hd, tl]

theorem ofLimbs_subC (n : Nat) : ∀ (a b : List UInt64) (c : UInt64), a.length + b.length ≤ n →
    ofLimbs b + c.toNat % 2 ≤ ofLimbs a → ofLimbs (subC a b c) = ofLimbs a - ofLimbs b - c.toNat % 2 := by
  induction n with
  | zero =>
    intro a b c hn h
    cases a <;> cases b <;> simp [subC, ofLimbs] at * <;> try omega
  | succ n ih =>
    intro a b c hn h
    by_cases hab : a = [] ∧ b = []
    · obtain ⟨rfl, rfl⟩ := hab; simp only [subC, ofLimbs] at *; omega
    rw [subC_step a b c hab]
    have hx := lv_lt (hd a); have hy := lv_lt (hd b)
    have hc : (c &&& 1).toNat < 2 := by rw [and1_toNat]; omega
    obtain ⟨hd', hb⟩ := subDigit (hd a &&& 4294967295) (hd b &&& 4294967295) (c &&& 1) (by rw [and_toNat]; omega)
      (by rw [and_toNat]; omega) hc
    rw [and_toNat, and_toNat, and1_toNat] at hd' hb
    have hl := tl_len n a b hn hab
    rw [ofLimbs_hd_tl a, ofLimbs_hd_tl b] at h
    rw [ofLimbs, ih _ _ _ hl (by rw [hb]; split <;> omega), ofLimbs_hd_tl a, ofLimbs_hd_tl b, hb]
    rw [lv_and]; unfold lv at *; rw [hd']; split <;> omega

/-! ## multiplication -/

/-- `a * lv y + lv c` digit by digit -/
def mulRow : List UInt64 → UInt64 → UInt64 → List UInt64
  | [], _, c => [c]
  | x :: a, y, c =>
    let s := (x &&& 4294967295) * (y &&& 4294967295) + (c &&& 4294967295)
    (s &&& 4294967295) :: mulRow a y (s >>> 32)

theorem mul_toNat (x y : UInt64) (h : x.toNat * y.toNat < 18446744073709551616) : (x * y).toNat = x.toNat * y.toNat := by
  rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt h

theorem ofLimbs_mulRow : ∀ (a : List UInt64) (y c : UInt64), ofLimbs (mulRow a y c) = ofLimbs a * lv y + lv c
  | [], y, c => by simp [mulRow, ofLimbs, lv]
  | x :: a, y, c => by
    have hx := lv_lt x; have hy := lv_lt y; have hc := lv_lt c
    have hp : lv x * lv y ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    have hs : ((x &&& 4294967295) * (y &&& 4294967295) + (c &&& 4294967295)).toNat = lv x * lv y + lv c := by
      rw [add_toNat _ _ (by rw [mul_toNat _ _ (by rw [and_toNat, and_toNat]; omega), and_toNat, and_toNat, and_toNat]; omega),
        mul_toNat _ _ (by rw [and_toNat, and_toNat]; omega), and_toNat, and_toNat, and_toNat]
    simp only [mulRow, ofLimbs]
    rw [ofLimbs_mulRow a y _, lv_and]
    have e : (lv x + 4294967296 * ofLimbs a) * lv y = lv x * lv y + 4294967296 * (ofLimbs a * lv y) := by
      rw [Nat.add_mul, Nat.mul_assoc]
    rw [e]
    generalize lv x * lv y = p at *
    unfold lv at *; rw [hs, shr_toNat, hs]; omega

/-- `a * b`, one row per digit of `b` -/
def mulL (a : List UInt64) : List UInt64 → List UInt64
  | [] => []
  | y :: b => addC (mulRow a y 0) (0 :: mulL a b) 0

theorem ofLimbs_mulL (a : List UInt64) : ∀ b : List UInt64, ofLimbs (mulL a b) = ofLimbs a * ofLimbs b
  | [] => by simp [mulL, ofLimbs]
  | y :: b => by
    rw [mulL, ofLimbs_addC, ofLimbs_mulRow, ofLimbs, ofLimbs, ofLimbs_mulL a b]
    simp only [lv, UInt64.toNat_zero, Nat.zero_mod, Nat.add_zero, Nat.zero_add]
    rw [Nat.mul_add, Nat.mul_left_comm]

/-- **`Nat.mul`** on limbs -/
def mul (a b : List UInt64) : List UInt64 := norm (mulL a b)

theorem mul_eq (a b : List UInt64) : mul a b = toLimbs (ofLimbs a * ofLimbs b) := by
  rw [mul, norm_eq, ofLimbs_mulL]

theorem mul_toLimbs (a b : Nat) : mul (toLimbs a) (toLimbs b) = toLimbs (a * b) := by
  rw [mul_eq, ofLimbs_toLimbs, ofLimbs_toLimbs]

/-! ## subtraction, truncated -/

/-- **`Nat.sub`** on limbs: `a - b` digit by digit, times `0` when `a < b` (no branch) -/
def sub (a b : List UInt64) : List UInt64 := norm (mulRow (subC a b 0) (1 - (cmpC a b &&& 1)) 0)

theorem sub_eq (a b : List UInt64) : sub a b = toLimbs (ofLimbs a - ofLimbs b) := by
  rw [sub, norm_eq, ofLimbs_mulRow, cmpC_eq]
  congr 1
  simp only [lv, UInt64.toNat_zero, Nat.zero_mod, Nat.add_zero]
  by_cases h : ofLimbs a < ofLimbs b
  · rw [if_pos h]; simp; omega
  · rw [if_neg h, ofLimbs_subC _ _ _ _ (Nat.le_refl _) (by simp; omega)]
    split <;> simp [show ((1 : UInt64) - (2 &&& 1)) = 1 from by decide]

theorem sub_toLimbs (a b : Nat) : sub (toLimbs a) (toLimbs b) = toLimbs (a - b) := by
  rw [sub_eq, ofLimbs_toLimbs, ofLimbs_toLimbs]

/-! ## division -/

/-- `2 a + c` (`c` read as a bit) -/
def shl1 : List UInt64 → UInt64 → List UInt64
  | [], c => if (c &&& 1) == 0 then [] else [1]
  | x :: a, c =>
    let s := (x &&& 4294967295) + (x &&& 4294967295) + (c &&& 1)
    (s &&& 4294967295) :: shl1 a (s >>> 32)

theorem and1_beq0 (c : UInt64) : ((c &&& 1) == 0) = decide (c.toNat % 2 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, and1_toNat]; rfl

theorem ofLimbs_shl1 : ∀ (a : List UInt64) (c : UInt64), ofLimbs (shl1 a c) = 2 * ofLimbs a + c.toNat % 2
  | [], c => by
    simp only [shl1, and1_beq0]
    by_cases h : c.toNat % 2 = 0 <;> simp [h, ofLimbs, lv] <;> omega
  | x :: a, c => by
    have hx := lv_lt x
    have hs : ((x &&& 4294967295) + (x &&& 4294967295) + (c &&& 1)).toNat = lv x + lv x + c.toNat % 2 := by
      rw [add_toNat _ _ (by rw [add_toNat _ _ (by rw [and_toNat]; omega), and_toNat, and1_toNat]; omega),
        add_toNat _ _ (by rw [and_toNat]; omega), and_toNat, and1_toNat]
    simp only [shl1, ofLimbs]
    rw [ofLimbs_shl1 a _, lv_and]
    unfold lv at *; rw [hs, shr_toNat, hs]; omega

/-- one step of the long division: `r1 - b` and bit `1` when `r1 ≥ b`, else `r1` and bit `0` (no branch: `b` is
subtracted times the bit) -/
def stepR (r1 b : List UInt64) : List UInt64 × UInt64 :=
  let lt := cmpC r1 b &&& 1
  (norm (subC r1 (mulRow b (1 - lt) 0) 0), 1 - lt)

theorem ofLimbs_norm (l : List UInt64) : ofLimbs (norm l) = ofLimbs l := by
  rw [norm_eq, ofLimbs_toLimbs]

theorem stepR_spec (r1 b : List UInt64) :
    ofLimbs (stepR r1 b).1 = (if ofLimbs r1 < ofLimbs b then ofLimbs r1 else ofLimbs r1 - ofLimbs b) ∧
    (stepR r1 b).2.toNat = (if ofLimbs r1 < ofLimbs b then 0 else 1) := by
  simp only [stepR, ofLimbs_norm, cmpC_eq]
  by_cases h : ofLimbs r1 < ofLimbs b
  · simp only [if_pos h, show (1 : UInt64) - (1 &&& 1) = 0 from by decide]
    have hm := ofLimbs_mulRow b 0 0
    simp only [lv, UInt64.toNat_zero, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at hm
    rw [ofLimbs_subC _ r1 _ 0 (Nat.le_refl _) (by rw [hm]; simp), hm]; simp
  · simp only [if_neg h]
    have e : ∀ c : UInt64, c = (if ofLimbs r1 = ofLimbs b then 0 else 2) → 1 - (c &&& 1) = 1 := by
      intro c hc; rw [hc]; split <;> decide
    rw [e _ rfl]
    have hm := ofLimbs_mulRow b 1 0
    simp only [lv, UInt64.toNat_zero, Nat.zero_mod, Nat.add_zero] at hm
    rw [show (1 : UInt64).toNat % 4294967296 = 1 from rfl, Nat.mul_one] at hm
    rw [ofLimbs_subC _ r1 _ 0 (Nat.le_refl _) (by rw [hm]; simp; omega), hm]; simp

/-- the 32 bits of a digit, the top bit of `y` first, into the remainder `r`; the quotient bits after `q` -/
def bitsLoop (y k : UInt64) (r b : List UInt64) (q : UInt64) : List UInt64 × UInt64 :=
  if _h : k = 0 then (r, q) else
  match stepR (shl1 r (y >>> 31)) b with
  | (r', c) => bitsLoop ((y <<< 1) &&& 4294967295) (k - 1) r' b (q + q + c)
termination_by k.toNat
decreasing_by
  have hk : k.toNat ≠ 0 := fun e => _h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

theorem shl_toNat (y : UInt64) :
    ((y <<< 1) &&& 4294967295).toNat = 2 * (y.toNat % 2147483648) := by
  rw [and_toNat]; unfold lv
  rw [UInt64.toNat_shiftLeft]; show y.toNat <<< 1 % 2 ^ 64 % 4294967296 = _
  rw [Nat.shiftLeft_eq]; omega

theorem shr31_toNat (y : UInt64) (_hy : y.toNat < 4294967296) : (y >>> 31).toNat % 2 = y.toNat / 2147483648 := by
  rw [UInt64.toNat_shiftRight]; show y.toNat >>> (31 % 64) % 2 = _
  rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.reduceMod, Nat.reducePow]; omega

/-- **the bit loop**: with `N = r * 2^n + (the top n of the 32 bits of y)`, the remainder `N % b` and the quotient
bits `q * 2^n + N / b` -/
theorem bitsLoop_spec (b : List UInt64) (hb : 0 < ofLimbs b) : ∀ (n : Nat) (y k : UInt64) (r : List UInt64)
    (q : UInt64), k.toNat = n → n ≤ 32 → y.toNat < 4294967296 → ofLimbs r < ofLimbs b → q.toNat < 2 ^ (32 - n) →
    ofLimbs (bitsLoop y k r b q).1 = (ofLimbs r * 2 ^ n + y.toNat / 2 ^ (32 - n)) % ofLimbs b ∧
    (bitsLoop y k r b q).2.toNat = q.toNat * 2 ^ n + (ofLimbs r * 2 ^ n + y.toNat / 2 ^ (32 - n)) / ofLimbs b := by
  intro n
  induction n with
  | zero =>
    intro y k r q hk _ hy hr _
    have : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    rw [bitsLoop, dif_pos this]
    simp only [Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show y.toNat < 2 ^ 32 from hy),
      Nat.add_zero, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr]
    simp
  | succ n ih =>
    intro y k r q hk hn hy hr hq
    have hk0 : k ≠ 0 := fun e => by rw [e] at hk; simp at hk
    have hk1 : (k - 1).toNat = n := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    rw [bitsLoop, dif_neg hk0]
    have hR1 := ofLimbs_shl1 r (y >>> 31)
    rw [shr31_toNat y hy] at hR1
    obtain ⟨hs1, hs2⟩ := stepR_spec (shl1 r (y >>> 31)) b
    generalize hst : stepR (shl1 r (y >>> 31)) b = st at *
    obtain ⟨r', c⟩ := st
    simp only at hs1 hs2 ⊢
    generalize ofLimbs (shl1 r (y >>> 31)) = R1 at *
    have hy' := shl_toNat y
    generalize hP : 2 ^ n = P at *
    have hP0 : 0 < P := by rw [← hP]; exact Nat.two_pow_pos _
    have h2P : 2 ^ (n + 1) = 2 * P := by rw [Nat.pow_succ, hP, Nat.mul_comm]
    have hQ : 2 ^ (32 - n) = 2 * 2 ^ (31 - n) := by
      rw [show 32 - n = (31 - n) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have h31 : 2147483648 = 2 ^ (31 - n) * P := by
      rw [← hP, ← Nat.pow_add, show 31 - n + n = 31 by omega]
    have hdiv : y.toNat / 2 ^ (32 - (n + 1)) = (y.toNat / 2147483648) * P + (y.toNat % 2147483648) / 2 ^ (31 - n) := by
      rw [show 32 - (n + 1) = 31 - n by omega]
      have e : y.toNat = (y.toNat % 2147483648) + 2 ^ (31 - n) * (P * (y.toNat / 2147483648)) := by
        rw [← Nat.mul_assoc, ← h31]; omega
      conv => lhs; rw [e]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.mul_comm P]; (try omega)
    have hy2 : ((y <<< 1) &&& 4294967295).toNat / 2 ^ (32 - n) = (y.toNat % 2147483648) / 2 ^ (31 - n) := by
      rw [hy', hQ, Nat.mul_div_mul_left _ _ (by decide)]
    have hN : ofLimbs r * (2 * P) + y.toNat / 2 ^ (32 - (n + 1)) = R1 * P + (y.toNat % 2147483648) / 2 ^ (31 - n) := by
      rw [hdiv, hR1]; grind
    have hlt2 : (y.toNat % 2147483648) / 2 ^ (31 - n) < P := by
      apply Nat.div_lt_of_lt_mul; rw [← h31]; omega
    have hq2 : q.toNat < 2 ^ (32 - n - 1) := by rw [show 32 - (n + 1) = 32 - n - 1 by omega] at hq; exact hq
    have hpow : 2 ^ (32 - n) = 2 * 2 ^ (32 - n - 1) := by
      have e : 32 - n = (32 - n - 1) + 1 := by omega
      conv => lhs; rw [e]
      rw [Nat.pow_succ, Nat.mul_comm]
    have hc : c.toNat ≤ 1 := by rw [hs2]; split <;> omega
    have hqq : (q + q + c).toNat = 2 * q.toNat + c.toNat := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 32 - n - 1 ≤ 31 by omega)
      rw [add_toNat _ _ (by rw [add_toNat _ _ (by omega)]; omega), add_toNat _ _ (by omega)]; omega
    have hr' : ofLimbs r' < ofLimbs b := by rw [hs1]; split <;> omega
    obtain ⟨h1, h2⟩ := ih ((y <<< 1) &&& 4294967295) (k - 1) r' (q + q + c) hk1 (by omega)
      (by rw [hy']; omega) hr' (by rw [hqq]; omega)
    rw [hy2] at h1 h2
    rw [h2P, hN, h1, h2, hqq, hs1, hs2]
    by_cases hlt : R1 < ofLimbs b
    · simp only [if_pos hlt]; refine ⟨?_, ?_⟩ <;> grind
    · simp only [if_neg hlt]
      have hX : R1 * P + y.toNat % 2147483648 / 2 ^ (31 - n) =
          (R1 - ofLimbs b) * P + y.toNat % 2147483648 / 2 ^ (31 - n) + ofLimbs b * P := by
        rw [Nat.sub_mul]; have : ofLimbs b * P ≤ R1 * P := Nat.mul_le_mul_right _ (by omega); omega
      rw [hX, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hb]
      refine ⟨?_, ?_⟩ <;> grind

theorem bitsLoop_zero (b : List UInt64) (hb : ofLimbs b = 0) : ∀ (n : Nat) (y k : UInt64)
    (r : List UInt64) (q : UInt64), k.toNat = n → n ≤ 32 → y.toNat < 4294967296 →
    ofLimbs (bitsLoop y k r b q).1 = ofLimbs r * 2 ^ n + y.toNat / 2 ^ (32 - n) := by
  intro n
  induction n with
  | zero =>
    intro y k r q hk _ hy
    have : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    rw [bitsLoop, dif_pos this]
    simp [Nat.div_eq_of_lt (show y.toNat < 2 ^ 32 from hy)]
  | succ n ih =>
    intro y k r q hk hn hy
    have hk0 : k ≠ 0 := fun e => by rw [e] at hk; simp at hk
    have hk1 : (k - 1).toNat = n := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    rw [bitsLoop, dif_neg hk0]
    have hR1 := ofLimbs_shl1 r (y >>> 31)
    rw [shr31_toNat y hy] at hR1
    obtain ⟨hs1, _⟩ := stepR_spec (shl1 r (y >>> 31)) b
    generalize hst : stepR (shl1 r (y >>> 31)) b = st at *
    obtain ⟨r', c⟩ := st
    simp only at hs1 ⊢
    rw [hb] at hs1; simp only [Nat.not_lt_zero, if_false, Nat.sub_zero] at hs1
    have hy' := shl_toNat y
    rw [ih _ _ _ _ hk1 (by omega) (by rw [hy']; omega), hs1, hR1]
    generalize hP : 2 ^ n = P at *
    have hP0 : 0 < P := by rw [← hP]; exact Nat.two_pow_pos _
    have h2P : 2 ^ (n + 1) = 2 * P := by rw [Nat.pow_succ, hP, Nat.mul_comm]
    have hQ : 2 ^ (32 - n) = 2 * 2 ^ (31 - n) := by
      rw [show 32 - n = (31 - n) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have h31 : 2147483648 = 2 ^ (31 - n) * P := by
      rw [← hP, ← Nat.pow_add, show 31 - n + n = 31 by omega]
    have hdiv : y.toNat / 2 ^ (32 - (n + 1)) = (y.toNat / 2147483648) * P + (y.toNat % 2147483648) / 2 ^ (31 - n) := by
      rw [show 32 - (n + 1) = 31 - n by omega]
      have e : y.toNat = (y.toNat % 2147483648) + 2 ^ (31 - n) * (P * (y.toNat / 2147483648)) := by
        rw [← Nat.mul_assoc, ← h31]; omega
      conv => lhs; rw [e]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.mul_comm P]; (try omega)
    rw [hy', hQ, Nat.mul_div_mul_left _ _ (by decide), h2P, hdiv]
    grind

/-- quotient and remainder by `b`, the high digits of `a` first -/
def divL (b : List UInt64) : List UInt64 → List UInt64 × List UInt64
  | [] => ([], [])
  | x :: a => match divL b a with
    | (q, r) => match bitsLoop (x &&& 4294967295) 32 r b 0 with
      | (r', qx) => (qx :: q, r')

theorem divL_spec (b : List UInt64) (hb : 0 < ofLimbs b) : ∀ a : List UInt64,
    ofLimbs (divL b a).1 = ofLimbs a / ofLimbs b ∧ ofLimbs (divL b a).2 = ofLimbs a % ofLimbs b
  | [] => by simp [divL, ofLimbs]
  | x :: a => by
    obtain ⟨ih1, ih2⟩ := divL_spec b hb a
    simp only [divL]
    generalize hd : divL b a = d at *
    obtain ⟨q, r⟩ := d
    simp only at ih1 ih2 ⊢
    have hr : ofLimbs r < ofLimbs b := by rw [ih2]; exact Nat.mod_lt _ hb
    obtain ⟨h1, h2⟩ := bitsLoop_spec b hb 32 (x &&& 4294967295) 32 r 0 rfl (by omega)
      (by rw [and_toNat]; exact lv_lt x) hr (by decide)
    generalize hl : bitsLoop (x &&& 4294967295) 32 r b 0 = res at *
    obtain ⟨r', qx⟩ := res
    simp only at h1 h2 ⊢
    simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add] at h2
    have hlx : (x &&& 4294967295).toNat / 2 ^ (32 - 32) = lv x := by rw [and_toNat]; simp
    rw [hlx] at h1 h2
    have hN : ofLimbs r * 2 ^ 32 + lv x < ofLimbs b * 2 ^ 32 := by
      have := Nat.mul_le_mul_right (2 ^ 32) (show ofLimbs r + 1 ≤ ofLimbs b by omega)
      have := lv_lt x; omega
    have hq : qx.toNat < 4294967296 := by
      rw [h2]; exact Nat.div_lt_of_lt_mul (by simp only [Nat.reducePow] at hN ⊢; omega)
    have hA : lv x + 4294967296 * ofLimbs a =
        (ofLimbs r * 2 ^ 32 + lv x) + ofLimbs b * (4294967296 * (ofLimbs a / ofLimbs b)) := by
      rw [ih2]; have := Nat.div_add_mod (ofLimbs a) (ofLimbs b); grind
    simp only [ofLimbs]
    rw [hA, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hb, ← h1, lv_of_lt _ hq, h2, ih1]
    exact ⟨by omega, rfl⟩

theorem divL_zero (b : List UInt64) (hb : ofLimbs b = 0) : ∀ a : List UInt64, ofLimbs (divL b a).2 = ofLimbs a
  | [] => by simp [divL, ofLimbs]
  | x :: a => by
    have ih := divL_zero b hb a
    simp only [divL]
    generalize hd : divL b a = d at *
    obtain ⟨q, r⟩ := d
    simp only at ih ⊢
    have h1 := bitsLoop_zero b hb 32 (x &&& 4294967295) 32 r 0 rfl (by omega) (by rw [and_toNat]; exact lv_lt x)
    generalize hl : bitsLoop (x &&& 4294967295) 32 r b 0 = res at *
    obtain ⟨r', qx⟩ := res
    simp only at h1 ⊢
    rw [h1, ih, and_toNat]; simp only [ofLimbs]; simp; omega

/-- **`Nat.div`** on limbs (`a / 0 = 0`: the quotient times `0`) -/
def div (a b : List UInt64) : List UInt64 := norm (mulRow (divL b a).1 (cmpC b [] >>> 1) 0)

/-- **`Nat.mod`** on limbs (`a % 0 = a`) -/
def mod (a b : List UInt64) : List UInt64 := norm (divL b a).2

theorem div_eq (a b : List UInt64) : div a b = toLimbs (ofLimbs a / ofLimbs b) := by
  rw [div, norm_eq, ofLimbs_mulRow, cmpC_eq]
  congr 1
  simp only [ofLimbs, Nat.not_lt_zero, if_false, lv, UInt64.toNat_zero, Nat.zero_mod, Nat.add_zero]
  by_cases hb : ofLimbs b = 0
  · rw [if_pos hb, hb]; simp
  · rw [if_neg hb, (divL_spec b (by omega) a).1]; simp

theorem mod_eq (a b : List UInt64) : mod a b = toLimbs (ofLimbs a % ofLimbs b) := by
  rw [mod, norm_eq]
  by_cases hb : ofLimbs b = 0
  · rw [divL_zero b hb, hb, Nat.mod_zero]
  · rw [(divL_spec b (by omega) a).2]

theorem div_toLimbs (a b : Nat) : div (toLimbs a) (toLimbs b) = toLimbs (Nat.div a b) := by
  rw [div_eq, ofLimbs_toLimbs, ofLimbs_toLimbs]; rfl

theorem mod_toLimbs (a b : Nat) : mod (toLimbs a) (toLimbs b) = toLimbs (Nat.mod a b) := by
  rw [mod_eq, ofLimbs_toLimbs, ofLimbs_toLimbs]; rfl

/-- the certificates' normal form of a decremented word (the S3 side computes `k.toBitVec + (2^64 - 1)`) -/
theorem u64_sub_one (k : UInt64) : k - 1 = 18446744073709551615 + k := by
  apply UInt64.toBitVec_inj.mp; simp; rw [BitVec.sub_eq_add_neg, BitVec.add_comm]; rfl

/-- the certificates' normal forms of `Nat.div` / `Nat.mod` (the oracle of a primitive applies the function) -/
theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

/-- the certificates' normal forms of the comparisons (a `Bool` result as data meets `decide`) -/
theorem nat_blt_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq]; simp
theorem nat_ble_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq]; simp
theorem nat_beq_decide (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq]; simp

/-! ## words -/

/-- **`UInt64.toNat`** as limbs -/
def ofWord (x : UInt64) : List UInt64 := norm [x &&& 4294967295, x >>> 32]

theorem ofWord_eq (x : UInt64) : ofWord x = toLimbs x.toNat := by
  rw [ofWord, norm_eq]; congr 1
  simp only [ofLimbs, lv_and]; unfold lv; rw [shr_toNat]; have := x.toNat_lt; omega

/-- **`UInt64.ofNat`** on limbs: the low two digits -/
def toWord : List UInt64 → UInt64
  | [] => 0
  | [x] => x &&& 4294967295
  | x :: y :: _ => (x &&& 4294967295) ||| ((y &&& 4294967295) <<< (32 : UInt64))

theorem toWord_eq (l : List UInt64) : toWord l = UInt64.ofNat (ofLimbs l) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat']
  match l with
  | [] => rfl
  | [x] => rw [toWord, and_toNat]; simp only [ofLimbs]; have := lv_lt x; omega
  | x :: y :: l =>
    rw [toWord, UInt64.toNat_or, UInt64.toNat_shiftLeft, and_toNat, and_toNat]
    simp only [ofLimbs]
    have hx := lv_lt x; have hy := lv_lt y
    show lv x ||| (lv y <<< (32 % 64)) % 2 ^ 64 = _
    rw [show 32 % 64 = 32 from rfl, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    rw [show lv y * 2 ^ 32 = 2 ^ 32 * lv y by rw [Nat.mul_comm], Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt (i := 32) (show lv x < 2 ^ 32 from hx)]
    omega

theorem toWord_toLimbs (n : Nat) : toWord (toLimbs n) = UInt64.ofNat n := by
  rw [toWord_eq, ofLimbs_toLimbs]

/-! ## bitwise operations -/

/-- a bitwise operation of two numbers, one digit at a time -/
theorem bitwise_digit (op : Nat → Nat → Nat) (g : Bool → Bool → Bool)
    (hop : ∀ x y i, Nat.testBit (op x y) i = g (Nat.testBit x i) (Nat.testBit y i)) (A B lx ly : Nat)
    (hx : lx < 2 ^ 32) (hy : ly < 2 ^ 32) (hxy : op lx ly < 2 ^ 32) :
    op (lx + 4294967296 * A) (ly + 4294967296 * B) = op lx ly + 4294967296 * op A B := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [show 4294967296 = 2 ^ 32 from rfl, Nat.add_comm lx, Nat.add_comm ly, Nat.add_comm (op lx ly)]
  rw [hop, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy, Nat.testBit_two_pow_mul_add _ hxy, hop, hop]
  split <;> rfl

/-- `a &&& b` digit by digit -/
def landC : List UInt64 → List UInt64 → List UInt64
  | x :: a, y :: b => ((x &&& y) &&& 4294967295) :: landC a b
  | _, _ => []

/-- `a ||| b` digit by digit -/
def lorC : List UInt64 → List UInt64 → List UInt64
  | [], [] => []
  | x :: a, [] => (x &&& 4294967295) :: lorC a []
  | [], y :: b => (y &&& 4294967295) :: lorC [] b
  | x :: a, y :: b => ((x ||| y) &&& 4294967295) :: lorC a b

/-- `a ^^^ b` digit by digit -/
def xorC : List UInt64 → List UInt64 → List UInt64
  | [], [] => []
  | x :: a, [] => (x &&& 4294967295) :: xorC a []
  | [], y :: b => (y &&& 4294967295) :: xorC [] b
  | x :: a, y :: b => ((x ^^^ y) &&& 4294967295) :: xorC a b

theorem lv_and2 (x y : UInt64) : lv ((x &&& y) &&& 4294967295) = lv x &&& lv y := by
  rw [lv_and]; unfold lv; rw [UInt64.toNat_and]
  exact Nat.and_mod_two_pow (n := 32)
theorem lv_or2 (x y : UInt64) : lv ((x ||| y) &&& 4294967295) = lv x ||| lv y := by
  rw [lv_and]; unfold lv; rw [UInt64.toNat_or]
  exact Nat.or_mod_two_pow (n := 32)
theorem lv_xor2 (x y : UInt64) : lv ((x ^^^ y) &&& 4294967295) = lv x ^^^ lv y := by
  rw [lv_and]; unfold lv; rw [UInt64.toNat_xor]
  exact Nat.xor_mod_two_pow (n := 32)

theorem ofLimbs_landC : ∀ a b : List UInt64, ofLimbs (landC a b) = ofLimbs a &&& ofLimbs b
  | x :: a, y :: b => by
    rw [landC, ofLimbs, ofLimbs, ofLimbs, ofLimbs_landC a b, lv_and2,
      bitwise_digit (· &&& ·) (· && ·) Nat.testBit_and _ _ _ _ (lv_lt x) (lv_lt y)
        (Nat.and_lt_two_pow _ (lv_lt y))]
  | [], _ => by simp [landC, ofLimbs]
  | _ :: _, [] => by simp [landC, ofLimbs]

theorem ofLimbs_lorC : ∀ a b : List UInt64, ofLimbs (lorC a b) = ofLimbs a ||| ofLimbs b
  | [], [] => by simp [lorC, ofLimbs]
  | x :: a, [] => by
    rw [lorC, ofLimbs, ofLimbs, ofLimbs_lorC a [], lv_and]; simp [ofLimbs]
  | [], y :: b => by
    rw [lorC, ofLimbs, ofLimbs, ofLimbs_lorC [] b, lv_and]; simp [ofLimbs]
  | x :: a, y :: b => by
    rw [lorC, ofLimbs, ofLimbs, ofLimbs, ofLimbs_lorC a b, lv_or2,
      bitwise_digit (· ||| ·) (· || ·) Nat.testBit_or _ _ _ _ (lv_lt x) (lv_lt y)
        (Nat.or_lt_two_pow (lv_lt x) (lv_lt y))]

theorem ofLimbs_xorC : ∀ a b : List UInt64, ofLimbs (xorC a b) = ofLimbs a ^^^ ofLimbs b
  | [], [] => by simp [xorC, ofLimbs]
  | x :: a, [] => by
    rw [xorC, ofLimbs, ofLimbs, ofLimbs_xorC a [], lv_and]; simp [ofLimbs]
  | [], y :: b => by
    rw [xorC, ofLimbs, ofLimbs, ofLimbs_xorC [] b, lv_and]; simp [ofLimbs]
  | x :: a, y :: b => by
    rw [xorC, ofLimbs, ofLimbs, ofLimbs, ofLimbs_xorC a b, lv_xor2,
      bitwise_digit (· ^^^ ·) (· ^^ ·) Nat.testBit_xor _ _ _ _ (lv_lt x) (lv_lt y)
        (Nat.xor_lt_two_pow (lv_lt x) (lv_lt y))]

/-- **`Nat.land`** on limbs -/
def land (a b : List UInt64) : List UInt64 := norm (landC a b)
/-- **`Nat.lor`** on limbs -/
def lor (a b : List UInt64) : List UInt64 := norm (lorC a b)
/-- **`Nat.xor`** on limbs -/
def xor (a b : List UInt64) : List UInt64 := norm (xorC a b)

theorem land_toLimbs (a b : Nat) : land (toLimbs a) (toLimbs b) = toLimbs (Nat.land a b) := by
  rw [land, norm_eq, ofLimbs_landC, ofLimbs_toLimbs, ofLimbs_toLimbs]; rfl
theorem lor_toLimbs (a b : Nat) : lor (toLimbs a) (toLimbs b) = toLimbs (Nat.lor a b) := by
  rw [lor, norm_eq, ofLimbs_lorC, ofLimbs_toLimbs, ofLimbs_toLimbs]; rfl
theorem xor_toLimbs (a b : Nat) : xor (toLimbs a) (toLimbs b) = toLimbs (Nat.xor a b) := by
  rw [xor, norm_eq, ofLimbs_xorC, ofLimbs_toLimbs, ofLimbs_toLimbs]; rfl

/-- the certificates' normal forms of the bitwise operations -/
theorem nat_land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem nat_lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem nat_xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

/-! ## `Nat.log2` -/

/-- `Nat.log2` of a word -/
def log2w (x : UInt64) : UInt64 := if h : x ≤ 1 then 0 else log2w (x >>> 1) + 1
termination_by x.toNat
decreasing_by
  rw [UInt64.toNat_shiftRight]; show x.toNat >>> (1 % 64) < _
  rw [Nat.shiftRight_eq_div_pow]; have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h); simp at *; omega

theorem log2w_toNat : ∀ (n : Nat) (x : UInt64), x.toNat = n → (log2w x).toNat = Nat.log2 n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x hx
    rw [log2w, Nat.log2_def]
    by_cases h : x ≤ 1
    · have : x.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp h
      rw [dif_pos h, if_neg (by omega)]; rfl
    · have : 1 < x.toNat := by have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h); simpa using this
      rw [dif_neg h, if_pos (by omega)]
      have hs : (x >>> 1).toNat = n / 2 := by
        rw [UInt64.toNat_shiftRight]; show x.toNat >>> (1 % 64) = _
        rw [Nat.shiftRight_eq_div_pow, hx]
      have ih' := ih (n / 2) (by omega) (x >>> 1) hs
      have hl : Nat.log2 (n / 2) < 64 := by
        by_cases hz : n / 2 = 0
        · rw [hz]; decide
        · exact (Nat.log2_lt hz).mpr (by have := x.toNat_lt; show n / 2 < 18446744073709551616; omega)
      rw [add_toNat _ _ (by rw [ih']; simp; omega), ih']; rfl

/-- `Nat.log2` of canonical limbs: `32 (length - 1) + log2 (top digit)` -/
def log2C : List UInt64 → List UInt64
  | [] => []
  | [x] => ofWord (log2w (x &&& 4294967295))
  | _ :: y :: r => add (log2C (y :: r)) [32]

theorem log2_shift (n : Nat) (h : 4294967296 ≤ n) : Nat.log2 n = Nat.log2 (n / 4294967296) + 32 := by
  have hq : n / 4294967296 ≠ 0 := by omega
  rw [Nat.log2_eq_iff (by omega)]
  have h1 := Nat.log2_self_le hq
  have h2 := @Nat.lt_log2_self (n / 4294967296)
  generalize Nat.log2 (n / 4294967296) = L at *
  have h1' := (Nat.le_div_iff_mul_le (by decide)).mp h1
  have h2' := (Nat.div_lt_iff_lt_mul (by decide)).mp h2
  rw [show L + 32 + 1 = (L + 1) + 32 by omega, Nat.pow_add, Nat.pow_add]
  exact ⟨h1', h2'⟩

theorem log2C_toLimbs (n : Nat) : log2C (toLimbs n) = toLimbs (Nat.log2 n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [log2C]
    by_cases h1 : n < 4294967296
    · rw [toLimbs_eq, if_neg h0, Nat.div_eq_of_lt h1, toLimbs_zero, log2C, ofWord_eq]
      congr 1
      rw [log2w_toNat n _ (by rw [and_toNat]; unfold lv; rw [UInt64.toNat_ofNat']; omega)]
    · have hq := ih (n / 4294967296) (by omega)
      rw [toLimbs_eq (n := n), if_neg h0]
      rw [toLimbs_eq (n := n / 4294967296), if_neg (by omega)] at hq ⊢
      rw [log2C, hq, add_eq, ofLimbs_toLimbs, log2_shift n (by omega)]
      rfl

/-- **`Nat.log2`** on limbs -/
def log2 (l : List UInt64) : List UInt64 := log2C (norm l)

theorem log2_toLimbs (n : Nat) : log2 (toLimbs n) = toLimbs (Nat.log2 n) := by
  rw [log2, norm_eq, ofLimbs_toLimbs, log2C_toLimbs]

/-! ## the encoding -/

/-- a `Nat` as the S3 value of its limbs -/
def natLV (n : Nat) : V := Enc.enc (toLimbs n)
/-- the `Nat` of an S3 value (any limb list) -/
def natLD (v : V) : Nat := ofLimbs (Enc.dec v)

/-- **`Nat` as limbs** (not an instance: `s3_compileL` makes it one locally) -/
@[reducible] def encNatL : Enc Nat where
  enc := natLV
  dec := natLD
  dec_enc n := by simp [natLV, natLD, ofLimbs_toLimbs]

/-- `Fin n` over limb `Nat`s (not an instance: `s3_compileL` makes it one locally) -/
@[reducible] def encFinL {n : Nat} [NeZero n] : Enc (Fin n) where
  enc i := .c 0 [natLV i.val]
  dec | .c 0 [a] => if h : natLD a < n then ⟨natLD a, h⟩ else 0 | _ => 0
  dec_enc i := by simp [natLV, natLD, ofLimbs_toLimbs]

/-- the wrappers' form of a `Nat` (the certificates of the primitives only) -/
theorem natL_enc (n : Nat) : @Enc.enc Nat encNatL n = Enc.enc (toLimbs n) := rfl
@[simp] theorem natL_dec_enc (n : Nat) : @Enc.dec Nat encNatL (Enc.enc (toLimbs n)) = n := by
  show ofLimbs (Enc.dec (Enc.enc (toLimbs n))) = n; rw [Enc.dec_enc, ofLimbs_toLimbs]

@[simp] theorem natL_zero : @Enc.enc Nat encNatL 0 = .c 0 [] := by
  show Enc.enc (toLimbs 0) = _; rw [toLimbs_zero]; rfl
@[simp] theorem natL_dec_nil : @Enc.dec Nat encNatL (.c 0 []) = 0 := rfl
@[simp] theorem natL_dec_cons (x : BitVec 64) (r : V) :
    @Enc.dec Nat encNatL (.c 1 [.w x, r]) = x.toNat % 4294967296 + 4294967296 * @Enc.dec Nat encNatL r := rfl
@[simp] theorem finL_enc {n : Nat} [NeZero n] (i : Fin n) : @Enc.enc (Fin n) encFinL i = .c 0 [@Enc.enc Nat encNatL i.val] := rfl
@[simp] theorem finL_dec {n : Nat} [NeZero n] (a : V) :
    @Enc.dec (Fin n) encFinL (.c 0 [a]) = if h : @Enc.dec Nat encNatL a < n then ⟨@Enc.dec Nat encNatL a, h⟩ else 0 := rfl

/-- a literal `k > 0`: its low digit and the rest (`s3EncNatLitL` instantiates it with computed literals) -/
theorem natL_lit (k r q : Nat) (h : Nat.beq k 0 = false) (hr : k % 4294967296 = r) (hq : k / 4294967296 = q) :
    @Enc.enc Nat encNatL k = .c 1 [.w (OfNat.ofNat r), @Enc.enc Nat encNatL q] := by
  show Enc.enc (toLimbs k) = _
  rw [toLimbs_eq, if_neg (by intro e; rw [e] at h; exact nomatch h), enc_cons, hq]
  congr

end Proven.S3.Limbs
