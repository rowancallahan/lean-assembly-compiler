/- User inductive types with payload as cells in a word block (source level, model-free), once and for all.

Values: `C`, a universal binary tree (`c t x l r`: constructor tag `t`, one scalar word `x`, two children;
`z` = absent).  A user type is mapped into `C` (generated, `Riscv/Frontx/Ind.lean`); its byte format is
`C.enc sh` for a shape `sh` (per tag the fields in declaration order).

Memory: word block 0 (`W`), cells of 4 words `[t, x, l, r]` at multiples of 4, bump-allocated from word 4
(global `5` = the bump pointer `h`); word cell 0 is `[255, 0, 0, 0]`, the cell of `z` (pointer 0).  Children
are allocated before their parent: a child pointer is below its parent (`Rp`), so the depth of a value is at
most its pointer / 4.

Programs: `E rk k` (a kind-indexed expression: word or tree), one structural function with one word parameter
`a` and one tree parameter `b`; per tag one arm.  `Pg.sem` is its meaning, `Pg.al` the cells it allocates.
`indProg` = `main` (decode the input(s), call, encode the result), `dec`, `enc`, `F`. -/
import Nano.Base.Compiler.CLang
import Spec.Encode

namespace Proven.Mach.Ind
open Proven.Mach

/-! ## values, shapes, byte format -/

inductive C where
  | z
  | c (t : Nat) (x : BitVec 64) (l r : C)
  deriving DecidableEq, Repr, Inhabited

def C.depth : C → Nat
  | .z => 0
  | .c _ _ l r => max l.depth r.depth + 1

def C.nodes : C → Nat
  | .z => 0
  | .c _ _ l r => l.nodes + r.nodes + 1

/-- a field of a constructor: the scalar `x` as 8 bytes (`x`) or as 1 byte (`b`, `x < 256`: a `UInt8`), the
children `l`, `r`, or the child `l` / `r` as a `String` (`sl`, `sr`: its length, 8 bytes little-endian, then its
UTF-8 bytes; `C.senc`) -/
inductive Fld where | x | l | r | b | sl | sr
  deriving DecidableEq, Repr

/-- per tag, the fields in the order of the byte format -/
abbrev Shape := List (List Fld)

/-! ### strings

In memory a string is a chain of cells (`C.str`): per byte a cell `[sTag sh + 1, byte, rest, z]`, then the end
`[sTag sh, 0, z, z]`, the shape's last two tags (the type `Bytes8` of `Riscv/Frontx/IndStr.lean`).  In the byte
format it is its length `n` (8 bytes, little-endian) followed by its `n` bytes, the format of `LList UInt8` in
`Spec/Encode.lean` (`C.senc`). -/

/-- the tag of the end of a string (`sTag sh + 1`: a byte) -/
def sTag (sh : Shape) : Nat := sh.length - 2

/-- the cells of the string of bytes `L` -/
def C.str (st : Nat) : List UInt8 → C
  | [] => .c st 0 .z .z
  | b :: L => .c (st + 1) (BitVec.ofNat 64 b.toNat) (C.str st L) .z

/-- the value is the cells of a string -/
def C.IsStr (st : Nat) (v : C) : Prop := ∃ L, v = C.str st L

/-- the bytes of a string: per cell with a child `l`, its byte `x` -/
def C.sb : C → List UInt8
  | .c _ x l@(.c _ _ _ _) _ => UInt8.ofNat x.toNat :: l.sb
  | _ => []

/-- **the byte format of a string**: its length (8 bytes, little-endian), then its bytes -/
def C.senc (v : C) : List UInt8 := leN 8 v.sb.length ++ v.sb

def encF (x : BitVec 64) (el er sl sr : List UInt8) : Fld → List UInt8
  | .x => leN 8 x.toNat
  | .l => el
  | .r => er
  | .b => (leN 8 x.toNat).take 1
  | .sl => sl
  | .sr => sr

/-- the byte format: tag byte, then the fields of the shape (`x` 8 bytes little-endian, a string `C.senc`); `z` is
`[255]` -/
def C.enc (sh : Shape) : C → List UInt8
  | .z => [255]
  | .c t x l r => UInt8.ofNat t :: (sh.getD t []).flatMap (encF x (l.enc sh) (r.enc sh) l.senc r.senc)

/-- well-formed for the shape: tags of the shape, absent fields `0` / `z`, present children well-formed, string
children the cells of a string -/
def C.wf (sh : Shape) : C → Prop
  | .z => False
  | .c t x l r => t < sh.length ∧ ((Fld.x ∉ sh.getD t [] → Fld.b ∉ sh.getD t [] → x = 0) ∧
      (Fld.b ∈ sh.getD t [] → x.toNat < 256)) ∧
      ((Fld.l ∈ sh.getD t [] → l.wf sh) ∧ (Fld.sl ∈ sh.getD t [] → l.IsStr (sTag sh)) ∧
        (Fld.l ∉ sh.getD t [] → Fld.sl ∉ sh.getD t [] → l = .z)) ∧
      ((Fld.r ∈ sh.getD t [] → r.wf sh) ∧ (Fld.sr ∈ sh.getD t [] → r.IsStr (sTag sh)) ∧
        (Fld.r ∉ sh.getD t [] → Fld.sr ∉ sh.getD t [] → r = .z))

def Shape.ok (sh : Shape) : Prop := sh.length < 255 ∧ ∀ fs ∈ sh, fs.Nodup

/-! ## cells -/

/-- the cell of `z` -/
def Z0 (W : List (BitVec 64)) : Prop :=
  W[0]? = some 255 ∧ W[1]? = some 0 ∧ W[2]? = some 0 ∧ W[3]? = some 0

/-- `p` points to a cell of `v` in `W`, every cell below the bump pointer `h`, children below the parent -/
inductive Rp (W : List (BitVec 64)) (h : Nat) : BitVec 64 → C → Prop
  | z : Rp W h 0 .z
  | c {p : BitVec 64} {t : Nat} {x pl pr : BitVec 64} {l r : C} : 4 ≤ p.toNat → p.toNat % 4 = 0 →
      p.toNat + 4 ≤ h → t < 256 →
      W[p.toNat]? = some (BitVec.ofNat 64 t) → W[p.toNat + 1]? = some x → W[p.toNat + 2]? = some pl →
      W[p.toNat + 3]? = some pr → pl.toNat < p.toNat → pr.toNat < p.toNat → Rp W h pl l → Rp W h pr r →
      Rp W h p (.c t x l r)

/-- `W'` agrees with `W` below `h` -/
def Agree (W W' : List (BitVec 64)) (h : Nat) : Prop := ∀ i, i < h → W'[i]? = W[i]?

theorem Rp.mono {W W' : List (BitVec 64)} {h h' : Nat} {p : BitVec 64} {v : C} (hr : Rp W h p v)
    (hh : h ≤ h') (ha : Agree W W' h) : Rp W' h' p v := by
  induction hr with
  | z => exact .z
  | c h1 h2 h3 h4 e0 e1 e2 e3 l1 l2 _ _ ihl ihr =>
    exact .c h1 h2 (by omega) h4 (by rw [ha _ (by omega)]; exact e0) (by rw [ha _ (by omega)]; exact e1)
      (by rw [ha _ (by omega)]; exact e2) (by rw [ha _ (by omega)]; exact e3) l1 l2 ihl ihr

theorem Rp.depth {W : List (BitVec 64)} {h : Nat} {p : BitVec 64} {v : C} (hr : Rp W h p v) :
    p.toNat % 4 = 0 ∧ 4 * v.depth ≤ p.toNat := by
  induction hr with
  | z => simp [C.depth]
  | c h1 h2 _ _ _ _ _ _ l1 l2 _ _ ihl ihr => simp only [C.depth]; omega

theorem Rp.lt {W : List (BitVec 64)} {h : Nat} {p : BitVec 64} {v : C} (hr : Rp W h p v) : p.toNat < h ∨ p = 0 := by
  cases hr with
  | z => exact .inr rfl
  | c _ _ h3 => exact .inl (by omega)

theorem Agree.trans {W₁ W₂ W₃ : List (BitVec 64)} {h₁ h₂ : Nat} (a : Agree W₁ W₂ h₁) (b : Agree W₂ W₃ h₂)
    (hh : h₁ ≤ h₂) : Agree W₁ W₃ h₁ := fun i hi => by rw [b i (by omega), a i hi]

theorem Agree.refl (W : List (BitVec 64)) (h : Nat) : Agree W W h := fun _ _ => rfl

/-- reading a cell: `z` reads as the cell `[255, 0, 0, 0]` -/
def C.tag : C → Nat | .z => 255 | .c t _ _ _ => t
def C.xv : C → BitVec 64 | .z => 0 | .c _ x _ _ => x
def C.lv : C → C | .z => .z | .c _ _ l _ => l
def C.rv : C → C | .z => .z | .c _ _ _ r => r

theorem Rp.read {W : List (BitVec 64)} {h : Nat} {p : BitVec 64} {v : C} (hr : Rp W h p v) (hz : Z0 W) :
    v.tag < 256 ∧ W[p.toNat]? = some (BitVec.ofNat 64 v.tag) ∧ W[p.toNat + 1]? = some v.xv ∧
      (∃ pl, W[p.toNat + 2]? = some pl ∧ Rp W h pl v.lv) ∧ (∃ pr, W[p.toNat + 3]? = some pr ∧ Rp W h pr v.rv) := by
  cases hr with
  | z => exact ⟨by decide, hz.1, hz.2.1, ⟨0, hz.2.2.1, .z⟩, ⟨0, hz.2.2.2, .z⟩⟩
  | c _ _ _ h4 e0 e1 e2 e3 _ _ rl rr => exact ⟨h4, e0, e1, ⟨_, e2, rl⟩, ⟨_, e3, rr⟩⟩

/-! ## programs -/

inductive Kd where | w | t
  deriving DecidableEq, Repr

@[reducible] def Kd.den : Kd → Type
  | .w => BitVec 64
  | .t => C

def Kd.dflt : (k : Kd) → k.den
  | .w => (0 : BitVec 64)
  | .t => C.z

/-- a value of either kind as a (word, tree) pair, and back -/
def Kd.pair : (k : Kd) → k.den → BitVec 64 × C
  | .w, y => (y, .z)
  | .t, y => (0, y)
def Kd.pick : (k : Kd) → BitVec 64 × C → k.den
  | .w, p => p.1
  | .t, p => p.2

@[simp] theorem Kd.pick_pair (k : Kd) (y : k.den) : k.pick (k.pair y) = y := by cases k <;> rfl

/-- expressions of a structural function with result kind `rk`, of kind `k`: the fields `x`, `l`, `r` of the
current node, the word parameter `a`, the tree parameter `b`, constants, operations, constructors (`mk`
allocates a cell), recursive calls on a child (`call false` = `l`, `call true` = `r`); the current node (`me`),
the fields of any tree value (`fw`, `ft`), calls of the program's later functions (`ext`), `let` (`bind`, `var`) -/
inductive E (rk : Kd) : Kd → Type where
  | x : E rk .w
  | a : E rk .w
  | k (c : BitVec 64) : E rk .w
  | bin (op : Op) (e₁ e₂ : E rk .w) : E rk .w
  | l : E rk .t
  | r : E rk .t
  | b : E rk .t
  | nul : E rk .t
  | mk (t : Nat) (ex : E rk .w) (el er : E rk .t) : E rk .t
  | call (ch : Bool) (ea : E rk .w) (eb : E rk .t) : E rk rk
  /-- `if c ≠ 0 then e₁ else e₂` (only the chosen branch is evaluated) -/
  | ite {k : Kd} (c : E rk .w) (e₁ e₂ : E rk k) : E rk k
  /-- the current node -/
  | me : E rk .t
  /-- the tag (`false`) or the scalar (`true`) of a tree value (`z`: `255`, `0`) -/
  | fw (i : Bool) (e : E rk .t) : E rk .w
  /-- the left (`false`) or right (`true`) child of a tree value (`z`: `z`) -/
  | ft (ch : Bool) (e : E rk .t) : E rk .t
  /-- a call of the `j`-th function after this one (of result kind `k`) on a tree, a word and a tree -/
  | ext (j : Nat) (k : Kd) (et : E rk .t) (ea : E rk .w) (eb : E rk .t) : E rk k
  /-- `let v := e₁; e₂` (`v` is `var 0` in `e₂`, the outer variables shift by one) -/
  | bind {k₁ k : Kd} (e₁ : E rk k₁) (e₂ : E rk k) : E rk k
  /-- the `i`-th enclosing `bind` (de Bruijn), of kind `k` -/
  | var (i : Nat) (k : Kd) : E rk k
  /-- a recursive call on a grandchild: child `c₂` of child `c₁` (`false` = `l`; the fields of a constructor
  that continue in an extension cell, `NOTES` section 25) -/
  | call2 (c₁ c₂ : Bool) (ea : E rk .w) (eb : E rk .t) : E rk rk

/-- one function: an arm per tag (tags `≥ arms.length` and `z` give `rk.dflt`); `X j` / `XA j` are the meaning and
the cell count of the `j`-th function after this one (`ext j`) -/
structure Pg (rk : Kd) where
  arms : List (E rk rk)
  X : Nat → C → BitVec 64 → C → BitVec 64 × C := fun _ _ _ _ => (0, .z)
  XA : Nat → C → BitVec 64 → C → Nat := fun _ _ _ _ => 0
  /-- straight-line body: no loop, every call a real call, one test per tag in sequence (`fLoopS`; for many
  constructors: a branch then jumps only over its own arm) -/
  st : Bool := false

variable {rk : Kd}

/-- what an expression is evaluated in: the recursive calls, the later functions, the current node, the
values of the enclosing `bind`s (innermost first) -/
structure Cn (rk : Kd) where
  f : Bool → BitVec 64 → C → rk.den
  g : Bool → Bool → BitVec 64 → C → rk.den
  X : Nat → C → BitVec 64 → C → BitVec 64 × C
  me : C
  ρ : List (BitVec 64 × C)

/-- the cell counts of the calls in an expression -/
structure Ca where
  f : Bool → BitVec 64 → C → Nat
  g : Bool → Bool → BitVec 64 → C → Nat
  X : Nat → C → BitVec 64 → C → Nat

def ev (self : Cn rk) (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C) :
    {k : Kd} → E rk k → k.den
  | _, .x => x
  | _, .a => a
  | _, .k c => c
  | _, .bin op e₁ e₂ => op.eval (ev self x l r a b e₁) (ev self x l r a b e₂)
  | _, .l => l
  | _, .r => r
  | _, .b => b
  | _, .nul => C.z
  | _, .mk t ex el er => C.c t (ev self x l r a b ex) (ev self x l r a b el) (ev self x l r a b er)
  | _, .call ch ea eb => self.f ch (ev self x l r a b ea) (ev self x l r a b eb)
  | _, .ite c e₁ e₂ => if ev self x l r a b c = 0 then ev self x l r a b e₂ else ev self x l r a b e₁
  | _, .me => self.me
  | _, .fw i e => if i then (ev self x l r a b e).xv else BitVec.ofNat 64 (ev self x l r a b e).tag
  | _, .ft ch e => if ch then (ev self x l r a b e).rv else (ev self x l r a b e).lv
  | _, .ext j kk et ea eb => kk.pick (self.X j (ev self x l r a b et) (ev self x l r a b ea) (ev self x l r a b eb))
  | _, @E.bind _ k₁ _ e₁ e₂ =>
    ev { self with ρ := k₁.pair (ev self x l r a b e₁) :: self.ρ } x l r a b e₂
  | _, .var i kk => kk.pick (self.ρ.getD i (0, .z))
  | _, .call2 c₁ c₂ ea eb => self.g c₁ c₂ (ev self x l r a b ea) (ev self x l r a b eb)

/-- cells allocated by an expression -/
def alE (self : Cn rk) (sal : Ca) (x : BitVec 64) (l r : C)
    (a : BitVec 64) (b : C) : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => alE self sal x l r a b e₁ + alE self sal x l r a b e₂
  | _, .mk _ ex el er => alE self sal x l r a b ex + alE self sal x l r a b el + alE self sal x l r a b er + 1
  | _, .call ch ea eb => alE self sal x l r a b ea + alE self sal x l r a b eb +
      sal.f ch (ev self x l r a b ea) (ev self x l r a b eb)
  | _, .ite c e₁ e₂ => alE self sal x l r a b c +
      if ev self x l r a b c = 0 then alE self sal x l r a b e₂ else alE self sal x l r a b e₁
  | _, .fw _ e => alE self sal x l r a b e
  | _, .ft _ e => alE self sal x l r a b e
  | _, .ext j _ et ea eb => alE self sal x l r a b et + alE self sal x l r a b ea + alE self sal x l r a b eb +
      sal.X j (ev self x l r a b et) (ev self x l r a b ea) (ev self x l r a b eb)
  | _, @E.bind _ k₁ _ e₁ e₂ => alE self sal x l r a b e₁ +
      alE { self with ρ := k₁.pair (ev self x l r a b e₁) :: self.ρ } sal x l r a b e₂
  | _, .call2 c₁ c₂ ea eb => alE self sal x l r a b ea + alE self sal x l r a b eb +
      sal.g c₁ c₂ (ev self x l r a b ea) (ev self x l r a b eb)
  | _, _ => 0

def Pg.sem (pg : Pg rk) : C → BitVec 64 → C → rk.den
  | .z, _, _ => rk.dflt
  | .c t x l r, a, b =>
    match pg.arms[t]? with
    | some e => ev ⟨fun ch a' b' => if ch then pg.sem r a' b' else pg.sem l a' b',
        fun c₁ c₂ a' b' => if c₁ then (match r with
            | .z => rk.dflt
            | .c _ _ rl rr => if c₂ then pg.sem rr a' b' else pg.sem rl a' b')
          else (match l with
            | .z => rk.dflt
            | .c _ _ ll lr => if c₂ then pg.sem lr a' b' else pg.sem ll a' b'),
        pg.X, .c t x l r, []⟩ x l r a b e
    | none => rk.dflt

def Pg.al (pg : Pg rk) : C → BitVec 64 → C → Nat
  | .z, _, _ => 0
  | .c t x l r, a, b =>
    match pg.arms[t]? with
    | some e => alE ⟨fun ch a' b' => if ch then pg.sem r a' b' else pg.sem l a' b',
        fun c₁ c₂ a' b' => if c₁ then (match r with
            | .z => rk.dflt
            | .c _ _ rl rr => if c₂ then pg.sem rr a' b' else pg.sem rl a' b')
          else (match l with
            | .z => rk.dflt
            | .c _ _ ll lr => if c₂ then pg.sem lr a' b' else pg.sem ll a' b'),
        pg.X, .c t x l r, []⟩
        ⟨fun ch a' b' => if ch then pg.al r a' b' else pg.al l a' b',
         fun c₁ c₂ a' b' => if c₁ then (match r with
            | .z => 0
            | .c _ _ rl rr => if c₂ then pg.al rr a' b' else pg.al rl a' b')
          else (match l with
            | .z => 0
            | .c _ _ ll lr => if c₂ then pg.al lr a' b' else pg.al ll a' b'), pg.XA⟩ x l r a b e
    | none => 0

/-- the functions of a program after the current one: meanings and cell counts, by position -/
def semX : List (Σ k : Kd, Pg k) → Nat → C → BitVec 64 → C → BitVec 64 × C
  | [], _ => fun _ _ _ => (0, .z)
  | ⟨k, p⟩ :: _, 0 => fun t a b => k.pair (p.sem t a b)
  | _ :: ps, j + 1 => semX ps j
def alX : List (Σ k : Kd, Pg k) → Nat → C → BitVec 64 → C → Nat
  | [], _ => fun _ _ _ => 0
  | ⟨_, p⟩ :: _, 0 => fun t a b => p.al t a b
  | _ :: ps, j + 1 => alX ps j

/-- each function's `X`, `XA` are those of the functions after it -/
def Chain : List (Σ k : Kd, Pg k) → Prop
  | [] => True
  | ⟨_, p⟩ :: ps => (∀ j, j < ps.length → p.X j = semX ps j ∧ p.XA j = alX ps j) ∧ Chain ps

/-! ## static measures -/

/-- constructors in an expression -/
def E.mks : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => e₁.mks + e₂.mks
  | _, .mk _ ex el er => ex.mks + el.mks + er.mks + 1
  | _, .call _ ea eb => ea.mks + eb.mks
  | _, .ite c e₁ e₂ => c.mks + max e₁.mks e₂.mks
  | _, .fw _ e => e.mks
  | _, .ft _ e => e.mks
  | _, .ext _ _ et ea eb => et.mks + ea.mks + eb.mks
  | _, .bind e₁ e₂ => e₁.mks + e₂.mks
  | _, .call2 _ _ ea eb => ea.mks + eb.mks
  | _, _ => 0

/-- calls on child `ch` -/
def E.calls (ch : Bool) : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => e₁.calls ch + e₂.calls ch
  | _, .mk _ ex el er => ex.calls ch + el.calls ch + er.calls ch
  | _, .call c ea eb => ea.calls ch + eb.calls ch + if c = ch then 1 else 0
  | _, .ite c e₁ e₂ => c.calls ch + max (e₁.calls ch) (e₂.calls ch)
  | _, .fw _ e => e.calls ch
  | _, .ft _ e => e.calls ch
  | _, .ext _ _ et ea eb => et.calls ch + ea.calls ch + eb.calls ch
  | _, .bind e₁ e₂ => e₁.calls ch + e₂.calls ch
  | _, .call2 _ _ ea eb => ea.calls ch + eb.calls ch
  | _, _ => 0

/-- largest tag of a constructor -/
def E.tags : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => max e₁.tags e₂.tags
  | _, .mk t ex el er => max (max t ex.tags) (max el.tags er.tags)
  | _, .call _ ea eb => max ea.tags eb.tags
  | _, .ite c e₁ e₂ => max c.tags (max e₁.tags e₂.tags)
  | _, .fw _ e => e.tags
  | _, .ft _ e => e.tags
  | _, .ext _ _ et ea eb => max et.tags (max ea.tags eb.tags)
  | _, .bind e₁ e₂ => max e₁.tags e₂.tags
  | _, .call2 _ _ ea eb => max ea.tags eb.tags
  | _, _ => 0

/-- temporaries used by `comp` beyond its first -/
def E.tmp : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => max e₁.tmp (e₂.tmp + 1) + 1
  | _, .mk _ ex el er => max (max ex.tmp (el.tmp + 1)) (er.tmp + 2) + 1
  | _, .call _ ea eb => max ea.tmp (eb.tmp + 1) + 1
  | _, .ite c e₁ e₂ => max c.tmp (max e₁.tmp e₂.tmp) + 1
  | _, .fw _ e => e.tmp + 1
  | _, .ft _ e => e.tmp + 1
  | _, .ext _ _ et ea eb => max (max et.tmp (ea.tmp + 1)) (eb.tmp + 2) + 1
  | _, .bind e₁ e₂ => max e₁.tmp (e₂.tmp + 1) + 1
  | _, .call2 _ _ ea eb => max ea.tmp (eb.tmp + 1) + 2
  | _, _ => 0

/-- calls of later functions and calls on grandchildren in an expression (both outside the linear cell bound
`al_le`) -/
def E.exts : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => e₁.exts + e₂.exts
  | _, .mk _ ex el er => ex.exts + el.exts + er.exts
  | _, .call _ ea eb => ea.exts + eb.exts
  | _, .ite c e₁ e₂ => c.exts + e₁.exts + e₂.exts
  | _, .fw _ e => e.exts
  | _, .ft _ e => e.exts
  | _, .ext _ _ et ea eb => et.exts + ea.exts + eb.exts + 1
  | _, .bind e₁ e₂ => e₁.exts + e₂.exts
  | _, .call2 _ _ ea eb => ea.exts + eb.exts + 1
  | _, _ => 0

/-- the kinds agree: `var i k` under binders of kinds `ks` (innermost first), `ext j k` with `nx[j] = k` -/
def E.okc (ks nx : List Kd) : {k : Kd} → E rk k → Bool
  | _, .bin _ e₁ e₂ => e₁.okc ks nx && e₂.okc ks nx
  | _, .mk _ ex el er => ex.okc ks nx && el.okc ks nx && er.okc ks nx
  | _, .call _ ea eb => ea.okc ks nx && eb.okc ks nx
  | _, .ite c e₁ e₂ => c.okc ks nx && e₁.okc ks nx && e₂.okc ks nx
  | _, .fw _ e => e.okc ks nx
  | _, .ft _ e => e.okc ks nx
  | _, .ext j kk et ea eb => nx[j]? == some kk && et.okc ks nx && ea.okc ks nx && eb.okc ks nx
  | _, @E.bind _ k₁ _ e₁ e₂ => e₁.okc ks nx && e₂.okc (k₁ :: ks) nx
  | _, .var i kk => ks[i]? == some kk
  | _, .call2 _ _ ea eb => ea.okc ks nx && eb.okc ks nx
  | _, _ => true

/-- is a tail call -/
def E.tail? : {k : Kd} → E rk k → Option (Bool × E rk .w × E rk .t)
  | _, .call ch ea eb => some (ch, ea, eb)
  | _, _ => none

def Pg.M (pg : Pg rk) : Nat := (pg.arms.map E.mks).foldr max 0

/-- every arm calls each child at most once, constructor tags below `n` -/
def Pg.ok (pg : Pg rk) (n : Nat) : Prop :=
  pg.arms.length ≤ 255 ∧ ∀ e ∈ pg.arms, e.calls false ≤ 1 ∧ e.calls true ≤ 1 ∧ e.tags < n ∧ e.tmp ≤ 5

/-! ## the compiler

Globals: `0` input base, `1` input length (result length on return), `2` word block base, `3` output base,
`4` input cursor, `5` bump pointer, `6` output cursor.  Functions: `0` main, `1` dec, `2` enc, `3` F.
F's locals: `8` p, `9` a, `10` b, `11` go, `12` res, `13` tag, `14` x, `15` l, `16` r, `17 ..` temporaries. -/

def vE (i : Nat) : BExp := .var i
def kE (c : Nat) : BExp := .const (BitVec.ofNat 64 c)
def addE (i c : Nat) : BExp := .bin .add (.var i) (kE c)
def asg (v : Nat) (e : BExp) : BStmt := .assign v e

/-- `W[hp + i] := e` -/
def stW (i : Nat) (e : BExp) : BStmt := .store64 0 (addE 5 i) e

/-- a new cell `[t, v_x, v_l, v_r]`, its pointer to `d`, bump -/
def alloc (t : BExp) (vx vl vr d : Nat) : BStmt :=
  .seq (stW 0 t) (.seq (stW 1 (vE vx)) (.seq (stW 2 (vE vl)) (.seq (stW 3 (vE vr))
    (.seq (asg d (vE 5)) (asg 5 (addE 5 4))))))

/-- `e` into variable `d`, temporaries from `n`; the `bind` values in the variables `sl` (innermost first) -/
def comp (fi : Nat) (sl : List Nat) : {k : Kd} → E rk k → Nat → Nat → CStmt
  | _, .x, d, _ => .base (asg d (vE 14))
  | _, .a, d, _ => .base (asg d (vE 9))
  | _, .k c, d, _ => .base (asg d (.const c))
  | _, .bin op e₁ e₂, d, n => .seq (comp fi sl e₁ n (n + 1)) (.seq (comp fi sl e₂ (n + 1) (n + 2))
      (.base (asg d (.bin op (vE n) (vE (n + 1))))))
  | _, .l, d, _ => .base (asg d (vE 15))
  | _, .r, d, _ => .base (asg d (vE 16))
  | _, .b, d, _ => .base (asg d (vE 10))
  | _, .nul, d, _ => .base (asg d (kE 0))
  | _, .mk t ex el er, d, n => .seq (comp fi sl ex n (n + 1)) (.seq (comp fi sl el (n + 1) (n + 2))
      (.seq (comp fi sl er (n + 2) (n + 3)) (.base (alloc (kE t) n (n + 1) (n + 2) d))))
  | _, .call ch ea eb, d, n => .seq (comp fi sl ea n (n + 1)) (.seq (comp fi sl eb (n + 1) (n + 2))
      (.call d fi [vE (if ch then 16 else 15), vE n, vE (n + 1)]))
  | _, .ite c e₁ e₂, d, n => .seq (comp fi sl c n (n + 1))
      (.ite (vE n) (comp fi sl e₁ d (n + 1)) (comp fi sl e₂ d (n + 1)))
  | _, .me, d, _ => .base (asg d (vE 8))
  | _, .fw i e, d, n => .seq (comp fi sl e n (n + 1)) (.base (.load64 d 0 (addE n (if i then 1 else 0))))
  | _, .ft ch e, d, n => .seq (comp fi sl e n (n + 1)) (.base (.load64 d 0 (addE n (if ch then 3 else 2))))
  | _, .ext j _ et ea eb, d, n => .seq (comp fi sl et n (n + 1)) (.seq (comp fi sl ea (n + 1) (n + 2))
      (.seq (comp fi sl eb (n + 2) (n + 3)) (.call d (fi + 1 + j) [vE n, vE (n + 1), vE (n + 2)])))
  | _, .bind e₁ e₂, d, n => .seq (comp fi sl e₁ n (n + 1)) (comp fi (n :: sl) e₂ d (n + 1))
  | _, .var i _, d, _ => .base (asg d (vE (sl.getD i 0)))
  | _, .call2 c₁ c₂ ea eb, d, n => .seq (comp fi sl ea n (n + 1)) (.seq (comp fi sl eb (n + 1) (n + 2))
      (.seq (.base (.load64 (n + 2) 0 (addE (if c₁ then 16 else 15) (if c₂ then 3 else 2))))
        (.call d fi [vE (n + 2), vE n, vE (n + 1)])))

/-- the four words of the cell at `v_p` -/
def loads (p t x l r : Nat) : BStmt :=
  .seq (.load64 t 0 (vE p)) (.seq (.load64 x 0 (addE p 1)) (.seq (.load64 l 0 (addE p 2)) (.load64 r 0 (addE p 3))))

def eqE (v c : Nat) : BExp := .bin .eq (vE v) (kE c)

/-- one arm: a tail call continues the loop on the child, anything else is the result -/
def arm (fi : Nat) (e : E rk rk) : CStmt :=
  match e.tail? with
  | some (ch, ea, eb) => .seq (comp fi [] ea 17 18) (.seq (comp fi [] eb 18 19)
      (.base (.seq (asg 8 (vE (if ch then 16 else 15))) (.seq (asg 9 (vE 17)) (asg 10 (vE 18))))))
  | none => .seq (comp fi [] e 12 17) (.base (asg 11 (kE 0)))

/-- the parts of an `ite` -/
def E.ite? : {k : Kd} → E rk k → Option (E rk .w × E rk k × E rk k)
  | _, .ite c e₁ e₂ => some (c, e₁, e₂)
  | _, _ => none

/-- an arm that is an `ite` (up to `f` deep) is split at the top: a call in a branch is a tail call too -/
def armT (fi : Nat) : Nat → E rk rk → CStmt
  | 0, e => arm fi e
  | f + 1, e => match e.ite? with
    | some (c, e₁, e₂) => .seq (comp fi [] c 17 18) (.ite (vE 17) (armT fi f e₁) (armT fi f e₂))
    | none => arm fi e

def disp (fi : Nat) : List (E rk rk) → Nat → CStmt
  | [], _ => .base (.seq (asg 12 (kE 0)) (asg 11 (kE 0)))
  | e :: es, i => .ite (eqE 13 i) (armT fi 8 e) (disp fi es (i + 1))

def fLoop (fi : Nat) (pg : Pg rk) : CStmt := .loop (vE 11) (.seq (.base (loads 8 13 14 15 16)) (disp fi pg.arms 0))

/-- one arm, not a loop: the value of `e` is the result -/
def armN (fi : Nat) (e : E rk rk) : CStmt := .seq (comp fi [] e 12 17) (.base (asg 11 (kE 0)))

/-- the arms in sequence, each behind its own test of the tag (`v_13` is kept by the arms) -/
def dispS (fi : Nat) : List (E rk rk) → Nat → CStmt
  | [], _ => .base (asg 12 (vE 12))
  | e :: es, i => .seq (.ite (eqE 13 i) (armN fi e) (.base (asg 12 (vE 12)))) (dispS fi es (i + 1))

/-- the straight-line body: the cell, the result `0` (`z` or the word `0`) unless an arm matches -/
def fLoopS (fi : Nat) (pg : Pg rk) : CStmt :=
  .seq (.base (.seq (loads 8 13 14 15 16) (asg 12 (kE 0)))) (dispS fi pg.arms 0)

def fLoopX (fi : Nat) (pg : Pg rk) : CStmt := if pg.st then fLoopS fi pg else fLoop fi pg

/-- the function at index `fi` with `nl` locals -/
def fFn (fi nl : Nat) (pg : Pg rk) : Fn := ⟨3, nl, .seq (.base (asg 11 (kE 1))) (fLoopX fi pg), vE 12⟩

/-- `x` from the 8 bytes at the cursor (`j` bytes from the top, Horner), into `v_9`; byte temporary `v_12` -/
def rdB : Nat → BStmt
  | 0 => asg 9 (kE 0)
  | j + 1 => .seq (rdB j) (.seq (.load 12 0 (addE 4 (7 - j)))
      (asg 9 (.bin .add (.bin .shl (vE 9) (kE 8)) (vE 12))))

/-- a new cell `[e_t, e_x, e_l, e_r]`, its pointer to `d`, bump -/
def allocK (t ex el er : BExp) (d : Nat) : BStmt :=
  .seq (stW 0 t) (.seq (stW 1 ex) (.seq (stW 2 el) (.seq (stW 3 er)
    (.seq (asg d (vE 5)) (asg 5 (addE 5 4))))))

/-- a string at the cursor into `v_d` (tags `st`, `st + 1`): its length `n` (8 bytes) into `v_13` (`v_9` kept), the
end cell, then a cell per byte from the last one back (`v_14` the position read, `v_12` the byte); the cursor after
the bytes -/
def dStr (st d : Nat) : CStmt :=
  .seq (.base (.seq (asg 13 (vE 9)) (.seq (rdB 8) (.seq (asg 14 (vE 9)) (.seq (asg 9 (vE 13)) (.seq (asg 13 (vE 14))
      (.seq (asg 14 (.bin .add (addE 4 8) (vE 13))) (allocK (kE st) (kE 0) (kE 0) (kE 0) d))))))))
  (.seq (.loop (.bin .sub (vE 14) (addE 4 8)) (.base (.seq (asg 14 (.bin .sub (vE 14) (kE 1)))
      (.seq (.load 12 0 (vE 14)) (allocK (kE (st + 1)) (vE 12) (vE d) (kE 0) d)))))
    (.base (asg 4 (.bin .add (addE 4 8) (vE 13)))))

def dFld (st : Nat) : Fld → CStmt
  | .x => .base (.seq (rdB 8) (asg 4 (addE 4 8)))
  | .l => .call 10 1 []
  | .r => .call 11 1 []
  | .b => .base (.seq (.load 9 0 (vE 4)) (asg 4 (addE 4 1)))
  | .sl => dStr st 10
  | .sr => dStr st 11

def dFlds (st : Nat) : List Fld → CStmt
  | [] => .base (asg 9 (vE 9))
  | f :: fs => .seq (dFld st f) (dFlds st fs)

/-- the fields of the tag in `v_8`: one test per tag in sequence (each branch jumps only over its own code, so the
number of tags is not limited by the reach of a branch; the fields keep `v_8`) -/
def dDisp (st : Nat) : Shape → Nat → CStmt
  | [], _ => .base (asg 9 (vE 9))
  | fs :: sh, i => .seq (.ite (eqE 8 i) (dFlds st fs) (.base (asg 9 (vE 9)))) (dDisp st sh (i + 1))

/-- `dec()`: locals `8` tag, `9` x, `10` l, `11` r, `12` byte, `13`, `14` (strings); the cell after its children -/
def decFn (sh : Shape) : Fn :=
  ⟨0, 7, .seq (.base (.seq (.load 8 0 (vE 4)) (.seq (asg 4 (addE 4 1))
      (.seq (asg 9 (kE 0)) (.seq (asg 10 (kE 0)) (asg 11 (kE 0)))))))
    (.seq (dDisp (sTag sh) sh 0) (.base (alloc (vE 8) 9 10 11 12))), vE 12⟩

/-- the low `j` bytes of `v_10` to the output at the cursor -/
def wrB : Nat → BStmt
  | 0 => asg 10 (vE 10)
  | j + 1 => .seq (wrB j) (.store 1 (addE 6 j) (.bin .lshr (vE 10) (kE (8 * j))))

/-- the count of the string at `v_p`: `v_14` the cell, `v_13` its child, `v_15` the count -/
def eCnt (p : Nat) : CStmt :=
  .seq (.base (.seq (asg 15 (kE 0)) (.seq (asg 14 (vE p)) (.load64 13 0 (addE 14 2)))))
    (.loop (vE 13) (.base (.seq (asg 15 (addE 15 1)) (.seq (asg 14 (vE 13)) (.load64 13 0 (addE 14 2))))))

/-- the bytes of the string at `v_14` (its child in `v_15`) to the output, `v_13` the byte -/
def eBytes : CStmt :=
  .loop (vE 15) (.base (.seq (.load64 13 0 (addE 14 1)) (.seq (.store 1 (vE 6) (vE 13)) (.seq (asg 6 (addE 6 1))
    (.seq (asg 14 (vE 15)) (.load64 15 0 (addE 14 2)))))))

/-- a string at `v_p` to the output: its length (8 bytes, `v_10` kept), then its bytes -/
def eStr (p : Nat) : CStmt :=
  .seq (eCnt p) (.seq (.base (.seq (asg 14 (vE 10)) (.seq (asg 10 (vE 15)) (.seq (wrB 8) (.seq (asg 6 (addE 6 8))
    (.seq (asg 10 (vE 14)) (.seq (asg 14 (vE p)) (.load64 15 0 (addE 14 2)))))))))
    eBytes)

def eFld : Fld → CStmt
  | .x => .base (.seq (wrB 8) (asg 6 (addE 6 8)))
  | .l => .call 13 2 [vE 11]
  | .r => .call 13 2 [vE 12]
  | .b => .base (.seq (wrB 1) (asg 6 (addE 6 1)))
  | .sl => eStr 11
  | .sr => eStr 12

def eFlds : List Fld → CStmt
  | [] => .base (asg 10 (vE 10))
  | f :: fs => .seq (eFld f) (eFlds fs)

/-- the fields of the tag in `v_9`: one test per tag in sequence (as `dDisp`) -/
def eDisp : Shape → Nat → CStmt
  | [], _ => .base (asg 10 (vE 10))
  | fs :: sh, i => .seq (.ite (eqE 9 i) (eFlds fs) (.base (asg 10 (vE 10)))) (eDisp sh (i + 1))

/-- `enc(p)`: locals `8` p, `9` tag, `10` x, `11` l, `12` r, `13` dummy, `14`, `15` (strings) -/
def encFn (sh : Shape) : Fn :=
  ⟨1, 8, .seq (.base (.seq (loads 8 9 10 11 12) (.seq (.store 1 (vE 6) (vE 9)) (asg 6 (addE 6 1)))))
    (eDisp sh 0), kE 0⟩

/-- the entry: the second argument `b` of `F` -/
inductive BIn where
  /-- the second input -/
  | inp
  /-- a fresh nullary constructor -/
  | ctor (t : Nat)
  | none
  deriving DecidableEq

/-- the word argument of the entry: a literal, or 8 bytes (little-endian) after the input tree(s) -/
def aC (ain : Bool) (a0 : BitVec 64) : BStmt :=
  if ain then .seq (asg 13 (vE 9)) (.seq (rdB 8) (.seq (asg 11 (vE 9)) (asg 9 (vE 13)))) else asg 11 (.const a0)

/-- `main()`: cell 0, decode, call `F`, the result to the output (a tree: its encoding, length returned; a word:
its low `nb` bytes) -/
def mainFn (bi : BIn) (ain : Bool) (a0 : BitVec 64) (tree : Bool) (nb : Nat) : Fn :=
  ⟨0, 6, .seq (.base (.seq (asg 4 (kE 0)) (.seq (asg 5 (kE 4)) (.seq (.store64 0 (kE 0) (kE 255))
      (.seq (.store64 0 (kE 1) (kE 0)) (.seq (.store64 0 (kE 2) (kE 0)) (.store64 0 (kE 3) (kE 0))))))))
    (.seq (.call 8 1 [])
    (.seq (match bi with
      | .inp => .call 9 1 []
      | .ctor t => .base (.seq (asg 11 (kE 0)) (alloc (kE t) 11 11 11 9))
      | .none => .base (asg 9 (kE 0)))
    (.seq (.base (aC ain a0)) (.seq (.call 10 3 [vE 8, vE 11, vE 9])
      (if tree then .seq (.base (asg 6 (kE 0))) (.call 13 2 [vE 10]) else .base (.seq (asg 6 (kE 0)) (wrB nb))))))),
    if tree then vE 6 else kE 0⟩

/-- the whole program: `main`, `dec` (shape `sh`), `enc` (shape `shO`), the entry function `pg`, the later
functions `hs` (each may call the ones after it), all with `nl` locals -/
def indProgM (sh shO : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k)) (bi : BIn) (ain : Bool) (a0 : BitVec 64)
    (nb nl : Nat) : Prog :=
  [mainFn bi ain a0 (rk = .t) nb, decFn sh, encFn shO, fFn 3 nl pg] ++ hs.mapIdx fun i p => fFn (4 + i) nl p.2

def indProg (sh : Shape) (pg : Pg rk) (bi : BIn) (a0 : BitVec 64) (nb : Nat) : Prog :=
  indProgM sh sh pg [] bi false a0 nb 16

/-- the tree parameter of the entry call -/
def BIn.val : BIn → C → C
  | .inp, v₂ => v₂
  | .ctor t, _ => .c t 0 .z .z
  | .none, _ => .z

/-- the input: the first value, then the second if `b` is an input -/
def inBytes (sh : Shape) : BIn → C → C → List UInt8
  | .inp, v₁, v₂ => v₁.enc sh ++ v₂.enc sh
  | _, v₁, _ => v₁.enc sh

/-- the input with the word argument: 8 bytes little-endian after the values when `ain` -/
def inBytesA (sh : Shape) (bi : BIn) (ain : Bool) (v₁ v₂ : C) (a : BitVec 64) : List UInt8 :=
  inBytes sh bi v₁ v₂ ++ if ain then leN 8 a.toNat else []

/-- the output: a tree's encoding, or the low `nb` bytes of a word -/
def Kd.out (sh : Shape) (nb : Nat) : (k : Kd) → k.den → List UInt8
  | .t, y => C.enc sh y
  | .w, y => (leN 8 (BitVec.toNat (w := 64) y)).take nb

end Proven.Mach.Ind
