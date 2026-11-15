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
import Compiler.CLang
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

inductive Fld where | x | l | r
  deriving DecidableEq, Repr

/-- per tag, the fields in the order of the byte format -/
abbrev Shape := List (List Fld)

def encF (x : BitVec 64) (el er : List UInt8) : Fld → List UInt8
  | .x => leN 8 x.toNat
  | .l => el
  | .r => er

/-- the byte format: tag byte, then the fields of the shape (`x` 8 bytes little-endian); `z` is `[255]` -/
def C.enc (sh : Shape) : C → List UInt8
  | .z => [255]
  | .c t x l r => UInt8.ofNat t :: (sh.getD t []).flatMap (encF x (l.enc sh) (r.enc sh))

/-- well-formed for the shape: tags of the shape, absent fields `0` / `z`, present children well-formed -/
def C.wf (sh : Shape) : C → Prop
  | .z => False
  | .c t x l r => t < sh.length ∧ (Fld.x ∉ sh.getD t [] → x = 0) ∧
      (if Fld.l ∈ sh.getD t [] then l.wf sh else l = .z) ∧ (if Fld.r ∈ sh.getD t [] then r.wf sh else r = .z)

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

/-- expressions of a structural function with result kind `rk`, of kind `k`: the fields `x`, `l`, `r` of the
current node, the word parameter `a`, the tree parameter `b`, constants, operations, constructors (`mk`
allocates a cell), recursive calls on a child (`call false` = `l`, `call true` = `r`) -/
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

/-- one function: an arm per tag (tags `≥ arms.length` and `z` give `rk.dflt`) -/
structure Pg (rk : Kd) where
  arms : List (E rk rk)

variable {rk : Kd}

def ev (self : Bool → BitVec 64 → C → rk.den) (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C) :
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
  | _, .call ch ea eb => self ch (ev self x l r a b ea) (ev self x l r a b eb)
  | _, .ite c e₁ e₂ => if ev self x l r a b c = 0 then ev self x l r a b e₂ else ev self x l r a b e₁

/-- cells allocated by an expression -/
def alE (self : Bool → BitVec 64 → C → rk.den) (sal : Bool → BitVec 64 → C → Nat) (x : BitVec 64) (l r : C)
    (a : BitVec 64) (b : C) : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => alE self sal x l r a b e₁ + alE self sal x l r a b e₂
  | _, .mk _ ex el er => alE self sal x l r a b ex + alE self sal x l r a b el + alE self sal x l r a b er + 1
  | _, .call ch ea eb => alE self sal x l r a b ea + alE self sal x l r a b eb +
      sal ch (ev self x l r a b ea) (ev self x l r a b eb)
  | _, .ite c e₁ e₂ => alE self sal x l r a b c +
      if ev self x l r a b c = 0 then alE self sal x l r a b e₂ else alE self sal x l r a b e₁
  | _, _ => 0

def Pg.sem (pg : Pg rk) : C → BitVec 64 → C → rk.den
  | .z, _, _ => rk.dflt
  | .c t x l r, a, b =>
    match pg.arms[t]? with
    | some e => ev (fun ch a' b' => if ch then pg.sem r a' b' else pg.sem l a' b') x l r a b e
    | none => rk.dflt

def Pg.al (pg : Pg rk) : C → BitVec 64 → C → Nat
  | .z, _, _ => 0
  | .c t x l r, a, b =>
    match pg.arms[t]? with
    | some e => alE (fun ch a' b' => if ch then pg.sem r a' b' else pg.sem l a' b')
        (fun ch a' b' => if ch then pg.al r a' b' else pg.al l a' b') x l r a b e
    | none => 0

/-! ## static measures -/

/-- constructors in an expression -/
def E.mks : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => e₁.mks + e₂.mks
  | _, .mk _ ex el er => ex.mks + el.mks + er.mks + 1
  | _, .call _ ea eb => ea.mks + eb.mks
  | _, .ite c e₁ e₂ => c.mks + max e₁.mks e₂.mks
  | _, _ => 0

/-- calls on child `ch` -/
def E.calls (ch : Bool) : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => e₁.calls ch + e₂.calls ch
  | _, .mk _ ex el er => ex.calls ch + el.calls ch + er.calls ch
  | _, .call c ea eb => ea.calls ch + eb.calls ch + if c = ch then 1 else 0
  | _, .ite c e₁ e₂ => c.calls ch + max (e₁.calls ch) (e₂.calls ch)
  | _, _ => 0

/-- largest tag of a constructor -/
def E.tags : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => max e₁.tags e₂.tags
  | _, .mk t ex el er => max (max t ex.tags) (max el.tags er.tags)
  | _, .call _ ea eb => max ea.tags eb.tags
  | _, .ite c e₁ e₂ => max c.tags (max e₁.tags e₂.tags)
  | _, _ => 0

/-- temporaries used by `comp` beyond its first -/
def E.tmp : {k : Kd} → E rk k → Nat
  | _, .bin _ e₁ e₂ => max e₁.tmp (e₂.tmp + 1) + 1
  | _, .mk _ ex el er => max (max ex.tmp (el.tmp + 1)) (er.tmp + 2) + 1
  | _, .call _ ea eb => max ea.tmp (eb.tmp + 1) + 1
  | _, .ite c e₁ e₂ => max c.tmp (max e₁.tmp e₂.tmp) + 1
  | _, _ => 0

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

/-- `e` into variable `d`, temporaries from `n` -/
def comp (fi : Nat) : {k : Kd} → E rk k → Nat → Nat → CStmt
  | _, .x, d, _ => .base (asg d (vE 14))
  | _, .a, d, _ => .base (asg d (vE 9))
  | _, .k c, d, _ => .base (asg d (.const c))
  | _, .bin op e₁ e₂, d, n => .seq (comp fi e₁ n (n + 1)) (.seq (comp fi e₂ (n + 1) (n + 2))
      (.base (asg d (.bin op (vE n) (vE (n + 1))))))
  | _, .l, d, _ => .base (asg d (vE 15))
  | _, .r, d, _ => .base (asg d (vE 16))
  | _, .b, d, _ => .base (asg d (vE 10))
  | _, .nul, d, _ => .base (asg d (kE 0))
  | _, .mk t ex el er, d, n => .seq (comp fi ex n (n + 1)) (.seq (comp fi el (n + 1) (n + 2))
      (.seq (comp fi er (n + 2) (n + 3)) (.base (alloc (kE t) n (n + 1) (n + 2) d))))
  | _, .call ch ea eb, d, n => .seq (comp fi ea n (n + 1)) (.seq (comp fi eb (n + 1) (n + 2))
      (.call d fi [vE (if ch then 16 else 15), vE n, vE (n + 1)]))
  | _, .ite c e₁ e₂, d, n => .seq (comp fi c n (n + 1)) (.ite (vE n) (comp fi e₁ d (n + 1)) (comp fi e₂ d (n + 1)))

/-- the four words of the cell at `v_p` -/
def loads (p t x l r : Nat) : BStmt :=
  .seq (.load64 t 0 (vE p)) (.seq (.load64 x 0 (addE p 1)) (.seq (.load64 l 0 (addE p 2)) (.load64 r 0 (addE p 3))))

def eqE (v c : Nat) : BExp := .bin .eq (vE v) (kE c)

/-- one arm: a tail call continues the loop on the child, anything else is the result -/
def arm (fi : Nat) (e : E rk rk) : CStmt :=
  match e.tail? with
  | some (ch, ea, eb) => .seq (comp fi ea 17 18) (.seq (comp fi eb 18 19)
      (.base (.seq (asg 8 (vE (if ch then 16 else 15))) (.seq (asg 9 (vE 17)) (asg 10 (vE 18))))))
  | none => .seq (comp fi e 12 17) (.base (asg 11 (kE 0)))

def disp (fi : Nat) : List (E rk rk) → Nat → CStmt
  | [], _ => .base (.seq (asg 12 (kE 0)) (asg 11 (kE 0)))
  | e :: es, i => .ite (eqE 13 i) (arm fi e) (disp fi es (i + 1))

def fLoop (pg : Pg rk) : CStmt := .loop (vE 11) (.seq (.base (loads 8 13 14 15 16)) (disp 3 pg.arms 0))

def fFn (pg : Pg rk) : Fn := ⟨3, 16, .seq (.base (asg 11 (kE 1))) (fLoop pg), vE 12⟩

/-- `x` from the 8 bytes at the cursor (`j` bytes from the top, Horner), into `v_9`; byte temporary `v_12` -/
def rdB : Nat → BStmt
  | 0 => asg 9 (kE 0)
  | j + 1 => .seq (rdB j) (.seq (.load 12 0 (addE 4 (7 - j)))
      (asg 9 (.bin .add (.bin .shl (vE 9) (kE 8)) (vE 12))))

def dFld : Fld → CStmt
  | .x => .base (.seq (rdB 8) (asg 4 (addE 4 8)))
  | .l => .call 10 1 []
  | .r => .call 11 1 []

def dFlds : List Fld → CStmt
  | [] => .base (asg 9 (vE 9))
  | f :: fs => .seq (dFld f) (dFlds fs)

def dDisp : Shape → Nat → CStmt
  | [], _ => .base (asg 9 (vE 9))
  | fs :: sh, i => .ite (eqE 8 i) (dFlds fs) (dDisp sh (i + 1))

/-- `dec()`: locals `8` tag, `9` x, `10` l, `11` r, `12` byte; the cell after its children -/
def decFn (sh : Shape) : Fn :=
  ⟨0, 5, .seq (.base (.seq (.load 8 0 (vE 4)) (.seq (asg 4 (addE 4 1))
      (.seq (asg 9 (kE 0)) (.seq (asg 10 (kE 0)) (asg 11 (kE 0)))))))
    (.seq (dDisp sh 0) (.base (alloc (vE 8) 9 10 11 12))), vE 12⟩

/-- the low `j` bytes of `v_10` to the output at the cursor -/
def wrB : Nat → BStmt
  | 0 => asg 10 (vE 10)
  | j + 1 => .seq (wrB j) (.store 1 (addE 6 j) (.bin .lshr (vE 10) (kE (8 * j))))

def eFld : Fld → CStmt
  | .x => .base (.seq (wrB 8) (asg 6 (addE 6 8)))
  | .l => .call 13 2 [vE 11]
  | .r => .call 13 2 [vE 12]

def eFlds : List Fld → CStmt
  | [] => .base (asg 10 (vE 10))
  | f :: fs => .seq (eFld f) (eFlds fs)

def eDisp : Shape → Nat → CStmt
  | [], _ => .base (asg 10 (vE 10))
  | fs :: sh, i => .ite (eqE 9 i) (eFlds fs) (eDisp sh (i + 1))

/-- `enc(p)`: locals `8` p, `9` tag, `10` x, `11` l, `12` r, `13` dummy -/
def encFn (sh : Shape) : Fn :=
  ⟨1, 6, .seq (.base (.seq (loads 8 9 10 11 12) (.seq (.store 1 (vE 6) (vE 9)) (asg 6 (addE 6 1)))))
    (eDisp sh 0), kE 0⟩

/-- the entry: the second argument `b` of `F` -/
inductive BIn where
  /-- the second input -/
  | inp
  /-- a fresh nullary constructor -/
  | ctor (t : Nat)
  | none
  deriving DecidableEq

/-- `main()`: cell 0, decode, call `F`, the result to the output (a tree: its encoding, length returned; a word:
its low `nb` bytes) -/
def mainFn (bi : BIn) (a0 : BitVec 64) (tree : Bool) (nb : Nat) : Fn :=
  ⟨0, 6, .seq (.base (.seq (asg 4 (kE 0)) (.seq (asg 5 (kE 4)) (.seq (.store64 0 (kE 0) (kE 255))
      (.seq (.store64 0 (kE 1) (kE 0)) (.seq (.store64 0 (kE 2) (kE 0)) (.store64 0 (kE 3) (kE 0))))))))
    (.seq (.call 8 1 [])
    (.seq (match bi with
      | .inp => .call 9 1 []
      | .ctor t => .base (.seq (asg 11 (kE 0)) (alloc (kE t) 11 11 11 9))
      | .none => .base (asg 9 (kE 0)))
    (.seq (.base (asg 11 (.const a0))) (.seq (.call 10 3 [vE 8, vE 11, vE 9])
      (if tree then .seq (.base (asg 6 (kE 0))) (.call 13 2 [vE 10]) else .base (.seq (asg 6 (kE 0)) (wrB nb))))))),
    if tree then vE 6 else kE 0⟩

def indProg (sh : Shape) (pg : Pg rk) (bi : BIn) (a0 : BitVec 64) (nb : Nat) : Prog :=
  [mainFn bi a0 (rk = .t) nb, decFn sh, encFn sh, fFn pg]

/-- the tree parameter of the entry call -/
def BIn.val : BIn → C → C
  | .inp, v₂ => v₂
  | .ctor t, _ => .c t 0 .z .z
  | .none, _ => .z

/-- the input: the first value, then the second if `b` is an input -/
def inBytes (sh : Shape) : BIn → C → C → List UInt8
  | .inp, v₁, v₂ => v₁.enc sh ++ v₂.enc sh
  | _, v₁, _ => v₁.enc sh

/-- the output: a tree's encoding, or the low `nb` bytes of a word -/
def Kd.out (sh : Shape) (nb : Nat) : (k : Kd) → k.den → List UInt8
  | .t, y => C.enc sh y
  | .w, y => (leN 8 (BitVec.toNat (w := 64) y)).take nb

end Proven.Mach.Ind
