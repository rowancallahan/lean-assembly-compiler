/- nano: the program as a micro-op stream, `ser : Prog → List UInt8` (integration, nano-int), and
**`mexp_ser : mexp (ser p) = genR p`**: the stack generator is the micro-op expander (`Nano/Expand.lean`, a compiled
stage) after `ser`.  `ser` mirrors `genR` node by node (postfix order, stack-relative slots, calls inlined), so
`ser ∘ nanoElab` is what a one-pass byte-level front end has to emit.
Property used by such a front end: `serE` of a callee body does not depend on the call site (slots are relative). -/
import Nano.Gen
import Nano.Expand

namespace Nano

/-- one micro-op -/
def mo (m x : UInt8) : List UInt8 := [m, x]

/-- t0 := n -/
def sLi (n : UInt64) : List UInt8 :=
  mo 5 0 ++ mo 6 ((n >>> 56).toUInt8) ++ mo 6 ((n >>> 48).toUInt8) ++ mo 6 ((n >>> 40).toUInt8) ++
  mo 6 ((n >>> 32).toUInt8) ++ mo 6 ((n >>> 24).toUInt8) ++ mo 6 ((n >>> 16).toUInt8) ++ mo 6 ((n >>> 8).toUInt8) ++
  mo 6 (n.toUInt8)

mutual
def serE : List Nat → Nat → Ex → List UInt8
  | _, _, .num n => sLi n ++ mo 3 0
  | sc, d, .var i => mo 7 (d - 1 - sc.getD i 0).toUInt8 ++ mo 3 0
  | sc, d, .add a b => serE sc d a ++ serE sc (d + 1) b ++ mo 8 24
  | sc, d, .sub a b => serE sc d a ++ serE sc (d + 1) b ++ mo 8 32
  | sc, d, .mul a b => serE sc d a ++ serE sc (d + 1) b ++ mo 8 40
  | sc, d, .let_ v b => serE sc d v ++ serE (d :: sc) (d + 1) b ++ mo 9 1
  | sc, d, .call b as => serA sc d as ++ serE (mkSc (cnt as) d) (d + cnt as) b ++ mo 9 (cnt as).toUInt8
  | _, _, _ => []
def serA : List Nat → Nat → Ex → List UInt8
  | sc, d, .acons e r => serE sc d e ++ serA sc (d + 1) r
  | _, _, _ => []
end

/-- one argument: read its 8 bytes, push, advance -/
def sArg : List UInt8 :=
  mo 1 0 ++ mo 2 6 ++ mo 2 5 ++ mo 2 4 ++ mo 2 3 ++ mo 2 2 ++ mo 2 1 ++ mo 2 0 ++ mo 3 0 ++ mo 4 0

def serPro : Nat → List UInt8
  | 0 => []
  | k + 1 => sArg ++ serPro k

/-- the result: 8 bytes -/
def sWr : List UInt8 :=
  mo 10 0 ++ mo 11 0 ++ mo 10 8 ++ mo 11 1 ++ mo 10 16 ++ mo 11 2 ++ mo 10 24 ++ mo 11 3 ++
  mo 10 32 ++ mo 11 4 ++ mo 10 40 ++ mo 11 5 ++ mo 10 48 ++ mo 11 6 ++ mo 10 56 ++ mo 11 7

/-- **the micro-op stream of a program** -/
def ser (p : Prog) : List UInt8 :=
  mo 0 0 ++ serPro p.1 ++ serE (mkSc p.1 0) p.1 p.2 ++ mo 7 0 ++ sWr ++ mo 12 0

/-! ## `mexp ∘ ser = genR` -/

theorem mexp_sLi (n : UInt64) (rest : List UInt8) : mexp (sLi n ++ rest) = li n ++ mexp rest := by
  simp [sLi, mo, mexp, li, r]

theorem mexp_push (rest : List UInt8) : mexp (mo 3 0 ++ rest) = push ++ mexp rest := by
  simp [mo, mexp, push, sd, r]

theorem mexp_ldv (k : Nat) (rest : List UInt8) : mexp (mo 7 k.toUInt8 ++ rest) = ld 5 31 k ++ mexp rest := by
  simp [mo, mexp, ld, r]

theorem mexp_bin (k : UInt8) (rest : List UInt8) : mexp (mo 8 k ++ rest) = binop k ++ mexp rest := by
  simp [mo, mexp, binop, ld, sd, addSp, r]

theorem mexp_nip (k : Nat) (rest : List UInt8) :
    mexp (mo 9 k.toUInt8 ++ rest) = ld 5 31 0 ++ addSp k ++ sd 5 31 0 ++ mexp rest := by
  simp [mo, mexp, ld, sd, addSp, r]

mutual
theorem mexp_serE : ∀ (e : Ex) (sc : List Nat) (d : Nat) (rest : List UInt8),
    mexp (serE sc d e ++ rest) = genE sc d e ++ mexp rest
  | .num n, sc, d, rest => by
    simp only [serE, genE, List.append_assoc, mexp_sLi, mexp_push]
  | .var i, sc, d, rest => by
    simp only [serE, genE, List.append_assoc, mexp_ldv, mexp_push]
  | .add a b, sc, d, rest => by
    simp only [serE, genE, List.append_assoc, mexp_serE a, mexp_serE b, mexp_bin]
  | .sub a b, sc, d, rest => by
    simp only [serE, genE, List.append_assoc, mexp_serE a, mexp_serE b, mexp_bin]
  | .mul a b, sc, d, rest => by
    simp only [serE, genE, List.append_assoc, mexp_serE a, mexp_serE b, mexp_bin]
  | .let_ v b, sc, d, rest => by
    have h := mexp_nip 1 rest
    simp only [serE, genE, List.append_assoc, mexp_serE v, mexp_serE b] at h ⊢
    exact congrArg _ (congrArg _ h)
  | .call b as, sc, d, rest => by
    simp only [serE, genE, List.append_assoc, mexp_serA as, mexp_serE b, mexp_nip]
  | .anil, sc, d, rest => by simp only [serE, genE, List.nil_append]
  | .acons _ _, sc, d, rest => by simp only [serE, genE, List.nil_append]
theorem mexp_serA : ∀ (e : Ex) (sc : List Nat) (d : Nat) (rest : List UInt8),
    mexp (serA sc d e ++ rest) = genA sc d e ++ mexp rest
  | .acons e r, sc, d, rest => by simp only [serA, genA, List.append_assoc, mexp_serE e, mexp_serA r]
  | .num _, _, _, _ | .var _, _, _, _ | .add _ _, _, _, _ | .sub _ _, _, _, _ | .mul _ _, _, _, _
  | .let_ _ _, _, _, _ | .call _ _, _, _, _ | .anil, _, _, _ => by simp only [serA, genA, List.nil_append]
end

theorem mexp_sArg (rest : List UInt8) : mexp (sArg ++ rest) = rd8 ++ push ++ r 8 28 28 1 ++ mexp rest := by
  simp [sArg, mo, mexp, rd8, push, sd, r, List.range, List.range.loop]

theorem mexp_serPro : ∀ (k : Nat) (rest : List UInt8), mexp (serPro k ++ rest) = pro k ++ mexp rest
  | 0, rest => rfl
  | k + 1, rest => by simp only [serPro, pro, List.append_assoc, mexp_sArg, mexp_serPro k]

theorem mexp_tail : mexp (mo 7 0 ++ sWr ++ mo 12 0) = ld 5 31 0 ++ wr8 ++ r 48 0 1 0 := by
  simp [sWr, mo, mexp, ld, wr8, r, List.range, List.range.loop]

/-- **the stack generator = the compiled expander after `ser`** -/
theorem mexp_ser (p : Prog) : mexp (ser p) = genR p := by
  have h0 : ∀ rest, mexp (mo 0 0 ++ rest) = r 0 31 2 0 ++ r 0 28 10 0 ++ mexp rest := fun rest => by
    simp [mo, mexp, r]
  simp only [ser, genR, List.append_assoc, h0, mexp_serPro, mexp_serE]
  have := mexp_tail; simp only [List.append_assoc] at this; rw [this]

end Nano
