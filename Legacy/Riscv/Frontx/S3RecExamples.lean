/- **Recursion through S3** (`Testing/notes/S3_REC.md`): recursive functions compiled from their equation lemmas
(`f.eq_def`), certified by Lean's own induction principles (`f.induct`; `f.mutual_induct`, ONE induction for a whole
mutual component).  Each entry: `main = encodeOut ∘ f ∘ decodeIn` (byte formats below and in `S3IO.lean`), the S3
program, certificates, `computes`, `correct` (exactly the Sail axioms).  Tests: `Testing/asm/emit_s3rec.lean`,
`python3 Testing/asm/ir_test.py check 50 s3_<name>`. Part (a) (structural) is in S3RecExamplesA.lean.

| entry | function under test | recursion |
|---|---|---|
| `S3Incs` | `Mach.IR.SR.incs` (self-hoster, verbatim) | structural (`List.brecOn`), `Nat`, result `Code Nat` |
| `S3Inits` | `Mach.IR.SR.inits` (verbatim) | structural (`List.brecOn`), extra `Nat` parameter |
| `S3Sets` | `Mach.IR.Hoist.sets` (verbatim) | structural (`List.brecOn`), `Nat` accumulator `m + 1` (`Nat.add`) |
| `S3InitL` | `Mach.initL` (verbatim, static `sp : Nat → Bool`) | structural (`List.brecOn`), `Nat.beq`/`Nat.blt` |
| `S3Merge` | `merge` | well-founded (`termination_by xs.length + ys.length`), not structural |
| `S3EvOd` | `evSum` / `odCnt` | mutual, different result types, non-tail calls |
| `S3Lex` | `lex` | lexicographic `(xs.length, k.toNat)`, the inner counter resets |
-/
import Legacy.Riscv.Frontx.S3RecExamplesA

namespace Proven.S3.Rec
open Proven.S3 Proven.S3.Ex Proven.Mach.IR

/-! ## (b) well-founded, not structural -/


/-- (b) well-founded, not structural: merge by total length -/
def merge : List UInt64 → List UInt64 → List UInt64
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- the words of the input, split at the first zero word, merged -/
def splitZ : List UInt64 → List UInt64 × List UInt64
  | [] => ([], [])
  | x :: r => if x = 0 then ([], r) else match splitZ r with | (a, b) => (x :: a, b)
def mergeMain (bs : List UInt8) : List UInt8 :=
  match splitZ (decW bs) with
  | (a, b) => encW (merge a b)
s3_compile S3Merge := mergeMain

/-! ## (c) mutual and (d) lexicographic -/


mutual
/-- (c) mutual, different result types, non-tail calls -/
def evSum : List UInt64 → List UInt64
  | [] => []
  | x :: r => (x + odCnt r) :: evSum r
def odCnt : List UInt64 → UInt64
  | [] => 0
  | x :: r => match evSum r with
    | [] => x
    | y :: _ => x * 2 + y
end

/-- (d) lexicographic measure; the inner counter resets from the next word -/
def lex : List UInt64 → UInt64 → UInt64 → UInt64
  | [], _, acc => acc
  | x :: r, k, acc =>
    if h : k = 0 then lex r (x &&& 7) (acc + x) else lex (x :: r) (k - 1) (acc * 3 + k)
termination_by xs k => (xs.length, k.toNat)
decreasing_by
  · exact Prod.Lex.left _ _ (by simp)
  · apply Prod.Lex.right
    have hk : k.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
def evMain (bs : List UInt8) : List UInt8 := encW (evSum (decW bs))
s3_compile S3EvOd := evMain
def lexMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | k :: r => enc8 (lex r k 1)
  | [] => []
s3_compile S3Lex := lexMain
end Proven.S3.Rec
