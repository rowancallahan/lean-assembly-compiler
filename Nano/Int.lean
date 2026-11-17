/- nano `Int64` programs.  An `Int64` program elaborates to the same `Ex` as a `UInt64` one (numerals as their
two's complement bits, `-n` as `0 - n`), so the code generator and its proof are shared.  This file gives the
`Int64` meaning directly with Lean's `Int64` operations (`denI`, `Prog.evalI`) and proves it is the bit-level
meaning (`denI_toUInt64`, `evalI_eq`), and that the byte-level program meaning `nanoRun` (8-byte little-endian two's
complement words) computes `Prog.evalI` (`nanoRun_int`). -/
import Nano.Proof

namespace Nano
open Proven

mutual
/-- the `Int64` meaning of an expression (Lean's `Int64` `+ - *`, numerals as `UInt64.toInt64`) -/
def denI : Ex → List Int64 → Int64
  | .num n, _ => n.toInt64
  | .var i, env => env.getD i 0
  | .add a b, env => denI a env + denI b env
  | .sub a b, env => denI a env - denI b env
  | .mul a b, env => denI a env * denI b env
  | .let_ v b, env => denI b (denI v env :: env)
  | .call b as, env => denI b (denAI as env).reverse
  | .anil, _ => 0
  | .acons _ _, _ => 0
def denAI : Ex → List Int64 → List Int64
  | .acons e r, env => denI e env :: denAI r env
  | _, _ => []
end

/-- the `Int64` meaning of a program -/
def Prog.evalI (p : Prog) (args : List Int64) : Option Int64 :=
  if args.length = p.1 then some (denI p.2 args.reverse) else none

theorem getD_map_toUInt64 (env : List Int64) (i : Nat) :
    (env.map Int64.toUInt64).getD i 0 = (env.getD i 0).toUInt64 := by
  simp [List.getD_eq_getElem?_getD]; cases env[i]? <;> rfl

mutual
/-- **`Int64` = bits**: the `Int64` meaning is the `UInt64` meaning on the two's complement bits -/
theorem denI_toUInt64 : ∀ (e : Ex) (env : List Int64), (denI e env).toUInt64 = den e (env.map Int64.toUInt64)
  | .num n, _ => by simp [denI, den]
  | .var i, env => by simp only [denI, den]; rw [getD_map_toUInt64]
  | .add a b, env => by simp only [denI, den]; rw [Int64.toUInt64_add, denI_toUInt64 a, denI_toUInt64 b]
  | .sub a b, env => by simp only [denI, den]; rw [Int64.toUInt64_sub, denI_toUInt64 a, denI_toUInt64 b]
  | .mul a b, env => by simp only [denI, den]; rw [Int64.toUInt64_mul, denI_toUInt64 a, denI_toUInt64 b]
  | .let_ v b, env => by simp only [denI, den]; rw [denI_toUInt64 b, List.map_cons, denI_toUInt64 v]
  | .call b as, env => by simp only [denI, den]; rw [denI_toUInt64 b, List.map_reverse, denAI_toUInt64 as]
  | .anil, _ => rfl
  | .acons _ _, _ => rfl
theorem denAI_toUInt64 : ∀ (e : Ex) (env : List Int64),
    (denAI e env).map Int64.toUInt64 = denA e (env.map Int64.toUInt64)
  | .acons e r, env => by simp only [denAI, denA, List.map_cons]; rw [denI_toUInt64 e, denAI_toUInt64 r]
  | .num _, _ => rfl
  | .var _, _ => rfl
  | .add _ _, _ => rfl
  | .sub _ _, _ => rfl
  | .mul _ _, _ => rfl
  | .let_ _ _, _ => rfl
  | .call _ _, _ => rfl
  | .anil, _ => rfl
end

/-- **`Prog.evalI` is `Prog.eval` on the bits** -/
theorem evalI_eq (p : Prog) (args : List Int64) :
    p.evalI args = (p.eval (args.map Int64.toUInt64)).map UInt64.toInt64 := by
  unfold Prog.evalI Prog.eval
  simp only [List.length_map]
  split
  · simp only [Option.map_some, Option.some.injEq]
    rw [← List.map_reverse, ← denI_toUInt64, Int64.toInt64_toUInt64]
  · rfl

/-! ## bytes: 8-byte little-endian two's complement -/

/-- an `Int64` as 8 little-endian bytes (two's complement) -/
def encI (v : Int64) : List UInt8 := leN 8 v.toUInt64.toNat

/-- the arguments, one 8-byte word each -/
def encIs (args : List Int64) : List UInt8 := args.flatMap encI

theorem wordsOf_encIs : ∀ args : List Int64, wordsOf args.length (encIs args) = some (args.map Int64.toUInt64)
  | [] => rfl
  | a :: as => by
    have h8 : (encI a).length = 8 := leN_length _ _
    have hd : (encIs (a :: as)).drop 8 = encIs as := by
      simp only [encIs, List.flatMap_cons]; rw [← h8, List.drop_left]
    have ht : (encIs (a :: as)).take 8 = encI a := by
      simp only [encIs, List.flatMap_cons]; rw [← h8, List.take_left]
    have hl : 8 ≤ (encIs (a :: as)).length := by simp only [encIs, List.flatMap_cons, List.length_append]; omega
    simp only [List.length_cons, wordsOf, if_pos hl, hd, ht, wordsOf_encIs as, Option.map_some, List.map_cons]
    congr
    unfold encI; rw [Proven.Ir.IndLow.unle_leN8 _ a.toUInt64.toNat_lt]; simp

/-- **the byte-level meaning computes `Prog.evalI`**: for every `Int64` argument list of the program's arity -/
theorem nanoRun_int (p : Prog) (args : List Int64) (h : args.length = p.1) :
    nanoRun p (encIs args) = (p.evalI args).map encI := by
  unfold nanoRun
  rw [← h, wordsOf_encIs, Option.bind_some, evalI_eq]
  cases p.eval (args.map Int64.toUInt64) <;> simp [encI]

end Nano
