-- differential test of inlV against inlB (run: lake env lean Testing/nano/v2s_inl_test.lean)
import Legacy.Nano.V2S.Inl
open Nano Nano.V2S Nano.U
-- random generator: LCG
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def gen : Nat → Nat → List UInt8 → List UInt8 × Nat
  | 0, s, acc => (acc.reverse, s)
  | n+1, s, acc =>
    let s1 := lcg s; let r := (s1 >>> 33) % 100
    let m : Nat := if r < 15 then 13 else if r < 25 then 14 else if r < 50 then 15 else (s1 >>> 20) % 13
    let s2 := lcg s1
    let x : Nat := if m == 14 then (s2 >>> 33) % 2 else (s2 >>> 33) % 6
    gen n s2 ((x.toUInt8) :: (m.toUInt8) :: acc)
def test : Nat → Nat → Nat → Nat
  | 0, _, bad => bad
  | k+1, s, bad =>
    let (xs, s') := gen (k % 23) s []
    let xs := if k % 3 == 0 then xs ++ [7] else xs
    test k s' (if inlV xs == inlB xs then bad else bad + 1)
#eval test 400 7 0
#eval (inlB [1,2,13,0,15,0,15,0,13,1,15,0,15,1,13,2]).length
#eval inlV [1,2,13,0,15,0,15,0,13,1,15,0,15,1,13,2] == inlB [1,2,13,0,15,0,15,0,13,1,15,0,15,1,13,2]
