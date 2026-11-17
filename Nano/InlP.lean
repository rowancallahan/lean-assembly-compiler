/- nano inliner stage as a paged machine (branch `nano-closeB`): `inlP : ByteArray → ByteArray`, in the shape the paged
front end (`wp_compile`) accepts, equal to `Nano.U.inlB` when the inliner's table fits the buffer (`inlP_eq`,
`Nano/InlPProof.lean`).

ONE work array `ob : Array Nat` (the paged front end allows one changing array per loop), `CAP` cells, preallocated:
* cells `0 … 65536`: `ob[j]` = start of the inlined body of def `j` (relative to `BASE`); `65537`: dummy;
* cell `HD = 65538`: header `start * 2^24 + (end + 1)` of the last closed def (`0`: none);
* cells `BASE + q`: the inlined bodies, oldest first, each followed by its arity byte.
Main loop (one step = one input byte, or one copied byte; every step writes three cells with `set!`): parity `ph`,
micro-op `m`, write position `w`, closed defs `n`, high callee byte `hi`, copy mode `cp`/`rem`, start `cs` of the current
body.  Emit loop: `wrap k body` byte by byte. -/
import Nano.SerU

namespace Nano.IP
open Nano

/-- start of the byte region -/
abbrev BASE : Nat := 65540
/-- writable bytes -/
abbrev WCAP : Nat := 262136
/-- cells -/
abbrev CAP : Nat := 327680
/-- header cell -/
abbrev HD : Nat := 65538

/-- the main loop -/
def mn (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat) : Array Nat :=
  if i < src.size then
    mn (((ob.set! (BASE + w)
          (if 0 < rem then ob[BASE + cp]!
           else if ph == 0 then (if src.get! i == 13 || src.get! i == 14 || src.get! i == 15 then ob[BASE + w]!
                                 else (src.get! i).toNat)
           else if m == 14 || m == 15 then ob[BASE + w]!
           else (src.get! i).toNat)).set!
          (if n < 65536 then n + 1 else 65537)
          (if 0 < rem then ob[if n < 65536 then n + 1 else 65537]!
           else if ph == 1 && m == 13 then w + 1 else ob[if n < 65536 then n + 1 else 65537]!)).set!
          HD
          (if 0 < rem then ob[HD]!
           else if ph == 1 && m == 13 then cs * 16777216 + w + 1 else ob[HD]!))
       src
       (if 0 < rem then i else i + 1 + 0 * w)
       (if 0 < rem then ph else if ph == 0 then 1 else 0)
       (if 0 < rem then m else if ph == 0 then (src.get! i).toNat else m)
       (if 0 < rem then (if w < WCAP then w + 1 else w)
        else if ph == 0 then
          (if src.get! i == 13 || src.get! i == 14 || src.get! i == 15 then w else if w < WCAP then w + 1 else w)
        else if m == 14 || m == 15 then w
        else if w < WCAP then w + 1 else w)
       (if 0 < rem then n else if ph == 1 && m == 13 then n + 1 else n)
       (if 0 < rem then hi else if ph == 1 && m == 14 then (src.get! i).toNat else hi)
       (if 0 < rem then cp + 1
        else if ph == 1 && m == 15 && hi * 256 + (src.get! i).toNat < n then
          (if ob[hi * 256 + (src.get! i).toNat]! < WCAP then ob[hi * 256 + (src.get! i).toNat]! else WCAP)
        else cp)
       (if 0 < rem then rem - 1
        else if ph == 1 && m == 15 && hi * 256 + (src.get! i).toNat < n then
          (if ob[hi * 256 + (src.get! i).toNat + 1]! - 1 - ob[hi * 256 + (src.get! i).toNat]! < WCAP
           then ob[hi * 256 + (src.get! i).toNat + 1]! - 1 - ob[hi * 256 + (src.get! i).toNat]! else WCAP)
        else 0)
       (if 0 < rem then cs else if ph == 1 && m == 13 then (if w < WCAP then w + 1 else w) else cs)
  else ob
termination_by (src.size - i) * (WCAP + 1) + rem
decreasing_by
  all_goals
    rename_i h
    simp only [WCAP] at *
    by_cases hr : 0 < rem
    · simp only [hr, dite_true]; omega
    · simp only [hr, dite_false, Nat.mul_zero, Nat.add_zero]
      split <;> (try split) <;> omega

/-- byte `s` (`< 20`) of `sArg` -/
def argB (s : Nat) : UInt8 :=
  if s % 2 == 0 then (if s == 0 then 1 else if s < 16 then 2 else if s == 16 then 3 else 4)
  else if s == 1 || 15 < s then 0 else UInt8.ofNat ((15 - s) / 2)

/-- byte `v` (`< 32`) of `sWr` -/
def wrB (v : Nat) : UInt8 :=
  if v % 4 == 0 then 10 else if v % 4 == 1 then UInt8.ofNat (8 * (v / 4)) else if v % 4 == 2 then 11
  else UInt8.ofNat (v / 4)

/-- the emit loop: `wrap k (body at BASE + ls, length len)`, byte `t` -/
def em (out : ByteArray) (ob : Array Nat) (t ls len k : Nat) : ByteArray :=
  if t < 20 * k + len + 38 then
    em (out.push
        (if t < 2 then 0
         else if t < 2 + 20 * k then argB ((t - 2) % 20)
         else if t < 2 + 20 * k + len then UInt8.ofNat ob[BASE + ls + (t - 2 - 20 * k)]!
         else if t == 2 + 20 * k + len then 7
         else if t == 3 + 20 * k + len then 0
         else if t < 36 + 20 * k + len then wrB (t - 4 - 20 * k - len)
         else if t == 36 + 20 * k + len then 12 else 0))
      ob (t + 1) ls len k
  else out
termination_by 20 * k + len + 38 - t

/-- **the inliner stage** -/
def inlP (xs : ByteArray) : ByteArray :=
  let ob := mn (Array.replicate CAP 0) xs 0 0 0 0 0 0 0 0 0
  let ls := ob[HD]! / 16777216 % 16777216
  let le := ob[HD]! % 16777216
  em (xs.extract 0 0) ob 0 ls (le - 1 - ls) (if le == 0 then 0 else ob[BASE + (le - 1)]! % 256)

end Nano.IP
