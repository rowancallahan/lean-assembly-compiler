/- nano inliner stage as a paged machine (branch `nano-closeB`): `inlP : ByteArray → ByteArray`, the shape the paged
front end (`wp_compile`) accepts, equal to `Nano.U.inlB` when the inliner's table fits the buffer (`inlP_eq`).

Buffer `ob` (`CAP` bytes, preallocated, written only with `set!`, one cell per step): the inlined bodies of the defs,
oldest first, each followed by its arity byte; `st` (`Array Nat`, `65537` cells): `st[j]` = start of body `j`.
Main loop (one step = one input byte, or one copied byte): parity `ph` (micro-op byte / argument byte), `m` the
micro-op, `w` the write position, `n` closed defs, `hi` the high callee byte, copy mode `cp`/`rem`, `cs` the start of
the current body, `ls`/`le`/`k` the last closed def.  At the end the header (last `8` cells) gets `ls`, `le - ls`, `k`.
Emit loop: `wrap k body` byte by byte. -/
import Nano.SerU

namespace Nano.IP
open Nano

/-- buffer capacity -/
abbrev CAP : Nat := 262144
/-- writable part (the header is the last 8 cells) -/
abbrev WCAP : Nat := 262136

/-- preallocate `CAP` zero bytes -/
def fill (b : ByteArray) (i : Nat) : ByteArray :=
  if i < CAP then fill (b.push 0) (i + 1) else b
termination_by CAP - i

/-- the main loop -/
def mn (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs ls le k : Nat) : ByteArray :=
  if i < src.size then
    mn (ob.set! w
          (if 0 < rem then ob.get! cp
           else if ph == 0 then (if src.get! i == 13 || src.get! i == 14 || src.get! i == 15 then ob.get! w
                                 else src.get! i)
           else if m == 14 || m == 15 then ob.get! w
           else src.get! i))
       (st.set! (n + 1)
          (if 0 < rem then st[n + 1]!
           else if ph == 1 && m == 13 then w + 1 else st[n + 1]!))
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
          (if st[hi * 256 + (src.get! i).toNat]! < WCAP then st[hi * 256 + (src.get! i).toNat]! else WCAP)
        else cp)
       (if 0 < rem then rem - 1
        else if ph == 1 && m == 15 && hi * 256 + (src.get! i).toNat < n then
          (if st[hi * 256 + (src.get! i).toNat + 1]! - 1 - st[hi * 256 + (src.get! i).toNat]! < WCAP
           then st[hi * 256 + (src.get! i).toNat + 1]! - 1 - st[hi * 256 + (src.get! i).toNat]! else WCAP)
        else 0)
       (if 0 < rem then cs else if ph == 1 && m == 13 then (if w < WCAP then w + 1 else w) else cs)
       (if 0 < rem then ls else if ph == 1 && m == 13 then cs else ls)
       (if 0 < rem then le else if ph == 1 && m == 13 then w else le)
       (if 0 < rem then k else if ph == 1 && m == 13 then (src.get! i).toNat else k)
  else
    ((((((ob.set! WCAP (UInt8.ofNat (ls % 256))).set! (WCAP + 1) (UInt8.ofNat (ls / 256 % 256))).set! (WCAP + 2)
      (UInt8.ofNat (ls / 65536 % 256))).set! (WCAP + 3) (UInt8.ofNat ((le - ls) % 256))).set! (WCAP + 4)
      (UInt8.ofNat ((le - ls) / 256 % 256))).set! (WCAP + 5) (UInt8.ofNat ((le - ls) / 65536 % 256))).set! (WCAP + 6)
      (UInt8.ofNat k)
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
  if v % 4 == 0 then 10 else if v % 4 == 1 then UInt8.ofNat (8 * (v / 4)) else if v % 4 == 2 then 11 else UInt8.ofNat (v / 4)

/-- the emit loop: `wrap k (body at ls, length len)`, byte `t` -/
def em (out ob : ByteArray) (t ls len k : Nat) : ByteArray :=
  if t < 20 * k + len + 38 then
    em (out.push
        (if t < 2 then 0
         else if t < 2 + 20 * k then argB ((t - 2) % 20)
         else if t < 2 + 20 * k + len then ob.get! (ls + (t - 2 - 20 * k))
         else if t == 2 + 20 * k + len then 7
         else if t == 3 + 20 * k + len then 0
         else if t < 36 + 20 * k + len then wrB (t - 4 - 20 * k - len)
         else if t == 36 + 20 * k + len then 12 else 0))
      ob (t + 1) ls len k
  else out
termination_by 20 * k + len + 38 - t

/-- **the inliner stage** -/
def inlP (xs : ByteArray) : ByteArray :=
  let ob := mn (fill (xs.extract 0 0) 0) (Array.replicate 65537 0) xs 0 0 0 0 0 0 0 0 0 0 0 0
  em (xs.extract 0 0) ob 0
    ((ob.get! WCAP).toNat + 256 * (ob.get! (WCAP + 1)).toNat + 65536 * (ob.get! (WCAP + 2)).toNat)
    ((ob.get! (WCAP + 3)).toNat + 256 * (ob.get! (WCAP + 4)).toNat + 65536 * (ob.get! (WCAP + 5)).toNat)
    (ob.get! (WCAP + 6)).toNat

end Nano.IP
