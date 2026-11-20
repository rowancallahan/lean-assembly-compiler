/- nano micro-op expander (integration, nano-int): a byte-level stage of the stack generator.  The generator `genR`
(`Nano/Gen.lean`) factors as `genR p = mexp (ser p)` (`Nano/Ser.lean`): `ser p` is the program as a flat stream of
2-byte micro-ops `[m, x]`, `mexp` expands each micro-op to its records.  `mexp` is in the front end's list style (one
pass, no helpers) so that OUR compiler compiles it (`Nano/ExpandSelf.lean`).
   0 HDR  t6 := sp & ~7; t3 := a0                   1 LB0     t0 := byte 7 of the argument at t3
   2 LBJ x               t0 := t0 << 8 | byte x at t3          3 PUSH    push t0 (with the out-of-memory check)
   4 ADV                 t3 += 8                               5 ZERO    t0 := 0
   6 SHOR x              t0 := t0 << 8 | x                     7 LDV x   t0 := stack slot x
   8 BIN x               pop b, a; push a (x) b (x = 24 add, 32 sub, 40 mul)
   9 NIP x               top := pop; drop x slots; push top   10 SRL x   t1 := t0 >> x
  11 SB x                byte x of the output := t1            other     RET -/
namespace Nano

def mexp : List UInt8 → List UInt8
  | m :: x :: rest =>
    if m == 0 then 5 :: 31 :: 2 :: 3 :: 1 :: 31 :: 31 :: 3 :: 0 :: 28 :: 10 :: 0 :: mexp rest
    else if m == 1 then 4 :: 5 :: 28 :: 7 :: mexp rest
    else if m == 2 then 1 :: 5 :: 5 :: 8 :: 4 :: 6 :: 28 :: x :: 14 :: 5 :: 5 :: 6 :: mexp rest
    else if m == 3 then 0 :: 31 :: 31 :: 248 :: 7 :: 0 :: 31 :: 12 :: 0 :: 10 :: 0 :: 255 :: 48 :: 0 :: 1 :: 0 :: 11 :: 5 :: 31 :: 0 :: mexp rest
    else if m == 4 then 8 :: 28 :: 28 :: 1 :: mexp rest
    else if m == 5 then 0 :: 5 :: 0 :: 0 :: mexp rest
    else if m == 6 then 1 :: 5 :: 5 :: 8 :: 6 :: 5 :: 5 :: x :: mexp rest
    else if m == 7 then 3 :: 5 :: 31 :: x :: mexp rest
    else if m == 8 then 3 :: 6 :: 31 :: 0 :: 3 :: 5 :: 31 :: 1 :: 8 :: 31 :: 31 :: 1 :: x :: 5 :: 5 :: 6 :: 11 :: 5 :: 31 :: 0 :: mexp rest
    else if m == 9 then 3 :: 5 :: 31 :: 0 :: 8 :: 31 :: 31 :: x :: 11 :: 5 :: 31 :: 0 :: mexp rest
    else if m == 10 then 5 :: 6 :: 5 :: x :: mexp rest
    else if m == 11 then 16 :: 6 :: 13 :: x :: mexp rest
    else 48 :: 0 :: 1 :: 0 :: mexp rest
  | _ => []

end Nano
