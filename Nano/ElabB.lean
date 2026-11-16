import Nano.Elab
/- nanoElabB, stage 1 (`lexB`): the lexer of `nanoElab` (`lex` + `uniTy`) as a byte-level state machine in the
front end's list style (one function, explicit recursion on a measure, UInt8/UInt64 scalars, one output byte per
step).  Two passes over the input: pass 1 (`m = 0`) validates and computes the program's type; pass 2 (`m = 1`,
restarted on the bookmark view `o`) emits `encLexT`: a header byte (`0` rejected, `1` UInt64, `2` Int64) and the
tokens (`encTok`).
Every step consumes one byte `c` and looks at the next one `n` (32 at the end: `e`).
States `st`: 0 between tokens, 1 in a word, 2 skip the `=` of `:=`, 3 in a numeral.  `sp`: `lex`'s fuel exceeds the
rest of the input (0 until the first token longer than its fuel cost); with `sp = 0` a word that runs to the end of
the input is split before its last character, exactly as `lex xs.length xs` does.
In a word, `d`/`w` include the current character, `d0` excludes it: `d` is the name-shape automaton (1..3 = 1..3
lowercase letters, 4 = digits, 5 = after `_`, 6 = dead), `w` the word packed behind a sentinel byte 1 (`2^63` beyond
7 characters).  In a numeral `w` is 0 on its first digit.  `ty`: the type seen so far (0 none, 1 UInt64, 2 Int64).
Token bytes (`encTok`): `( ) * + - ; : :=` as `40 41 42 43 45 59 58 61`; a word as its characters and a kind byte
(0 name, 1 `def`, 2 `let`, 3 `UInt64`, 4 `Int64`); a numeral as 5, its digits, 6. -/
namespace Nano.B

/-- the name-shape automaton step from `dd` on `ch` -/
macro "DSTEP" dd:term "," ch:term : term => `(if $dd == 6 then (6 : UInt64) else if $dd == 5 then (if 48 ≤ $ch && $ch ≤ 57 then 4 else 6)
  else if 97 ≤ $ch && $ch ≤ 122 && $dd ≤ 2 then $dd + 1 else if $dd == 0 then 6
  else if 48 ≤ $ch && $ch ≤ 57 then 4 else if $ch == 95 then 5 else 6)
macro "WSTEP" ww:term "," ch:term : term =>
  `(if $ww < 0x100000000000000 then ($ww <<< 8) ||| ($ch).toUInt64 else (0x8000000000000000 : UInt64))
/-- the kind of the word (`dd`, `ww`): 0 name, 1 `def`, 2 `let`, 3 `UInt64`, 4 `Int64`, 9 rejected -/
macro "KIND" dd:term "," ww:term : term => `(if $ww == 0x1646566 then (1 : UInt64) else if $ww == 0x16c6574 then 2
  else if $ww == 0x155496e743634 then 3 else if $ww == 0x1496e743634 then 4
  else if 1 ≤ $dd && $dd ≤ 4 && !($ww == 0x1616e64 || $ww == 0x16174 || $ww == 0x1626966 || $ww == 0x1626e65 ||
    $ww == 0x16279 || $ww == 0x1646f || $ww == 0x1656e64 || $ww == 0x1666f72 || $ww == 0x166756e ||
    $ww == 0x1676574 || $ww == 0x16964 || $ww == 0x16966 || $ww == 0x1696e || $ww == 0x1697465 ||
    $ww == 0x16d6178 || $ww == 0x16d696e || $ww == 0x16d74 || $ww == 0x16d7574 || $ww == 0x16e6f74 ||
    $ww == 0x16f72 || $ww == 0x172666c || $ww == 0x1736574 || $ww == 0x1747279 || $ww == 0x1786f72) then 0 else 9)
set_option hygiene false in
/-- the type after the word `ww` (9: a conflict) -/
macro "TYU" ww:term : term => `(if $ww == 0x155496e743634 then (if ty == 2 then (9 : UInt64) else 1)
  else if $ww == 0x1496e743634 then (if ty == 1 then (9 : UInt64) else 2) else ty)

set_option hygiene false in
/-- the automaton after the first two characters `c`, `n` of a word -/
macro "DSTEP0" n:term : term => `(if 97 ≤ c && c ≤ 122 then (if 97 ≤ $n && $n ≤ 122 then (2 : UInt64)
  else if 48 ≤ $n && $n ≤ 57 then 4 else if $n == 95 then 5 else 6) else 6)

def isL (c : UInt8) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95
def isW (c : UInt8) : Bool := isL c || (48 ≤ c && c ≤ 57)

set_option hygiene false in
/-- one step on the character `c` with lookahead `n` (`e`: `c` is the last byte; then `n` = 32) -/
macro "STEP" n:term "," e:term : term => `(
    if st == 2 then lx t o m 0 sp d d0 w ty
    else if st == 0 then
      if c == 32 || c == 10 then lx t o m 0 sp d d0 w ty
      else if c == 13 then (if $n == 10 then lx t o m 0 1 d d0 w ty else [0])
      else if c == 58 then
        (if $n == 61 then (if m == 0 then lx t o m 2 1 d d0 w ty else 61 :: lx t o m 2 1 d d0 w ty)
         else (if m == 0 then lx t o m 0 sp d d0 w ty else 58 :: lx t o m 0 sp d d0 w ty))
      else if c == 40 || c == 42 || c == 43 || c == 59 || (c == 41 && !($n == 40 || isW $n)) ||
          (c == 45 && !($n == 45)) then
        (if m == 0 then lx t o m 0 sp d d0 w ty else c :: lx t o m 0 sp d d0 w ty)
      else if 48 ≤ c && c ≤ 57 then
        (if 48 ≤ $n && $n ≤ 57 then (if m == 0 then lx t o m 3 sp d d0 0 ty else 5 :: c :: lx t o m 3 sp d d0 0 ty)
         else if isL $n || $n == 40 || ($e && sp == 0) then [0]
         else (if m == 0 then lx t o m 0 sp d d0 w ty else 5 :: c :: 6 :: lx t o m 0 sp d d0 w ty))
      else if isL c then
        (if isW $n then
           (if m == 0 then lx t o m 1 sp (DSTEP0 $n) (if 97 ≤ c && c ≤ 122 then 1 else 6)
              ((0x10000 : UInt64) ||| (c.toUInt64 <<< 8) ||| ($n).toUInt64) ty
            else c :: lx t o m 1 sp (DSTEP0 $n) (if 97 ≤ c && c ≤ 122 then 1 else 6)
              ((0x10000 : UInt64) ||| (c.toUInt64 <<< 8) ||| ($n).toUInt64) ty)
         else if $n == 40 || ($e && sp == 0) || !(97 ≤ c && c ≤ 122) then [0]
         else (if m == 0 then lx t o m 0 sp d d0 w ty else c :: 0 :: lx t o m 0 sp d d0 w ty))
      else [0]
    else if st == 1 then
      if isW $n then
        (if m == 0 then lx t o m 1 sp (DSTEP d, $n) d (WSTEP w, $n) ty
         else c :: lx t o m 1 sp (DSTEP d, $n) d (WSTEP w, $n) ty)
      else if $e && sp == 0 then
        -- `lex`'s fuel equals the rest: the word is split before its last character
        (if w < 0x1000000 || (KIND d0, (w >>> 8)) == 9 || (TYU (w >>> 8)) == 9 then [0]
         else if 48 ≤ c && c ≤ 57 then
           (if m == 0 then lx t o m 0 1 d d0 w (TYU (w >>> 8))
            else (KIND d0, (w >>> 8)).toUInt8 :: 5 :: c :: 6 :: lx t o m 0 1 d d0 w (TYU (w >>> 8)))
         else if !(97 ≤ c && c ≤ 122) then [0]
         else (if m == 0 then lx t o m 0 1 d d0 w (TYU (w >>> 8))
            else (KIND d0, (w >>> 8)).toUInt8 :: c :: 0 :: lx t o m 0 1 d d0 w (TYU (w >>> 8))))
      else if $n == 40 || (KIND d, w) == 9 || (TYU w) == 9 then [0]
      else (if m == 0 then lx t o m 0 1 d d0 w (TYU w) else c :: (KIND d, w).toUInt8 :: lx t o m 0 1 d d0 w (TYU w))
    else if st == 3 then
      if 48 ≤ $n && $n ≤ 57 then (if m == 0 then lx t o m 3 sp d d0 1 ty else c :: lx t o m 3 sp d d0 1 ty)
      else if isL $n || $n == 40 then [0]
      else if $e && sp == 0 then
        (if w == 0 then [0] else (if m == 0 then lx t o m 0 1 d d0 w ty else 6 :: 5 :: c :: 6 :: lx t o m 0 1 d d0 w ty))
      else (if m == 0 then lx t o m 0 1 d d0 w ty else c :: 6 :: lx t o m 0 1 d d0 w ty)
    else [0])

/-- the machine; see the file header -/
def lx (xs o : List UInt8) (m st sp d d0 w ty : UInt64) : List UInt8 :=
  match xs with
  | c :: t =>
    if t.isEmpty then STEP (32 : UInt8), true else STEP (t.headD 0), false
  | [] =>
    if m == 0 then (if ty == 0 then [0] else ty.toUInt8 :: lx o o 1 0 0 0 0 0 ty) else []
termination_by (if m = 0 then o.length + 1 else 0) + xs.length
decreasing_by
  all_goals simp only [List.length_cons, List.length_nil]
  all_goals (try subst_vars) <;> (try simp only [List.length_cons, List.length_nil]) <;> (repeat' split) <;>
    first | omega | exact absurd ‹(1 : UInt64) = 0› (by decide) | simp_all

/-- stage 1 on the source bytes -/
def lexB (xs : List UInt8) : List UInt8 := lx xs xs 0 0 0 0 0 0 0

end Nano.B
