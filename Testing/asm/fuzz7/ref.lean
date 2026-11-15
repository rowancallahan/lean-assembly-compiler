/- FUZZ7 reference: the entries' source functions verbatim (lean-zip @7e10583 Zip/Native/Inflate.lean:536,555,587;
core Nat.gcd; the ops expressions of Riscv/Frontx/WaMul.lean and MulExamples.lean), executed by Lean.
stdin: lines `FN HEX` (HEX = input bytes, `-` = empty); stdout: result bytes as hex (Res.enc: UInt64/Nat 8 bytes LE
(Nat mod 2^64), UInt32 4 bytes, Array UInt32 4 bytes per element). -/
set_option linter.unusedVariables false
def countLengthsFast (lengths : Array UInt8) (maxBits : Nat) : Array Nat :=
  go lengths maxBits 0 (Array.replicate (maxBits + 1) 0)
where
  go (lengths : Array UInt8) (maxBits i : Nat) (count : Array Nat) : Array Nat :=
    if h : i < lengths.size then
      let ln := lengths[i].toNat
      let count := if 0 < ln ∧ ln ≤ maxBits then count.set! ln (count[ln]! + 1) else count
      go lengths maxBits (i + 1) count
    else count
  termination_by lengths.size - i
def kraftSumFast (count : Array Nat) (maxBits : Nat) : Nat :=
  go count maxBits 0 0
where
  go (count : Array Nat) (maxBits b acc : Nat) : Nat :=
    if h : b ≤ maxBits then
      go count maxBits (b + 1) (acc + count[b]! * (1 <<< (maxBits - b)))
    else acc
  termination_by maxBits + 1 - b
def nextCodesFast (count : Array Nat) (maxBits : Nat) : Array UInt32 :=
  go count maxBits 1 0 (Array.replicate (maxBits + 1) 0)
where
  go (count : Array Nat) (maxBits bits code : Nat) (nc : Array UInt32) : Array UInt32 :=
    if h : bits ≤ maxBits then
      let code := (code + count[bits - 1]!) * 2
      go count maxBits (bits + 1) code (nc.set! bits code.toUInt32)
    else nc
  termination_by maxBits + 1 - bits
def rd32 (xs : ByteArray) (o : Nat) : Nat :=
  xs[o]!.toNat + 256 * xs[o + 1]!.toNat + 65536 * xs[o + 2]!.toNat + 16777216 * xs[o + 3]!.toNat
def rd64 (xs : ByteArray) (o : Nat) : UInt64 :=
  xs[o]!.toUInt64 ||| xs[o + 1]!.toUInt64 <<< 8 ||| xs[o + 2]!.toUInt64 <<< 16 ||| xs[o + 3]!.toUInt64 <<< 24 |||
    xs[o + 4]!.toUInt64 <<< 32 ||| xs[o + 5]!.toUInt64 <<< 40 ||| xs[o + 6]!.toUInt64 <<< 48 |||
    xs[o + 7]!.toUInt64 <<< 56
def rd32u (xs : ByteArray) (o : Nat) : UInt32 :=
  xs[o]!.toUInt32 ||| xs[o + 1]!.toUInt32 <<< 8 ||| xs[o + 2]!.toUInt32 <<< 16 ||| xs[o + 3]!.toUInt32 <<< 24
def ops64 (a b : UInt64) : UInt64 := (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< b) ^^^ (a >>> b)
def ops32 (a b : UInt32) : UInt32 := (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< b) ^^^ (a >>> b)
def opsN (a b : Nat) : Nat := (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< (b % 64)) ^^^ (a >>> b)
def le (n w : Nat) : List UInt8 := (List.range w).map fun j => UInt8.ofNat (n / 256 ^ j % 256)
def hx (xs : List UInt8) : String := String.join (xs.map fun b =>
  let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s)
def dig (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
def unhex (s : String) : ByteArray :=
  if s == "-" then ByteArray.empty else
  let cs := s.toList.toArray
  ⟨(Array.range (cs.size / 2)).map fun i => UInt8.ofNat (dig cs[2*i]! * 16 + dig cs[2*i+1]!)⟩
def run (fn : String) (xs : ByteArray) : List UInt8 :=
  match fn with
  | "wa_kraft" => le (kraftSumFast (countLengthsFast xs.data 15) 15) 8
  | "wa_nextcodes" => ((nextCodesFast (countLengthsFast xs.data 15) 15).toList.flatMap fun c => le c.toNat 4)
  | "wa_gcd" => le (Nat.gcd (rd32 xs 0) (rd32 xs 4)) 8
  | "fx_gcd" => le (Nat.gcd (rd64 xs 0).toNat (rd64 xs 8).toNat) 8
  | "wa_ops64" => le (ops64 (rd64 xs 0) (rd64 xs 8)).toNat 8
  | "fx_ops64" => le (ops64 (rd64 xs 0) (rd64 xs 8)).toNat 8
  | "wa_ops32" => le (ops32 (rd32u xs 0) (rd32u xs 4)).toNat 4
  | "fx_ops32" => le (ops32 (rd64 xs 0).toUInt32 (rd64 xs 8).toUInt32).toNat 4
  | "wa_opsn" => le (opsN (rd32 xs 0) (rd32 xs 4)) 8
  | "fx_opsn" => le (opsN (rd64 xs 0).toNat (rd64 xs 8).toNat) 8
  | _ => panic! s!"unknown {fn}"
partial def loop (h : IO.FS.Stream) : IO Unit := do
  let l ← h.getLine
  if l.isEmpty then return
  match l.trimAscii.toString.splitOn " " with
  | [fn, x] => IO.println (hx (run fn (unhex x)))
  | _ => pure ()
  loop h
def main : IO Unit := do loop (← IO.getStdin)
