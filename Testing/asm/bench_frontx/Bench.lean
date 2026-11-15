-- Lean versions of the Frontx entry points (definitions copied from Riscv/Frontx/*.lean, no proofs needed here),
-- compiled with `lean -c`.  main FN N REPS KIND: builds N bytes, calls FN REPS times, prints a checksum.
namespace B
def crcBit (c : UInt32) : UInt32 := if c &&& 1 = 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1
def crcByte (c : UInt32) (b : UInt8) : UInt32 :=
  crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (c ^^^ b.toUInt32))))))))
def crcGo (xs : ByteArray) (i : Nat) (c : UInt32) : UInt32 :=
  if h : i < xs.size then crcGo xs (i + 1) (crcByte c xs[i]) else c
termination_by xs.size - i
def crcRaw (xs : ByteArray) : UInt32 := crcGo xs 0 0xFFFFFFFF

@[inline] def at' (bs : ByteArray) (i : Nat) : UInt8 := if h : i < bs.size then bs[i] else 0
@[inline] def b64Digit (c : UInt8) : UInt32 :=
  if 65 ≤ c && c ≤ 90 then c.toUInt32 - 65
  else if 97 ≤ c && c ≤ 122 then c.toUInt32 - 71
  else if 48 ≤ c && c ≤ 57 then c.toUInt32 + 4
  else if c == 43 then 62
  else if c == 47 then 63
  else 64
def b64Sum (bs : ByteArray) (i fuel : Nat) (n : UInt32) : UInt32 :=
  match fuel with
  | 0 => n
  | f + 1 => b64Sum bs (i + 1) f (n + b64Digit (at' bs i))
def b64All (xs : ByteArray) : UInt32 := b64Sum xs 0 xs.size 0

def findByte (bs : ByteArray) (i : Nat) (c : UInt8) : Nat := Id.run do
  let mut j := i
  for _ in [i:bs.size] do
    if at' bs j == c then return j
    j := j + 1
  return bs.size
def findNL (xs : ByteArray) : Nat := findByte xs 0 10

def be32 (b : ByteArray) (i : Nat) : Nat :=
  ((at' b i).toNat <<< 24) ||| ((at' b (i + 1)).toNat <<< 16) ||| ((at' b (i + 2)).toNat <<< 8) ||| (at' b (i + 3)).toNat
def be32At0 (xs : ByteArray) : Nat := be32 xs 0

namespace NonTail
def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
def filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: filter p xs else filter p xs
end NonTail
namespace Tail
def sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs
def sum (xs : List Nat) : Nat := sumHelper 0 xs
def lengthHelper (soFar : Nat) : List α → Nat
  | [] => soFar
  | _ :: xs => lengthHelper (soFar + 1) xs
def length (xs : List α) : Nat := lengthHelper 0 xs
end Tail
def mlength : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (mlength ys)
def take (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | _, [] => []
  | Nat.zero, _ => []
  | Nat.succ n', x :: xs => x :: take n' xs
def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, x :: xs => drop n xs
def head? {α : Type} (xs : List α) : Option α := match xs with | [] => none | y :: _ => some y
def final? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [y] => some y
  | _ :: y2 :: ys => final? (y2 :: ys)
def findFirst? {α : Type} (xs : List α) (p : α → Bool) : Option α :=
  match xs with
  | [] => none
  | y :: ys => if p y then some y else findFirst? ys p

def tailSum (xs : ByteArray) : Nat := Tail.sum (xs.data.toList.map UInt8.toNat)
def nonTailSum (xs : ByteArray) : Nat := NonTail.sum (xs.data.toList.map UInt8.toNat)
def tailLength (xs : ByteArray) : Nat := Tail.length xs.data.toList
def bookLength (xs : ByteArray) : Nat := mlength xs.data.toList
def take5 (xs : ByteArray) : List UInt8 := take 5 xs.data.toList
def drop5 (xs : ByteArray) : List UInt8 := drop 5 xs.data.toList
def filterAll (xs : ByteArray) : List UInt8 := NonTail.filter (· > 3) xs.data.toList
def incEach (xs : ByteArray) : List UInt8 := List.map (· + 1) xs.data.toList
def twice (xs : ByteArray) : List UInt8 := xs.data.toList ++ xs.data.toList
def headOf (xs : ByteArray) : Option UInt8 := head? xs.data.toList
def finalOf (xs : ByteArray) : Option UInt8 := final? xs.data.toList
def findFirstGt3 (xs : ByteArray) : Option UInt8 := findFirst? xs.data.toList (· > 3)

def optN : Option UInt8 → Nat | none => 0 | some b => b.toNat + 1
def run : String → ByteArray → Nat
  | "crcraw", xs => (crcRaw xs).toNat
  | "b64all", xs => (b64All xs).toNat
  | "findnl", xs => findNL xs
  | "be32at0", xs => be32At0 xs
  | "tailsum", xs => tailSum xs
  | "nontailsum", xs => nonTailSum xs
  | "taillength", xs => tailLength xs
  | "booklength", xs => bookLength xs
  | "take5", xs => (take5 xs).length
  | "drop5", xs => (drop5 xs).length
  | "filterall", xs => (filterAll xs).length
  | "inceach", xs => (incEach xs).length
  | "twice", xs => (twice xs).length
  | "headof", xs => optN (headOf xs)
  | "finalof", xs => optN (finalOf xs)
  | "findfirstgt3", xs => optN (findFirstGt3 xs)
  | _, _ => panic! "fn"
end B

def mkInput (n : Nat) (kind : String) : ByteArray := Id.run do
  let mut xs := ByteArray.empty
  let mut s : UInt64 := 88172645463325252
  for _ in [0:n] do
    s := s ^^^ (s <<< 13); s := s ^^^ (s >>> 7); s := s ^^^ (s <<< 17)
    xs := xs.push (if kind == "scan" then (s >>> 33).toUInt8 &&& 3 else (s >>> 33).toUInt8)
  return xs

def main (args : List String) : IO Unit := do
  let [fn, n, reps, kind] := args | throw (IO.userError "args")
  let xs := mkInput n.toNat! kind
  let mut acc := 0
  for _ in [0:reps.toNat!] do
    acc := acc + B.run fn xs
  IO.println acc
