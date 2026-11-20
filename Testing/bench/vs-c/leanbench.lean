/- Native Lean (x86-64) reference: natural Lean implementations of the benchmarked functions.
   usage: lb FUNC N   (FUNC=none builds the input only; subtract it). -/
def gen (n : Nat) : Array UInt8 := Id.run do
  let mut s : UInt64 := 88172645463325252
  let mut a := Array.mkEmpty n
  for _ in [0:n] do
    s := s ^^^ (s <<< 13); s := s ^^^ (s >>> 7); s := s ^^^ (s <<< 17)
    a := a.push (s >>> 24).toUInt8
  return a
def cks (a : Array UInt8) : Nat := a.foldl (fun h x => (h * 31 + x.toNat) % 1000000007) 0
def gcdSub (a b : Nat) : Nat := if a = 0 then b else if b = 0 then a else if a < b then gcdSub a (b - a) else gcdSub (a - b) b
decreasing_by all_goals omega
def sumDown : Nat → Nat → Nat | 0, acc => acc | n+1, acc => sumDown n (acc + n + 1)
def main (args : List String) : IO Unit := do
  let n := args[1]!.toNat!
  let xs := gen n
  let r : Nat := match args[0]! with
    | "none" => cks xs
    | "msort" => cks (xs.toList.mergeSort (· ≤ ·)).toArray
    | "insertion" => cks (xs.insertionSort (· < ·))
    | "sum" => xs.foldl (fun s x => s + x.toNat) 0
    | "take" => cks (xs.extract 0 n)
    | "inc" => cks (xs.map (· + 1))
    | "gcd" => gcdSub 100000 3 + n * 0
    | "loopsum" => sumDown n 0
    | _ => 0
  IO.println r
