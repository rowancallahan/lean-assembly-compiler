import Compiler.Front.PipeFront
/- Three-way test, list class (verdict B): ORIGINAL book definitions (fp-lean, Examples/Intro.lean and
   Examples/ProgramsProofs/*; `partial` where the book needs a termination proof) run by Lean on the same
   inputs as the `compile%` machine code.  Format read by book_pipe_test.py. -/
open Proven
namespace Book
def take (n : Nat) (xs : List α) : List α :=
  match n, xs with | 0, _ => [] | _, [] => [] | n + 1, x :: xs => x :: take n xs
def drop : Nat → List α → List α | 0, xs => xs | _, [] => [] | n + 1, _ :: xs => drop n xs
namespace NonTail
def reverse : List α → List α | [] => [] | x :: xs => reverse xs ++ [x]
def sum : List Nat → Nat | [] => 0 | x :: xs => x + sum xs
end NonTail
namespace Tail
def sumHelper (soFar : Nat) : List Nat → Nat | [] => soFar | x :: xs => sumHelper (x + soFar) xs
def sum (xs : List Nat) : Nat := sumHelper 0 xs
def reverseHelper (soFar : List α) : List α → List α | [] => soFar | x :: xs => reverseHelper (x :: soFar) xs
def reverse (xs : List α) : List α := reverseHelper [] xs
end Tail
partial def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x'::xs') ys'
def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs => let (a, b) := splitList xs; (x :: b, a)
partial def mergeSort [Ord α] (xs : List α) : List α :=
  if xs.length < 2 then xs else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt => insertSorted (arr.swap i' i) ⟨i', by grind⟩
partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1) else arr
def insertionSort [Ord α] (arr : Array α) : Array α := insertionSortLoop arr 0
namespace NonTail
def length : List α → Nat | [] => 0 | _ :: xs => length xs + 1
def filter (p : α → Bool) : List α → List α | [] => [] | x :: xs => if p x then x :: filter p xs else filter p xs
end NonTail
namespace Tail
def lengthHelper (soFar : Nat) : List α → Nat | [] => soFar | _ :: xs => lengthHelper (soFar + 1) xs
def length (xs : List α) : Nat := lengthHelper 0 xs
def filterHelper (accum : List α) (p : α → Bool) : List α → List α
  | [] => accum.reverse
  | x :: xs => if p x then filterHelper (x :: accum) p xs else filterHelper accum p xs
def filter (p : α → Bool) (xs : List α) : List α := filterHelper [] p xs
end Tail
def head? {α : Type} (xs : List α) : Option α := match xs with | [] => none | y :: _ => some y
def final? {α : Type} (xs : List α) : Option α := match xs with | [] => none | [y] => some y | _ :: y :: ys => final? (y :: ys)
def findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with | [] => none | y :: ys => if predicate y then some y else findFirst? ys predicate
end Book
-- machine side
def c_sum := compile% fun xs : List UInt8 => xs.foldl (fun (a : BitVec 64) x => a + x.toBitVec.setWidth 64) 0
def c_rev := compile% fun xs : List UInt8 => xs.reverse
def c_take5 := compile% fun xs : List UInt8 => xs.take 5
def c_drop5 := compile% fun xs : List UInt8 => xs.drop 5
def c_sort := compile% fun xs : List UInt8 => xs.mergeSort
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def le8 (n : Nat) : List UInt8 := (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def inputs : List (List UInt8) :=
  [[], [0], [255], [3, 3], [9, 200], [255, 255, 255, 255, 255, 255, 255], List.replicate 64 255, List.replicate 64 0,
   (List.range 64).map (UInt8.ofNat ·), ((List.range 64).map (UInt8.ofNat ·)).reverse] ++
  (List.range 300).map fun i =>
    let L := if i % 7 = 0 then 64 else rnd i 99 % 65
    (List.range L).map fun j => UInt8.ofNat (match i % 4 with | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | _ => 255 - rnd i j % 3)
def optb : Option UInt8 → List UInt8 | none => [0] | some v => [1, v]
def emit {α : Type} {enc : α → List UInt8} {f : List UInt8 → α} (n : String) (c : Compiled enc f) (orig : List UInt8 → List UInt8) : IO Unit := do
  let d := "Testing/notes/book_tries/pipe-words"
  IO.FS.createDirAll d
  IO.FS.writeFile s!"{d}/{n}.words" (String.intercalate "\n" (c.code.map hex8) ++ "\n")
  IO.FS.writeFile s!"{d}/{n}.space" (String.intercalate " " ((List.range 65).map fun k => toString (XPipe.space c.pipe k)) ++ "\n")
  IO.FS.writeFile s!"{d}/{n}.sspace" (String.intercalate " " ((List.range 65).map fun k => toString (XPipe.sspace c.pipe k)) ++ "\n")
  IO.FS.writeFile s!"{d}/{n}.exp" (String.join (inputs.map fun xs => s!"{hx xs} {hx (orig xs)}\n"))
def c_len := compile% fun xs : List UInt8 => BitVec.ofNat 64 xs.length
def c_filt := compile% fun xs : List UInt8 => xs.filter (· > 3)
def c_head := compile% fun xs : List UInt8 => xs.head?
def c_last := compile% fun xs : List UInt8 => xs.getLast?
def c_find := compile% fun xs : List UInt8 => xs.find? (· > 3)
#eval show IO Unit from do
  emit "sum64_Tail.sum" c_sum fun xs => le8 (Book.Tail.sum (xs.map (·.toNat)))
  emit "sum64_NonTail.sum" c_sum fun xs => le8 (Book.NonTail.sum (xs.map (·.toNat)))
  emit "reverse_NonTail.reverse" c_rev fun xs => Book.NonTail.reverse xs
  emit "reverse_Tail.reverse" c_rev fun xs => Book.Tail.reverse xs
  emit "take5_Book.take" c_take5 fun xs => Book.take 5 xs
  emit "drop5_Book.drop" c_drop5 fun xs => Book.drop 5 xs
  emit "sort_Book.mergeSort" c_sort fun xs => Book.mergeSort xs
  emit "sort_Book.insertionSort" c_sort fun xs => (Book.insertionSort xs.toArray).toList
  emit "len_Tail.length" c_len fun xs => le8 (Book.Tail.length xs)
  emit "len_NonTail.length" c_len fun xs => le8 (Book.NonTail.length xs)
  emit "filter_Tail.filter" c_filt fun xs => Book.Tail.filter (· > 3) xs
  emit "filter_NonTail.filter" c_filt fun xs => Book.NonTail.filter (· > 3) xs
  emit "head_Book.head?" c_head fun xs => optb (Book.head? xs)
  emit "last_Book.final?" c_last fun xs => optb (Book.final? xs)
  emit "find_Book.findFirst?" c_find fun xs => optb (Book.findFirst? xs (· > 3))
