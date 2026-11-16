/- Hand-written RTL programs and interpreter tests (`#guard`, run at elaboration):
* `reverse`: builds a linked list of 2-cell blocks from the input bytes, reverses it in place by pointer
  chasing, and writes it to the output (output = input reversed);
* `mix`: a hash over the input with an unrolled body of about 300 operations (code longer than 1024 words: the
  loop test's exit branch is out of short-branch range), one allocated cell per byte, 8 output bytes. -/
import Compiler.Ir.Sem

namespace Proven.Ir.Examples
open Proven.Ir Proven.Mach Proven.Top.Alloc

def blk (ps : List VReg) (body : List (Inst VReg)) (t : Term VReg) : Block VReg := ⟨ps, body, t⟩
def isZero (x : VReg) : Tst VReg := ⟨.eq, .r x, .i 0⟩

/-- `reverse`: vregs `0` input, `1` length, `2` output -/
def reverseF : Func VReg where
  params := [0, 1, 2]
  entry := 0
  blocks := [
    (0, blk [] [] (.jmp 1 [.r 1, .i 0])),
    -- build: i, acc
    (1, blk [3, 4] [] (.br (isZero 3) 3 [] 2 [])),
    (2, blk [] [.let_ 5 (.op .sub (.r 3) (.i 1)), .ldb 6 0 (.r 5), .alloc 7 (.i 2), .st (.r 6) 7 0, .st (.r 4) 7 1]
      (.jmp 1 [.r 5, .r 7])),
    (3, blk [] [] (.jmp 4 [.r 4, .i 0])),
    -- reverse in place: cur, prev
    (4, blk [8, 9] [] (.br (isZero 8) 6 [] 5 [])),
    (5, blk [] [.ld 10 8 1, .st (.r 9) 8 1] (.jmp 4 [.r 10, .r 8])),
    (6, blk [] [] (.jmp 7 [.r 9, .i 0])),
    -- write: p, j
    (7, blk [11, 12] [] (.br (isZero 11) 9 [] 8 [])),
    (8, blk [] [.ld 13 11 0, .stb (.r 13) 2 (.r 12), .ld 14 11 1, .let_ 15 (.op .add (.r 12) (.i 1))]
      (.jmp 7 [.r 14, .r 15])),
    (9, blk [] [] (.ret []))]

def reverse : Prog VReg := ⟨[reverseF], 0⟩

/-- the unrolled mixing body on vreg `5` (scratch `6`) -/
def mixBody : Nat → List (Inst VReg)
  | 0 => []
  | k + 1 => [.let_ 6 (.op .lshr (.r 5) (.i (BitVec.ofNat 64 (k % 13 + 3)))),
      .let_ 5 (.op .xor (.r 5) (.r 6)),
      .let_ 5 (.mop .mul (.r 5) (.i (BitVec.ofNat 64 (0x100000001b3 + 2 * k)))),
      .let_ 5 (.op .add (.r 5) (.i (BitVec.ofNat 64 (k * 977 % 2048))))] ++ mixBody k

/-- `mix`: vregs `0` input, `1` length, `2` output; loop `3` index, `4` hash -/
def mixF : Func VReg where
  params := [0, 1, 2]
  entry := 0
  blocks := [
    (0, blk [] [] (.jmp 1 [.i 0, .i 0xcbf29ce484222325])),
    (1, blk [3, 4] [] (.br ⟨.eq, .r 3, .r 1⟩ 3 [] 2 [])),
    (2, blk [] ([.ldb 7 0 (.r 3), .let_ 5 (.op .xor (.r 4) (.r 7))] ++ mixBody 75 ++
        [.alloc 8 (.i 1), .st (.r 5) 8 0, .ld 9 8 0, .let_ 3 (.op .add (.r 3) (.i 1))])
      (.jmp 1 [.r 3, .r 9])),
    (3, blk [] [.stb (.r 4) 2 (.i 0), .let_ 6 (.op .lshr (.r 4) (.i 8)), .stb (.r 6) 2 (.i 1),
        .let_ 6 (.op .lshr (.r 4) (.i 16)), .stb (.r 6) 2 (.i 2), .let_ 6 (.op .lshr (.r 4) (.i 24)),
        .stb (.r 6) 2 (.i 3), .let_ 6 (.op .lshr (.r 4) (.i 32)), .stb (.r 6) 2 (.i 4),
        .let_ 6 (.op .lshr (.r 4) (.i 40)), .stb (.r 6) 2 (.i 5), .let_ 6 (.op .lshr (.r 4) (.i 48)),
        .stb (.r 6) 2 (.i 6), .let_ 6 (.op .lshr (.r 4) (.i 56)), .stb (.r 6) 2 (.i 7)] (.ret []))]

def mix : Prog VReg := ⟨[mixF], 0⟩

/-! ## Tests -/

#guard (interp reverse 1000 []).map (·.1) = some []
#guard (interp reverse 1000 [1, 2, 3]).map (·.1) = some [3, 2, 1]
#guard (interp reverse 100000 ((List.range 200).map UInt8.ofNat)).map (·.1) =
  some ((List.range 200).reverse.map UInt8.ofNat)
#guard (interp reverse 1000 [5, 6]).map (fun r => peak r.2) = some 4
#guard (interp mix 100000 [1, 2, 3]).map (·.1.length) = some 8
#guard (interp mix 100000 [1, 2, 3]).map (fun r => peak r.2) = some 3

/-- the reference for `mix` -/
def mixRef (xs : List UInt8) : BitVec 64 :=
  xs.foldl (fun h b => (List.range 75).reverse.foldl (fun h k =>
      let h := h ^^^ (h >>> (k % 13 + 3))
      let h := h * BitVec.ofNat 64 (0x100000001b3 + 2 * k)
      h + BitVec.ofNat 64 (k * 977 % 2048)) (h ^^^ b.toBitVec.setWidth 64)) 0xcbf29ce484222325

#guard (interp mix 100000 [7, 200, 13, 0]).map (·.1) =
  some ((List.range 8).map fun i => UInt8.ofBitVec ((mixRef [7, 200, 13, 0] >>> (8 * i)).setWidth 8))

end Proven.Ir.Examples
