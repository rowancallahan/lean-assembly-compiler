/- The inductive path (`Compiler/Ind.lean`, NOTES §17/§21/§25/§28) lowered to RTL (`Testing/notes/IR_DESIGN.md` §3):
* a value is a pointer to a block of 4 cells `[tag, x, l, r]` (`alloc 4` and four `st`), `z` is the word `0`;
* a field read of a value is a test for `z` and one `ld`;
* the dispatch on the tag of the current node is a `switch`; an arm that is a recursive call is a jump back to the
  entry with new parameters (a loop), every other call a `call`;
* `dec` / `enc` are RTL functions (the byte format `C.enc`: tag, fields; strings as length + UTF-8 bytes, in
  memory a chain of cells, NOTES §28).
Functions: `0` main `(input, length, output)`, `1` dec `(input, cursor) → (value, cursor)`, `2` enc `(output, value,
cursor) → cursor`, `3 + i` the program's functions `(node, word, tree) → result`.

Pure Lean (core only). -/
import Compiler.Ir.Struct
import Compiler.Ind

namespace Proven.Ir.IndLow
open Proven.Ir Proven.Mach Proven.Mach.Ind
set_option autoImplicit false

def mov (d s : VReg) : SC := .i (.let_ d (.arg (.r s)))
def setK (d : VReg) (c : BitVec 64) : SC := .i (.let_ d (.arg (.i c)))
def bin (o : Op) (d a b : VReg) : SC := .i (.let_ d (.op o (.r a) (.r b)))
def addK (d a : VReg) (c : BitVec 64) : SC := .i (.let_ d (.op .add (.r a) (.i c)))
def nz (x : VReg) : Tst VReg := ⟨.ne, .r x, .i 0⟩

/-- a new cell `[t, x, l, r]` into `d` -/
def mkCell (d : VReg) (t x l r : Arg VReg) : SC :=
  .seqs [.i (.alloc d (.i 4)), .i (.st t d 0), .i (.st x d 1), .i (.st l d 2), .i (.st r d 3)]

/-- field `k` of the value in `v` into `d` (`z` reads as `zk`) -/
def fld (d v : VReg) (k : Nat) (zk : BitVec 64) : SC := .ite (nz v) (.i (.ld d v k)) (setK d zk)

/-! ## the program's functions -/

section
variable {rk : Kd}

/-- `e` into `d`, temporaries from `n`; registers: `0` node, `1` word, `2` tree, `3` tag, `4` x, `5` l, `6` r; the
`bind` values in `ρ` (innermost first); `fi` this function -/
def lowE (fi : FId) (ρ : List VReg) : {k : Kd} → E rk k → VReg → VReg → SC
  | _, .x, d, _ => mov d 4
  | _, .a, d, _ => mov d 1
  | _, .k c, d, _ => setK d c
  | _, .bin op e₁ e₂, d, n => .seqs [lowE fi ρ e₁ n (n + 1), lowE fi ρ e₂ (n + 1) (n + 2), bin op d n (n + 1)]
  | _, .l, d, _ => mov d 5
  | _, .r, d, _ => mov d 6
  | _, .b, d, _ => mov d 2
  | _, .nul, d, _ => setK d 0
  | _, .mk t ex el er, d, n => .seqs [lowE fi ρ ex n (n + 1), lowE fi ρ el (n + 1) (n + 2),
      lowE fi ρ er (n + 2) (n + 3), mkCell d (.i (BitVec.ofNat 64 t)) (.r n) (.r (n + 1)) (.r (n + 2))]
  | _, .call ch ea eb, d, n => .seqs [lowE fi ρ ea n (n + 1), lowE fi ρ eb (n + 1) (n + 2),
      .i (.call [d] fi [.r (if ch then 6 else 5), .r n, .r (n + 1)])]
  | _, .ite c e₁ e₂, d, n => .seq (lowE fi ρ c n (n + 1)) (.ite (nz n) (lowE fi ρ e₁ d (n + 1)) (lowE fi ρ e₂ d (n + 1)))
  | _, .me, d, _ => mov d 0
  | _, .fw i e, d, n => .seq (lowE fi ρ e n (n + 1)) (fld d n (if i then 1 else 0) (if i then 0 else 255))
  | _, .ft ch e, d, n => .seq (lowE fi ρ e n (n + 1)) (fld d n (if ch then 3 else 2) 0)
  | _, .ext j _ et ea eb, d, n => .seqs [lowE fi ρ et n (n + 1), lowE fi ρ ea (n + 1) (n + 2),
      lowE fi ρ eb (n + 2) (n + 3), .i (.call [d] (fi + 1 + j) [.r n, .r (n + 1), .r (n + 2)])]
  | _, .bind e₁ e₂, d, n => .seq (lowE fi ρ e₁ n (n + 1)) (lowE fi (n :: ρ) e₂ d (n + 1))
  | _, .var i _, d, _ => mov d (ρ.getD i 0)
  | _, .call2 c₁ c₂ ea eb, d, n => .seqs [lowE fi ρ ea n (n + 1), lowE fi ρ eb (n + 1) (n + 2),
      fld (n + 2) (if c₁ then 6 else 5) (if c₂ then 3 else 2) 0, .i (.call [d] fi [.r (n + 2), .r n, .r (n + 1)])]

/-- an arm (tail position): a recursive call on a child is a jump to the entry (label `0`), an `if` / `let`
continues in tail position, anything else is the result -/
def lowT (fi : FId) (ρ : List VReg) : {k : Kd} → E rk k → VReg → TC
  | _, .call ch ea eb, n => .seq (.seq (lowE fi ρ ea n (n + 1)) (lowE fi ρ eb (n + 1) (n + 2)))
      (.term (.jmp 0 [.r (if ch then 6 else 5), .r n, .r (n + 1)]))
  | _, .ite c e₁ e₂, n => .seq (lowE fi ρ c n (n + 1)) (.ite (nz n) (lowT fi ρ e₁ (n + 1)) (lowT fi ρ e₂ (n + 1)))
  | _, .bind e₁ e₂, n => .seq (lowE fi ρ e₁ n (n + 1)) (lowT fi (n :: ρ) e₂ (n + 1))
  | _, e, n => .seq (lowE fi ρ e n (n + 1)) (.term (.ret [.r n]))

/-- the entry: `z` gives the default `0`; else the cell's four words, then the arm of its tag (labels `1 ..`),
tags without an arm to the default (label `arms + 1`) -/
def entryTC (na : Nat) : TC :=
  .ite (nz 0)
    (.seq (.seqs [.i (.ld 3 0 0), .i (.ld 4 0 1), .i (.ld 5 0 2), .i (.ld 6 0 3)])
      (.term (.switch 3 ((List.range na).map (· + 1)) (na + 1))))
    (.term (.ret [.i 0]))

/-- **the function at index `fi`**: parameters node, word, tree -/
def lowPg (fi : FId) (pg : Pg rk) : Func VReg :=
  mkFunc [0, 1, 2] [0, 1, 2] (pg.arms.length + 2)
    ((0, entryTC pg.arms.length) :: (pg.arms.mapIdx fun j e => (j + 1, lowT fi [] e 7)) ++
      [(pg.arms.length + 1, .term (.ret [.i 0]))])

end

/-! ## dec, enc -/

/-- the 8 bytes at `cur` (little-endian) into `d`; temporaries `t1`, `t2`; `inp` the input -/
def rd8 (inp cur d t1 t2 : VReg) : SC :=
  .seq (setK d 0) (.seqs ((List.range 8).reverse.map fun j =>
    .seqs [addK t1 cur (BitVec.ofNat 64 j), .i (.ldb t2 inp (.r t1)), .i (.let_ d (.op .shl (.r d) (.i 8))),
      bin .add d d t2]))

/-- dec registers: `0` input, `1` cursor, `2` tag, `3` x, `4` l, `5` r, `6 .. 11` temporaries -/
def decStr (st : Nat) (d : VReg) : SC :=
  .seqs [rd8 0 1 8 6 7, addK 1 1 8,
    mkCell 10 (.i (BitVec.ofNat 64 st)) (.i 0) (.i 0) (.i 0),
    bin .add 9 1 8,
    .loop ⟨.ne, .r 9, .r 1⟩ (.seqs [.i (.let_ 9 (.op .sub (.r 9) (.i 1))), .i (.ldb 7 0 (.r 9)),
      mkCell 11 (.i (BitVec.ofNat 64 (st + 1))) (.r 7) (.r 10) (.i 0), mov 10 11]),
    bin .add 1 1 8, mov d 10]

def decFld (st : Nat) : Fld → SC
  | .x => .seq (rd8 0 1 3 6 7) (addK 1 1 8)
  | .b => .seq (.i (.ldb 3 0 (.r 1))) (addK 1 1 1)
  | .l => .i (.call [4, 1] 1 [.r 0, .r 1])
  | .r => .i (.call [5, 1] 1 [.r 0, .r 1])
  | .sl => decStr st 4
  | .sr => decStr st 5

/-- **dec**: the tag, the fields of its shape, the cell after its children -/
def decF (sh : Shape) : Func VReg :=
  mkFunc [0, 1] [0, 1] (sh.length + 2)
    ((0, .seq (.seqs [.i (.ldb 2 0 (.r 1)), addK 1 1 1, setK 3 0, setK 4 0, setK 5 0])
        (.term (.switch 2 ((List.range sh.length).map (· + 1)) (sh.length + 1)))) ::
      (sh.mapIdx fun i fs => (i + 1, .seq (SC.seqs (fs.map (decFld (sTag sh)))) (.term (.jmp (sh.length + 1) [])))) ++
      [(sh.length + 1, .seq (mkCell 6 (.r 2) (.r 3) (.r 4) (.r 5)) (.term (.ret [.r 6, .r 1])))])

/-- the low byte of `v` to the output at `o`, `o := o + 1` (enc registers: `0` output, `1` value, `2` cursor) -/
def put (v : Arg VReg) : SC := .seq (.i (.stb v 0 (.r 2))) (addK 2 2 1)

/-- the 8 bytes of `x` (little-endian) -/
def put8 (x t : VReg) : SC :=
  .seqs ((List.range 8).map fun j => .seq (.i (.let_ t (.op .lshr (.r x) (.i (BitVec.ofNat 64 (8 * j)))))) (put (.r t)))

/-- `go` := the child `l` of the cell at `q` if there is a cell (else `0`) -/
def nextL (go q : VReg) : SC := fld go q 2 0

/-- a string at `c` to the output: its length (the cells with a child), then their bytes; registers `7 .. 11` -/
def encStr (c : VReg) : SC :=
  .seqs [setK 7 0, mov 8 c, nextL 9 8,
    .loop (nz 9) (.seqs [addK 7 7 1, mov 8 9, nextL 9 8]),
    put8 7 10,
    mov 8 c, nextL 9 8,
    .loop (nz 9) (.seqs [.i (.ld 10 8 1), put (.r 10), mov 8 9, nextL 9 8])]

def encFld : Fld → SC
  | .x => put8 4 7
  | .b => put (.r 4)
  | .l => .i (.call [2] 2 [.r 0, .r 5, .r 2])
  | .r => .i (.call [2] 2 [.r 0, .r 6, .r 2])
  | .sl => encStr 5
  | .sr => encStr 6

/-- **enc**: `z` is the byte `255`; a cell its tag byte and the fields of its shape -/
def encF (sh : Shape) : Func VReg :=
  mkFunc [0, 1, 2] [0, 1, 2] (sh.length + 2)
    ((0, .ite (nz 1)
        (.seq (.seqs [.i (.ld 3 1 0), .i (.ld 4 1 1), .i (.ld 5 1 2), .i (.ld 6 1 3), put (.r 3)])
          (.term (.switch 3 ((List.range sh.length).map (· + 1)) (sh.length + 1))))
        (.seq (put (.i 255)) (.term (.ret [.r 2])))) ::
      (sh.mapIdx fun i fs => (i + 1, .seq (SC.seqs (fs.map encFld)) (.term (.jmp (sh.length + 1) [])))) ++
      [(sh.length + 1, .term (.ret [.r 2]))])

/-! ## main, the program -/

/-- main registers: `0` input, `1` length, `2` output, `3` cursor, `4` first value, `5` second, `6` word, `7` result,
`8 ..` temporaries -/
def mainF (bi : BIn) (ain : Bool) (a0 : BitVec 64) (tree : Bool) (nb : Nat) : Func VReg :=
  mkFunc [0, 1, 2] [0, 1, 2] 1 [(0, .seq (.seqs [
    setK 3 0,
    .i (.call [4, 3] 1 [.r 0, .r 3]),
    (match bi with
      | .inp => .i (.call [5, 3] 1 [.r 0, .r 3])
      | .ctor t => mkCell 5 (.i (BitVec.ofNat 64 t)) (.i 0) (.i 0) (.i 0)
      | .none => setK 5 0),
    (if ain then rd8 0 3 6 8 9 else setK 6 a0),
    .i (.call [7] 3 [.r 4, .r 6, .r 5]),
    (if tree then .i (.call [8] 2 [.r 2, .r 7, .i 0])
     else .seqs ((List.range nb).map fun j =>
       .seq (.i (.let_ 8 (.op .lshr (.r 7) (.i (BitVec.ofNat 64 (8 * j)))))) (.i (.stb (.r 8) 2 (.i (BitVec.ofNat 64 j))))))])
    (.term (.ret [])))]

/-- **the RTL program** of an inductive-path program -/
def lower {rk : Kd} (sh shO : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k)) (bi : BIn) (ain : Bool)
    (a0 : BitVec 64) (nb : Nat) : Prog VReg :=
  ⟨[mainF bi ain a0 (rk = .t) nb, decF sh, encF shO, lowPg 3 pg] ++ hs.mapIdx fun i p => lowPg (4 + i) p.2, 0⟩

end Proven.Ir.IndLow
