/- **the proved nano code generator**: `nanoGenIR : Prog → List UInt8` (RISC-V machine code, `StartCorrect` convention).
(Named `nanoGenIR`: `nanoGen`/`nanoCompile` in `Nano/Gen.lean` are nano-e2e's raw, self-hostable path.)
Route (b) of Testing/notes/NANO_PROOF.md: nano is lowered to the shared IR as structured code (`lower`, one function,
straight-line), and the IR compiler (`Riscv/Back/IrTop.lean`, proved once) makes the machine code.
Calls are inlined (the AST carries callee bodies).  Registers of `main`: `0` input, `1` length, `2` output,
`3` cursor, `5`/`6` byte temporaries, `7` result, `8` byte scratch, `10 + k` parameter `k`, `10 + arity ..` the
expression temporaries: a compound expression computed from register `nx` on leaves its value in `nx` (its
sub-expressions use `nx ..` and are dead after), so the registers used grow with the nesting depth, not the size
(the IR back end allows at most 254 frame slots). -/
import Legacy.Nano.Ast
import Legacy.Compiler.Ir.IndLowMain
import Legacy.Riscv.Back.IrTop

namespace Nano
open Proven.Ir Proven.Ir.IndLow Proven.Mach

/-- `d := a ∘ b` for a nano operator -/
def binRhs (o : Nat) (a b : Arg Nat) : Rhs Nat :=
  match o with
  | 0 => .op .add a b
  | 1 => .op .sub a b
  | _ => .mop .mul a b

mutual
/-- an expression: its code, the operand holding its value, the next free register -/
def cE : Ex → List (Arg Nat) → Nat → SC × Arg Nat × Nat
  | .num n, _, nx => (.nop, .i n.toBitVec, nx)
  | .var i, env, nx => (.nop, env.getD i (.i 0), nx)
  | .add a b, env, nx =>
    let ra := cE a env nx
    let rb := cE b env ra.2.2
    (.seq (.seq ra.1 rb.1) (.i (.let_ nx (binRhs 0 ra.2.1 rb.2.1))), .r nx, nx + 1)
  | .sub a b, env, nx =>
    let ra := cE a env nx
    let rb := cE b env ra.2.2
    (.seq (.seq ra.1 rb.1) (.i (.let_ nx (binRhs 1 ra.2.1 rb.2.1))), .r nx, nx + 1)
  | .mul a b, env, nx =>
    let ra := cE a env nx
    let rb := cE b env ra.2.2
    (.seq (.seq ra.1 rb.1) (.i (.let_ nx (binRhs 2 ra.2.1 rb.2.1))), .r nx, nx + 1)
  | .let_ v b, env, nx =>
    let rv := cE v env nx
    let rb := cE b (rv.2.1 :: env) rv.2.2
    (.seq (.seq rv.1 rb.1) (.i (.let_ nx (.arg rb.2.1))), .r nx, nx + 1)
  | .call b as, env, nx =>
    let ra := cA as env nx
    let rb := cE b ra.2.1.reverse ra.2.2
    (.seq (.seq ra.1 rb.1) (.i (.let_ nx (.arg rb.2.1))), .r nx, nx + 1)
  | .anil, _, nx => (.nop, .i 0, nx)
  | .acons _ _, _, nx => (.nop, .i 0, nx)
/-- an argument list: its code, the operands, the next free register -/
def cA : Ex → List (Arg Nat) → Nat → SC × List (Arg Nat) × Nat
  | .acons e r, env, nx =>
    let re := cE e env nx
    let rr := cA r env re.2.2
    (.seq re.1 rr.1, re.2.1 :: rr.2.1, rr.2.2)
  | _, _, nx => (.nop, [], nx)
end

/-- load the parameters `0 .. k` (word `j` at input byte `8 j`) into registers `10 + j` -/
def ldArgs : Nat → SC
  | 0 => .nop
  | k + 1 => .seq (ldArgs k) (.seq (setK 3 (BitVec.ofNat 64 (8 * k))) (rd8 0 3 (10 + k) 5 6))

/-- the environment of the body: parameter `n - 1` is variable `0` -/
def argEnv (n : Nat) : List (Arg Nat) := ((List.range n).map fun k => Arg.r (10 + k)).reverse

/-- `main`: load the parameters, compute the body into `7`, write it as 8 little-endian bytes, return -/
def mainTC (p : Prog) : TC :=
  let r := cE p.2 (argEnv p.1) (10 + p.1)
  .seq (.seqs [ldArgs p.1, r.1, .i (.let_ 7 (.arg r.2.1)), .seqs ((List.range' 0 8).map wStep)]) (.term (.ret []))

/-- **the RTL program** of a nano program -/
def lower (p : Prog) : Proven.Ir.Prog VReg := ⟨[mkFunc [0, 1, 2] [0, 1, 2] 1 [(0, mainTC p)]], 0⟩

/-- **the code generator**: RISC-V machine code (empty if the IR back end rejects the program) -/
def nanoGenIR (p : Prog) : List UInt8 :=
  match compileW (lower p) with
  | some (ws, _) => Proven.Top.wordBytes ws
  | none => []

end Nano
