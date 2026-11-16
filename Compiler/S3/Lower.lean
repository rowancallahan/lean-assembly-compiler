/- **Lowering S3 to the shared IR** (RTL, `Compiler/Ir/Syntax.lean`) through structured code (`SC`/`TC`,
`Compiler/Ir/Struct.lean`).

* a value lives in a register: a word as `.w`, a constructor `j` with fields `fs` as a pointer to a fresh block of
  `|fs| + 1` cells `[j, fs...]` (`Compiler/S3/LowerOk.lean`: `Rep`);
* `low e ρ n` puts the value of `e` into register `n`, the variables being in the registers `ρ`, and writes only
  registers `≥ n`; `let` binds register `n`, `match` reads the tag into `n + 1` and the fields into `n + 2 ..`,
  dispatches by a chain of tag tests; calls are IR calls;
* function `f` is IR function `f` with parameters `0 .. k - 1`; IR function `|fns|` is `main`: it builds the input
  byte list (`inLoop`), calls the S3 `main`, writes the result list to the output (`outLoop`).

Pure Lean (core only). -/
import Compiler.S3.Syntax
import Compiler.Ir.IndLow

namespace Proven.S3
open Proven.Ir Proven.Ir.IndLow Proven.Mach
set_option autoImplicit false

def reg {Γ : List Ty} {τ : Ty} (ρ : List VReg) (x : Var Γ τ) : VReg := ρ.getD x.idx 0

def opK (o : Op) (d : VReg) (a b : Arg VReg) : SC := .i (.let_ d (.op o a b))

def lowPrim (o : Prim) (n a b : VReg) : SC :=
  match o with
  | .op o => opK o n (.r a) (.r b)
  | .mul => .i (.let_ n (.mop .mul (.r a) (.r b)))
  | .udiv => .ite ⟨.eq, .r b, .i 0⟩ (setK n 0) (.i (.let_ n (.mop .divu (.r a) (.r b))))
  | .urem => .i (.let_ n (.mop .remu (.r a) (.r b)))

def lowCmp (c : Cmp) (n a b : VReg) : SC :=
  match c with
  | .eq => opK .eq n (.r a) (.r b)
  | .ne => .seq (opK .eq n (.r a) (.r b)) (opK .xor n (.r n) (.i 1))
  | .ult => opK .ult n (.r a) (.r b)
  | .ule => .seq (opK .ult n (.r b) (.r a)) (opK .xor n (.r n) (.i 1))
  | .slt => opK .slt n (.r a) (.r b)
  | .sle => .seq (opK .slt n (.r b) (.r a)) (opK .xor n (.r n) (.i 1))

/-- load fields `0 .. m - 1` of the block `x` into `base ..` -/
def ldFs (x base : VReg) : Nat → SC
  | 0 => .nop
  | m + 1 => .seq (ldFs x base m) (.i (.ld (base + m) x (m + 1)))

/-- store the registers `rs` into cells `k ..` of the block `d` -/
def stFs (d : VReg) : Nat → List VReg → SC
  | _, [] => .nop
  | k, r :: rs => .seq (.i (.st (.r r) d k)) (stFs d (k + 1) rs)

/-- dispatch on the tag in `t`: arm `j` when the tag is `k + j` (the last arm unconditionally) -/
def chain (t : VReg) : Nat → List SC → SC
  | _, [] => .nop
  | _, [a] => a
  | k, a :: as => .ite ⟨.eq, .r t, .i (BitVec.ofNat 64 k)⟩ a (chain t (k + 1) as)

/-- the field registers of a match arm -/
def fregs (base m : Nat) : List VReg := (List.range m).map (base + ·)

/-- **the code of an expression**: its value into register `n` -/
def low {S : Sig} : {Γ : List Ty} → {τ : Ty} → Expr S Γ τ → List VReg → VReg → SC
  | _, _, .var x, ρ, n => mov n (reg ρ x)
  | _, _, .lit c, _, n => setK n c
  | _, _, .blit c, _, n => setK n (bv c)
  | _, _, .bin o a b, ρ, n => lowPrim o n (reg ρ a) (reg ρ b)
  | _, _, .cmp c a b, ρ, n => lowCmp c n (reg ρ a) (reg ρ b)
  | _, _, .bnot a, ρ, n => opK .xor n (.r (reg ρ a)) (.i 1)
  | _, _, .let_ e₁ e₂, ρ, n => .seq (low e₁ ρ n) (.seq (low e₂ (n :: ρ) (n + 1)) (mov n (n + 1)))
  | _, _, .ite c e₁ e₂, ρ, n => .ite ⟨.ne, .r (reg ρ c), .i 0⟩ (low e₁ ρ n) (low e₂ ρ n)
  | _, _, .mk _ j xs, ρ, n =>
    .seq (.i (.alloc n (.i (BitVec.ofNat 64 (xs.idxs.length + 1)))))
      (.seq (.i (.st (.i (BitVec.ofNat 64 j)) n 0)) (stFs n 1 (xs.idxs.map (ρ.getD · 0))))
  | _, _, .cas (i := i) x arms, ρ, n =>
    .seq (.i (.ld (n + 1) (reg ρ x) 0))
      (chain (n + 1) 0 (List.ofFn fun j =>
        .seq (ldFs (reg ρ x) (n + 2) (S.flds i j).length)
          (.seq (low (arms j) (fregs (n + 2) (S.flds i j).length ++ ρ) (n + 2 + (S.flds i j).length))
            (mov n (n + 2 + (S.flds i j).length)))))
  | _, _, .call f xs _, ρ, n => .i (.call [n] f.val (xs.idxs.map fun k => .r (ρ.getD k 0)))

/-- the code of a function with `k` parameters -/
def fnTC {S : Sig} {Γ : List Ty} {τ : Ty} (e : Expr S Γ τ) : TC :=
  .seq (low e (List.range Γ.length) Γ.length) (.term (.ret [.r Γ.length]))

def lowFn (P : Prog) (f : Fin P.S.fns.length) : Func VReg :=
  mkFunc (List.range P.S.fns[f].1.length) (List.range P.S.fns[f].1.length) 1 [(0, fnTC (P.body f))]

/-! ## `main`: bytes in, bytes out -/

/-- the input as a byte list in register `3` (built from the end; `4` the index) -/
def inLoop : SC :=
  SC.seqs [.i (.alloc 3 (.i 1)), .i (.st (.i 0) 3 0), mov 4 1,
    .loop ⟨.ne, .r 4, .i 0⟩ (SC.seqs [opK .sub 4 (.r 4) (.i 1), .i (.ldb 5 0 (.r 4)), .i (.alloc 6 (.i 3)),
      .i (.st (.i 1) 6 0), .i (.st (.r 5) 6 1), .i (.st (.r 3) 6 2), mov 3 6])]

/-- write the byte list in register `7` to the output (`8` the index, `9` the tag) -/
def outLoop : SC :=
  SC.seqs [setK 8 0, .i (.ld 9 7 0),
    .loop ⟨.ne, .r 9, .i 0⟩ (SC.seqs [.i (.ld 10 7 1), .i (.stb (.r 10) 2 (.r 8)), addK 8 8 1, .i (.ld 7 7 2),
      .i (.ld 9 7 0)])]

def mainTC (fm : FId) : TC := .seq (SC.seqs [inLoop, .i (.call [7] fm [.r 3]), outLoop]) (.term (.ret []))

def mainF (fm : FId) : Func VReg := mkFunc [0, 1, 2] [0, 1, 2] 1 [(0, mainTC fm)]

/-- **the RTL program of an S3 program** -/
def lowerP (P : Prog) : Ir.Prog VReg := ⟨List.ofFn (lowFn P) ++ [mainF P.main.val], P.S.fns.length⟩

end Proven.S3
