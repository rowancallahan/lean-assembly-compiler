/- Emission of a Lin function (every location a frame slot) to target operations (`EOp`), with
* placement: the work block holds the frame at its top (`enter nS`) and the cell blocks at its bottom, bump
  allocated in `r13`; `r10` holds the frame base (the heap limit); `alloc` checks the free cells and jumps to the
  out-of-memory exit (`leave; a0 := -1; ret`) when the request does not fit;
* long branches: a conditional branch is the short form when the distance is in range (`brOK`), else the inverted
  short branch over a jump (`br ¬c +2; jmp far`); distances come from block positions `pos` computed by an
  untrusted fixpoint (`layout`) and are re-decided here; `emitBs` checks that every block starts where `pos`
  says, so a wrong hint gives `none`, never wrong code.

Register use: `r0 .. r6` scratch (`r0 .. r6` carry the arguments of a jump), `r10` limit, `r11` input address
(the status register at the end), `r12` input length, `r13` heap pointer, `r14` output address. -/
import Compiler.Ir.Target
import Compiler.Ir.Sem

namespace Proven.Ir
open Proven.Mach
set_option autoImplicit false

def R0 : Reg := ⟨0, by decide⟩
def R1 : Reg := ⟨1, by decide⟩
def RLim : Reg := ⟨10, by decide⟩
def RIn : Reg := ⟨11, by decide⟩
def RLen : Reg := ⟨12, by decide⟩
def RHp : Reg := ⟨13, by decide⟩
def ROut : Reg := ⟨14, by decide⟩

def okA (nS : Nat) : Arg Nat → Bool
  | .r x => decide (x < nS)
  | .i _ => true

def ldArg (d : Reg) : Arg Nat → EOp
  | .r x => .w (.ldS d x)
  | .i c => .w (.li d c)

/-- load the arguments into `r0, r1, ...` -/
def loadAll : Nat → List (Arg Nat) → List EOp
  | _, [] => []
  | k, a :: as => ldArg (rk k) a :: loadAll (k + 1) as

/-- store `r0, r1, ...` into the parameters -/
def storeAll : Nat → List Nat → List EOp
  | _, [] => []
  | k, p :: ps => .w (.stS p (rk k)) :: storeAll (k + 1) ps

/-- store registers into slots, pairwise -/
def storeRegs : List Nat → List Reg → List EOp
  | p :: ps, r :: rs => .w (.stS p r) :: storeRegs ps rs
  | _, _ => []

def exit0 : List EOp := [.w (.li RIn (BitVec.allOnes 64)), .w .ret]
def exit1 : List EOp := [.leave, .w (.li RIn (BitVec.allOnes 64)), .w .ret]

namespace Target
variable (T : Target)

def len (os : List EOp) : Nat := (T.words os).length

/-- one jump from word `q` to word `t` -/
def jW (q t : Nat) : Option EOp :=
  if q ≤ t then (if T.jOK false (t - q) then some (.w (.jmp false (t - q))) else none)
  else (if T.jOK true (q - t) then some (.w (.jmp true (q - t))) else none)

/-- go from word `q` to word `t`: nothing when `t = q` (fall through) -/
def jTo (q t : Nat) : Option (List EOp) :=
  if t = q then some [] else (T.jW q t).map ([·])

/-- a conditional branch from word `q` to word `t` on `c r0 r1`: short when in range, else long -/
def brTo (c : Cond) (q t : Nat) : Option (List EOp) :=
  if T.brOK (decide (t < q)) (if t < q then q - t else t - q) then
    some [.w (.br c R0 (some R1) (decide (t < q)) (if t < q then q - t else t - q))]
  else if T.brOK false (T.lenBr + T.lenJ) then
    (T.jW (q + T.lenBr) t).map fun j => [.w (.br c.neg R0 (some R1) false (T.lenBr + T.lenJ)), j]
  else none

/-- the code of an edge from word `q`: the arguments into the parameters of `l`, then to `l` -/
def edge (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (q : Nat) (l : Lbl) (as : List (Arg Nat)) :
    Option (List EOp) :=
  match F.blocks.lookup l with
  | none => none
  | some B =>
    if as.length = B.params.length ∧ as.length ≤ 7 ∧ as.all (okA nS) = true ∧ B.params.all (· < nS) = true then
      (T.jTo (q + T.len (loadAll 0 as ++ storeAll 0 B.params)) (pos l)).map
        fun j => loadAll 0 as ++ storeAll 0 B.params ++ j
    else none

/-- the code of an instruction at word `q` (`ex`: the out-of-memory exit) -/
def emitI (nS ex q : Nat) : Inst Nat → Option (List EOp)
  | .let_ d (.arg a) => if d < nS ∧ okA nS a = true then some [ldArg R0 a, .w (.stS d R0)] else none
  | .let_ d (.op o a b) => if d < nS ∧ okA nS a = true ∧ okA nS b = true then
      some [ldArg R0 a, ldArg R1 b, .w (.bin o R0 R0 R1), .w (.stS d R0)] else none
  | .let_ d (.mop m a b) => if d < nS ∧ okA nS a = true ∧ okA nS b = true then
      some [ldArg R0 a, ldArg R1 b, .w (.mop m R0 R0 R1), .w (.stS d R0)] else none
  | .let_ d (.padd p i) => if d < nS ∧ p < nS ∧ okA nS i = true ∧ T.immOK .shl 3 = true then
      some [.w (.ldS R0 p), ldArg R1 i, .w (.bini .shl R1 R1 3), .w (.bin .add R0 R0 R1), .w (.stS d R0)] else none
  | .ldb d p i => if d < nS ∧ p < nS ∧ okA nS i = true ∧ T.offOK 0 = true then
      some [.w (.ldS R0 p), ldArg R1 i, .w (.bin .add R0 R0 R1), .w (.lbu R0 R0 0), .w (.stS d R0)] else none
  | .stb v p i => if p < nS ∧ okA nS i = true ∧ okA nS v = true ∧ T.offOK 0 = true then
      some [.w (.ldS R0 p), ldArg R1 i, .w (.bin .add R0 R0 R1), ldArg R1 v, .w (.sb R1 R0 0)] else none
  | .ld d p k => if d < nS ∧ p < nS ∧ k < 2 ^ 32 ∧ T.offOK (BitVec.ofNat 64 (8 * k)) = true then
      some [.w (.ldS R0 p), .w (.ld R0 R0 (BitVec.ofNat 64 (8 * k))), .w (.stS d R0)] else none
  | .st v p k => if p < nS ∧ okA nS v = true ∧ k < 2 ^ 32 ∧ T.offOK (BitVec.ofNat 64 (8 * k)) = true then
      some [.w (.ldS R0 p), ldArg R1 v, .w (.sd R1 R0 (BitVec.ofNat 64 (8 * k)))] else none
  | .alloc d n =>
    if d < nS ∧ okA nS n = true ∧ T.immOK .lshr 3 = true ∧ T.immOK .shl 3 = true ∧
        T.brOK false (T.lenBr + T.lenJ) = true then
      (T.jW (q + T.len [ldArg R0 n, .w (.bin .sub R1 RLim RHp), .w (.bini .lshr R1 R1 3),
          .w (.br .geu R1 (some R0) false (T.lenBr + T.lenJ))]) ex).map fun j =>
        [ldArg R0 n, .w (.bin .sub R1 RLim RHp), .w (.bini .lshr R1 R1 3),
          .w (.br .geu R1 (some R0) false (T.lenBr + T.lenJ)), j,
          .w (.stS d RHp), .w (.bini .shl R0 R0 3), .w (.bin .add RHp RHp R0)]
    else none
  | _ => none

def emitIs (nS ex : Nat) : Nat → List (Inst Nat) → Option (List EOp)
  | _, [] => some []
  | q, i :: is => match T.emitI nS ex q i with
    | some c => (emitIs nS ex (q + T.len c) is).map (c ++ ·)
    | none => none

def emitT (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (q : Nat) : Term Nat → Option (List EOp)
  | .jmp l as => T.edge F nS pos q l as
  | .br t l₁ a₁ l₂ a₂ =>
    if a₁.isEmpty = true ∧ okA nS t.a = true ∧ okA nS t.b = true then
      match T.brTo t.c (q + T.len [ldArg R0 t.a, ldArg R1 t.b]) (pos l₁) with
      | some b => (T.edge F nS pos (q + T.len ([ldArg R0 t.a, ldArg R1 t.b] ++ b)) l₂ a₂).map
          fun e => [ldArg R0 t.a, ldArg R1 t.b] ++ b ++ e
      | none => none
    else none
  | .ret _ => some [.leave, .w .ret]
  | .switch _ _ _ => none

def emitB (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (ex q : Nat) (B : Block Nat) : Option (List EOp) :=
  match T.emitIs nS ex q B.body with
  | some c => (T.emitT F nS pos (q + T.len c) B.term).map (c ++ ·)
  | none => none

/-- the blocks in order; each must start where `pos` says, the exit where `ex` says -/
def emitBs (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (ex : Nat) : Nat → List (Lbl × Block Nat) → Option (List EOp)
  | q, [] => if q = ex then some [] else none
  | q, (l, B) :: bs => if pos l = q then
      match T.emitB F nS pos ex q B with
      | some c => (emitBs F nS pos ex (q + T.len c) bs).map (c ++ ·)
      | none => none
    else none

/-- check the frame fits (else `exit0`), then the frame limit into `r10` -/
def pro1 (nS : Nat) : List EOp :=
  [.top RLim, .w (.bini .add RLim RLim 8), .w (.bin .sub R0 RLim RHp), .w (.li R1 (BitVec.ofNat 64 (8 * (nS + 1)))),
    .w (.br .geu R0 (some R1) false (T.lenBr + T.len exit0))]

/-- open the frame, the parameters of `main` into their slots -/
def pro2 (nS : Nat) (F : Func Nat) : List EOp :=
  [.w (.bin .sub RLim RLim R1), .enter nS] ++ storeRegs F.params [RIn, RLen, ROut]

def pro (nS : Nat) (F : Func Nat) : List EOp := T.pro1 nS ++ exit0 ++ pro2 nS F

/-- **the code of a function** -/
def emitF (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (ex : Nat) : Option (List EOp) :=
  if nS ≤ T.maxSlots ∧ F.params.all (· < nS) = true ∧ T.immOK .add 8 = true ∧
      T.brOK false (T.lenBr + T.len exit0) = true then
    match T.jTo (T.len (T.pro nS F)) (pos F.entry) with
    | some j => (T.emitBs F nS pos ex (T.len (T.pro nS F ++ j)) F.blocks).map fun b => T.pro nS F ++ j ++ b ++ exit1
    | none => none
  else none

/-! ## The untrusted layout (block positions by fixpoint iteration) -/

def starts (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (ex : Nat) :
    Nat → List (Lbl × Block Nat) → List (Lbl × Nat) × Nat
  | q, [] => ([], q)
  | q, (l, B) :: bs =>
    let r := starts F nS pos ex (q + ((T.emitB F nS pos ex q B).map T.len).getD 0) bs
    ((l, q) :: r.1, r.2)

def posOf (ps : List (Lbl × Nat)) (l : Lbl) : Nat := (ps.lookup l).getD 0

def layout (F : Func Nat) (nS : Nat) : Nat → List (Lbl × Nat) × Nat → List (Lbl × Nat) × Nat
  | 0, h => h
  | k + 1, (ps, ex) =>
    let q := T.len (T.pro nS F) + T.len (((T.jTo (T.len (T.pro nS F)) (posOf ps F.entry))).getD [])
    layout F nS k (T.starts F nS (posOf ps) ex q F.blocks)

end Target
end Proven.Ir
