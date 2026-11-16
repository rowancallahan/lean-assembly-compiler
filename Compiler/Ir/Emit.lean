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
def R2 : Reg := ⟨2, by decide⟩
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

def R7 : Reg := ⟨7, by decide⟩
def R8 : Reg := ⟨8, by decide⟩
def R9 : Reg := ⟨9, by decide⟩

/-- the registers `r0 .. r6` -/
def argRegs : List Reg := (List.range 7).map rk

/-- what the code of one function knows about the others: where each starts, its slots, its parameter count -/
structure Env where
  fq : FId → Nat
  fs : FId → Nat
  fp : FId → Nat

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

/-- the code of an instruction other than `call` at word `q` (`ex`: the out-of-memory exit) -/
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

/-- the check that a frame of `n` slots fits below the current one (`r7 := free bytes`, `r8 := frame bytes`;
else to the exit), then the frame limit moved down -/
def chkPre (n : Nat) : List EOp :=
  [.w (.bin .sub R7 RLim RHp), .w (.li R8 (BitVec.ofNat 64 (8 * (n + 1)))),
    .w (.br .geu R7 (some R8) false (T.lenBr + T.lenJ))]

/-- the frame check, the call of the function at word `t` (from word `q`) -/
def callTo (ex n q t : Nat) : Option (List EOp) :=
  match T.jW (q + T.len (T.chkPre n)) ex with
  | some j =>
    let qc := q + T.len (T.chkPre n ++ [j, .w (.bin .sub RLim RLim R8)])
    if T.callOK ((t : Int) - qc) = true then
      some (T.chkPre n ++ [j, .w (.bin .sub RLim RLim R8), .call ((t : Int) - qc)])
    else none
  | none => none

/-- after the return: the frame limit back up, the results from `r0 ..` into their slots -/
def callPost (n : Nat) (ds : List Nat) : List EOp :=
  [.w (.li R9 (BitVec.ofNat 64 (8 * (n + 1)))), .w (.bin .add RLim RLim R9)] ++ storeRegs ds argRegs

/-- the code of `call ds g as` at word `q` -/
def emitCall (E : Env) (nS ex q : Nat) (ds : List Nat) (g : FId) (as : List (Arg Nat)) : Option (List EOp) :=
  if as.length ≤ 7 ∧ ds.length ≤ 7 ∧ as.all (okA nS) = true ∧ ds.all (· < nS) = true ∧ as.length = E.fp g ∧
      E.fs g ≤ T.maxSlots ∧ 8 * (E.fs g + 1) < 2 ^ 64 ∧ T.brOK false (T.lenBr + T.lenJ) = true then
    (T.callTo ex (E.fs g) (q + T.len (loadAll 0 as)) (E.fq g)).map fun c => loadAll 0 as ++ c ++ callPost (E.fs g) ds
  else none

def emitI' (E : Env) (nS ex q : Nat) : Inst Nat → Option (List EOp)
  | .call ds g as => T.emitCall E nS ex q ds g as
  | i => T.emitI nS ex q i

def emitIs (E : Env) (nS ex : Nat) : Nat → List (Inst Nat) → Option (List EOp)
  | _, [] => some []
  | q, i :: is => match T.emitI' E nS ex q i with
    | some c => (emitIs E nS ex (q + T.len c) is).map (c ++ ·)
    | none => none

/-- `switch`: the value in `r0`, then per index `i` a test `r0 = i` and a branch to its block -/
def swChain (pos : Lbl → Nat) : Nat → Nat → List Lbl → Option (List EOp)
  | _, _, [] => some []
  | q, i, l :: ls => match T.brTo .eq (q + T.len [.w (.li R1 (BitVec.ofNat 64 i))]) (pos l) with
    | some b => (swChain pos (q + T.len ([.w (.li R1 (BitVec.ofNat 64 i))] ++ b)) (i + 1) ls).map
        fun c => [.w (.li R1 (BitVec.ofNat 64 i))] ++ b ++ c
    | none => none

/-- a block without parameters -/
def noParams (F : Func Nat) (l : Lbl) : Bool := ((F.blocks.lookup l).map fun B => B.params.isEmpty) == some true

def emitT (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (q : Nat) : Term Nat → Option (List EOp)
  | .jmp l as => T.edge F nS pos q l as
  | .br t l₁ a₁ l₂ a₂ =>
    if a₁.isEmpty = true ∧ okA nS t.a = true ∧ okA nS t.b = true then
      match T.brTo t.c (q + T.len [ldArg R0 t.a, ldArg R1 t.b]) (pos l₁) with
      | some b => (T.edge F nS pos (q + T.len ([ldArg R0 t.a, ldArg R1 t.b] ++ b)) l₂ a₂).map
          fun e => [ldArg R0 t.a, ldArg R1 t.b] ++ b ++ e
      | none => none
    else none
  | .ret vs => if vs.length ≤ 7 ∧ vs.all (okA nS) = true ∧ nS ≤ T.maxSlots then
      some (loadAll 0 vs ++ [.leaveC nS, .w .ret]) else none
  | .switch x ls d =>
    if x < nS ∧ ls.length < 2 ^ 32 ∧ ls.all (noParams F) = true ∧ noParams F d = true then
      match T.swChain pos (q + T.len [.w (.ldS R0 x)]) 0 ls with
      | some c => (T.jTo (q + T.len ([.w (.ldS R0 x)] ++ c)) (pos d)).map fun j => [.w (.ldS R0 x)] ++ c ++ j
      | none => none
    else none

def emitB (E : Env) (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (ex q : Nat) (B : Block Nat) : Option (List EOp) :=
  match T.emitIs E nS ex q B.body with
  | some c => (T.emitT F nS pos (q + T.len c) B.term).map (c ++ ·)
  | none => none

/-- the blocks in order; each must start where `pos` says, the code must end where `qe` says -/
def emitBs (E : Env) (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (ex qe : Nat) :
    Nat → List (Lbl × Block Nat) → Option (List EOp)
  | q, [] => if q = qe then some [] else none
  | q, (l, B) :: bs => if pos l = q then
      match T.emitB E F nS pos ex q B with
      | some c => (emitBs E F nS pos ex qe (q + T.len c) bs).map (c ++ ·)
      | none => none
    else none

/-- `n` zero slots (`r7` holds zero) -/
def zeros (n : Nat) : List EOp := (List.range n).map fun j => .w (.stS j R7)

/-- the prologue of a function: open its frame, all slots zero, the arguments into the parameter slots -/
def proF (nS : Nat) (F : Func Nat) : List EOp :=
  [.enterC nS, .w (.li R7 0)] ++ zeros nS ++ storeAll 0 F.params

/-- **the code of a function** at word `q` (its blocks at `pos`, the next function at `qe`) -/
def emitF (E : Env) (F : Func Nat) (pos : Lbl → Nat) (ex q qe : Nat) : Option (List EOp) :=
  if F.slots ≤ T.maxSlots ∧ F.slots < 2 ^ 32 ∧ F.params.length ≤ 7 ∧ (F.blocks.lookup F.entry).isSome = true ∧
      F.params.all (· < F.slots) = true then
    match T.jTo (q + T.len (proF F.slots F)) (pos F.entry) with
    | some j => (T.emitBs E F F.slots pos ex qe (q + T.len (proF F.slots F ++ j)) F.blocks).map
        fun b => proF F.slots F ++ j ++ b
    | none => none
  else none

/-- the stub: check its two cells fit (else `exit0`), open them (the caller's frame register, the return
address), the frame limit, the arguments `input, length, output` of `main` -/
def stub1 : List EOp :=
  [.top R0, .w (.bini .add R0 R0 8), .w (.bin .sub R1 R0 RHp), .w (.li R2 16),
    .w (.br .geu R1 (some R2) false (T.lenBr + T.len exit0))]

def stub2 : List EOp :=
  [.w (.bin .sub RLim R0 R2), .enter 0, .enterC 0, .w (.mov R0 RIn), .w (.mov R1 RLen), .w (.mov R2 ROut)]

/-- after `main` returns: close the stub's cells, return -/
def stub3 : List EOp := [.leaveC 0, .leave, .w .ret]

/-- the stub, calling `main` (at word `t`, with `n` slots) -/
def emitStub (ex n t : Nat) : Option (List EOp) :=
  if T.immOK .add 8 = true ∧ T.brOK false (T.lenBr + T.len exit0) = true ∧ T.brOK false (T.lenBr + T.lenJ) = true ∧
      n ≤ T.maxSlots ∧ 8 * (n + 1) < 2 ^ 64 then
    (T.callTo ex n (T.len (T.stub1 ++ exit0 ++ stub2)) t).map fun c => T.stub1 ++ exit0 ++ stub2 ++ c ++ stub3
  else none

end Target

/-! ## The whole program -/

/-- where things are: per function its start and its block positions, the exit -/
structure Lay where
  fq : List Nat
  pos : List (List (Lbl × Nat))
  ex : Nat
  deriving Repr

def posOf (ps : List (Lbl × Nat)) (l : Lbl) : Nat := (ps.lookup l).getD 0

def Lay.posF (L : Lay) (f : FId) : Lbl → Nat := posOf (L.pos.getD f [])

def Prog.env (P : Prog Nat) (L : Lay) : Env :=
  ⟨fun f => L.fq.getD f 0, fun f => ((P.funcs[f]?).map (·.slots)).getD 0,
    fun f => ((P.funcs[f]?).map (·.params.length)).getD 0⟩

namespace Target
variable (T : Target)

/-- the functions in order, function `f` at `L.fq[f]` -/
def emitFs (P : Prog Nat) (L : Lay) : FId → Nat → List (Func Nat) → Option (List EOp)
  | _, q, [] => if q = L.ex then some [] else none
  | f, q, F :: Fs => if L.fq.getD f 0 = q then
      match T.emitF (P.env L) F (L.posF f) L.ex q (L.fq.getD (f + 1) L.ex) with
      | some c => (emitFs P L (f + 1) (q + T.len c) Fs).map (c ++ ·)
      | none => none
    else none

/-- **the code of a program**: the stub, the functions, the exit -/
def emitP (P : Prog Nat) (L : Lay) : Option (List EOp) :=
  if ((P.funcs[P.main]?).map (·.params.length)) = some 3 then
    match T.emitStub L.ex (((P.funcs[P.main]?).map (·.slots)).getD 0) (L.fq.getD P.main 0) with
    | some st => (T.emitFs P L 0 (T.len st) P.funcs).map fun c => st ++ c ++ [.exit]
    | none => none
  else none

/-! ## The untrusted layout (positions by fixpoint iteration) -/

def starts (E : Env) (F : Func Nat) (nS : Nat) (pos : Lbl → Nat) (ex : Nat) :
    Nat → List (Lbl × Block Nat) → List (Lbl × Nat) × Nat
  | q, [] => ([], q)
  | q, (l, B) :: bs =>
    let r := starts E F nS pos ex (q + ((T.emitB E F nS pos ex q B).map T.len).getD 0) bs
    ((l, q) :: r.1, r.2)

/-- one round: every function's start and block positions from the previous round's -/
def layFs (P : Prog Nat) (L : Lay) : FId → Nat → List (Func Nat) → List Nat × List (List (Lbl × Nat)) × Nat
  | _, q, [] => ([], [], q)
  | f, q, F :: Fs =>
    let q1 := q + T.len (proF F.slots F) + T.len ((T.jTo (q + T.len (proF F.slots F)) (L.posF f F.entry)).getD [])
    let r := T.starts (P.env L) F F.slots (L.posF f) L.ex q1 F.blocks
    let rest := layFs P L (f + 1) r.2 Fs
    (q :: rest.1, r.1 :: rest.2.1, rest.2.2)

def layStep (P : Prog Nat) (L : Lay) : Lay :=
  let q0 := ((T.emitStub L.ex (((P.funcs[P.main]?).map (·.slots)).getD 0) (L.fq.getD P.main 0)).map T.len).getD 0
  let r := T.layFs P L 0 q0 P.funcs
  ⟨r.1, r.2.1, r.2.2⟩

def layout (P : Prog Nat) : Nat → Lay → Lay
  | 0, L => L
  | k + 1, L => layout P k (T.layStep P L)

/-- the number of rounds: enough for every jump to settle in practice (any result is checked by `emitP`) -/
def rounds (P : Prog Nat) : Nat := (P.funcs.map fun F => F.blocks.length).foldl (· + ·) 0 + 8

end Target
end Proven.Ir
