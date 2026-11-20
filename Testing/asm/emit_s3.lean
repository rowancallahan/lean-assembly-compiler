/- QEMU + Sail tests of the S3 route (`Riscv/Frontx/S3Examples.lean`): for every example the RTL program
`S3.lowerP P`, its words (`Ir.compile`: allocation, layout, emission), and 50 cases: input bytes, Lean's `main` on
them, and `memoryNeeded` (from the IR interpreter, which is checked against Lean's result).  Run:
`lake env lean --tstack=4000000 Testing/asm/emit_s3.lean`, then `python3 Testing/asm/ir_test.py check 50 s3_<name>`
(QEMU + Sail at `memoryNeeded` and `memoryNeeded - 1`).  Helpers copied from `Testing/asm/emit_ind_ir.lean`. -/
import Legacy.Riscv.Back.IrTarget
import Legacy.Compiler.Ir.Lin
import Legacy.Riscv.Frontx.S3Examples
open Proven.Ir Proven.Mach.Riscv Proven.Top.Alloc
open Proven.S3 Proven.S3.Ex Proven.Frontx.IndEx

def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64

def compileT (P : Prog VReg) : Option (List (BitVec 32) × Prog Nat) :=
  match alloc P with
  | some Q => (rvT.lin Q).map fun c => (rvT.words c, Q)
  | none => none

def mainSlots (Q : Prog Nat) : Nat := ((Q.funcs[Q.main]?).map (·.slots)).getD 0

/-- the peak, oldest event first (the same as `peak`, in one pass) -/
def peakF (E : List MemEvent) : Nat :=
  (E.reverse.foldl (fun (c, m) e => match e with
    | .alloc n => (c + n, max m (c + n)) | .free n => (c - n, max m (c - n))) (0, 0)).2


/-! ### A fast interpreter (arrays) of the IR semantics `Compiler/Ir/Sem.lean`, for the tests only: the same
steps as `step`, with arrays for the memory and the blocks; checked against `interp` on the small cases. -/
namespace Fast
open Proven.Mach
structure FFr where
  f : Nat
  l : Nat
  pc : Nat
  regs : Array Val
  dst : List Nat
structure FSt where
  inp : Array UInt8
  out : Array (Option UInt8)
  cells : Array (Option Val)
  blks : Array (Nat × Nat × Bool)
  ev : List MemEvent
def get (g : Array Val) (x : Nat) : Val := g.getD x (.w 0)
def set (g : Array Val) (x : Nat) (v : Val) : Array Val :=
  if x < g.size then g.set! x v else (g ++ Array.replicate (x + 1 - g.size) (Val.w 0)).set! x v
def aval (g : Array Val) : Arg Nat → Val | .r x => get g x | .i c => .w c
def word (g : Array Val) (a : Arg Nat) : Option (BitVec 64) := match aval g a with | .w x => some x | _ => none
def blk (m : FSt) : Nat → Option (Nat × Nat)
  | 0 | 1 => none
  | k + 2 => match m.blks[k]? with | some (st, sz, true) => some (st, sz) | _ => none
def setMany (g : Array Val) : List Nat → List Val → Array Val
  | x :: xs, v :: vs => setMany (set g x v) xs vs
  | _, _ => g
def rhs (m : FSt) (g : Array Val) : Rhs Nat → Option Val
  | .arg a => some (aval g a)
  | .op o a b => match word g a, word g b with | some x, some y => some (.w (o.eval x y)) | _, _ => none
  | .mop mo a b => match word g a, word g b with | some x, some y => some (.w (mo.eval x y)) | _, _ => none
  | .padd p i => match get g p, word g i with
    | .p b o, some k => match blk m b with
      | some (_, sz) => if o + k.toNat ≤ sz then some (.p b (o + k.toNat)) else none
      | none => none
    | _, _ => none
def tst (g : Array Val) (t : Tst Nat) : Option Bool :=
  match aval g t.a, aval g t.b with
  | .w x, .w y => some (t.c.eval x y)
  | .p _ _, .w y => if y = 0 then nullTest t.c else none
  | .w x, .p _ _ => if x = 0 then nullTest t.c else none
  | .p _ _, .p _ _ => none
def setOut (out : Array (Option UInt8)) (i : Nat) (v : UInt8) : Array (Option UInt8) :=
  if i < out.size then out.set! i (some v) else (out ++ Array.replicate (i - out.size) none).push (some v)
def exec (m : FSt) (g : Array Val) : Inst Nat → Option (Array Val × FSt)
  | .let_ d e => (rhs m g e).map fun v => (set g d v, m)
  | .ldb d p i => match word g i, get g p with
    | some k, .p 0 0 => (m.inp[k.toNat]?).map fun b => (set g d (.w (b.toBitVec.setWidth 64)), m)
    | some k, .p 1 0 => match m.out[k.toNat]? with
      | some (some b) => some (set g d (.w (b.toBitVec.setWidth 64)), m)
      | _ => none
    | _, _ => none
  | .stb v p i => match word g v, word g i, get g p with
    | some x, some k, .p 1 0 => some (g, { m with out := setOut m.out k.toNat (UInt8.ofBitVec (x.setWidth 8)) })
    | _, _, _ => none
  | .ld d p k => match get g p with
    | .p b o => match blk m b with
      | some (c0, sz) => if o + k < sz then (match m.cells[c0 + o + k]? with
          | some (some v) => some (set g d v, m) | _ => none) else none
      | none => none
    | .w _ => none
  | .st v p k => match get g p with
    | .p b o => match blk m b with
      | some (c0, sz) => if o + k < sz then some (g, { m with cells := m.cells.set! (c0 + o + k) (some (aval g v)) })
          else none
      | none => none
    | .w _ => none
  | .alloc d n => match word g n with
    | some c => some (set g d (.p (m.blks.size + 2) 0),
        { m with cells := m.cells ++ Array.replicate c.toNat none, blks := m.blks.push (m.cells.size, c.toNat, true)
                 ev := MemEvent.alloc c.toNat :: m.ev })
    | none => none
  | .free p => match get g p with
    | .p (k + 2) 0 => match blk m (k + 2) with
      | some (c0, sz) => some (g, { m with blks := m.blks.set! k (c0, sz, false), ev := .free sz :: m.ev })
      | none => none
    | _ => none
  | .call _ _ _ => none
/-- per function: params, entry, slots, the blocks by label -/
structure FF where
  F : Func Nat
  bl : Array (Option (Block Nat))
def mk (F : Func Nat) : FF :=
  let n := (F.blocks.map (·.1)).foldl max 0 + 1
  ⟨F, (List.range n).toArray.map fun l => F.blocks.lookup l⟩
def jump (FF : FF) (fr : FFr) (l : Nat) (vs : List Val) : Option FFr :=
  match FF.bl[l]? with
  | some (some B) => if vs.length = B.params.length then some { fr with l := l, pc := 0, regs := setMany fr.regs B.params vs }
      else none
  | _ => none
partial def run (P : Array FF) (fuel : Nat) (stk : List FFr) (m : FSt) : Option (List Val × FSt) :=
  if fuel = 0 then none else
  match stk with
  | [] => none
  | fr :: rest => match P[fr.f]? with
    | none => none
    | some F => match F.bl[fr.l]? with
      | some (some B) => match B.body[fr.pc]? with
        | some (.call ds g as) => match P[g]? with
          | some G => if as.length = G.F.params.length then
              run P (fuel - 1) (⟨g, G.F.entry, 0, setMany #[] G.F.params (as.map (aval fr.regs)), ds⟩ ::
                { fr with pc := fr.pc + 1 } :: rest) { m with ev := .alloc (G.F.slots + 1) :: m.ev }
            else none
          | none => none
        | some i => match exec m fr.regs i with
          | some (g', m') => run P (fuel - 1) ({ fr with pc := fr.pc + 1, regs := g' } :: rest) m'
          | none => none
        | none => match B.term with
          | .jmp l as => (jump F fr l (as.map (aval fr.regs))).bind fun fr' => run P (fuel - 1) (fr' :: rest) m
          | .br t l₁ a₁ l₂ a₂ => match tst fr.regs t with
            | some true => (jump F fr l₁ (a₁.map (aval fr.regs))).bind fun fr' => run P (fuel - 1) (fr' :: rest) m
            | some false => (jump F fr l₂ (a₂.map (aval fr.regs))).bind fun fr' => run P (fuel - 1) (fr' :: rest) m
            | none => none
          | .switch x ls d => match get fr.regs x with
            | .w k => (jump F fr (ls[k.toNat]?.getD d) []).bind fun fr' => run P (fuel - 1) (fr' :: rest) m
            | _ => none
          | .ret vs => match rest with
            | [] => some (vs.map (aval fr.regs), m)
            | c :: rest' => if vs.length = fr.dst.length then
                run P (fuel - 1) ({ c with regs := setMany c.regs fr.dst (vs.map (aval fr.regs)) } :: rest')
                  { m with ev := .free (F.F.slots + 1) :: m.ev }
              else none
      | _ => none
def interp (Q : Prog Nat) (fuel : Nat) (input : List UInt8) : Option (List UInt8 × List MemEvent) :=
  let P := Q.funcs.toArray.map mk
  match P[Q.main]? with
  | none => none
  | some F =>
    match run P fuel [⟨Q.main, F.F.entry, 0, setMany #[] F.F.params [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0], []⟩]
        ⟨input.toArray, #[], #[], #[], []⟩ with
    | some (_, m) => (m.out.toList.mapM id).map fun o => (o, m.ev)
    | none => none
end Fast

def emitR (name : String) (P : Prog VReg) (_retLen : Bool) (cases : List (List UInt8 × List UInt8)) : IO Unit := do
  -- `IR_SKIP=1`: keep the outputs of entries already emitted
  if (← IO.getEnv "IR_SKIP") == some "1" && (← System.FilePath.pathExists s!"Testing/asm/ir-words/{name}.cases") then
    IO.println s!"{name}: kept"; return
  let t0 ← IO.monoMsNow
  match compileT P with
  | none => IO.println s!"{name}: compile failed"
  | some (ws, Q) =>
    IO.FS.writeFile s!"Testing/asm/ir-words/{name}.words" (String.intercalate "\n" (s!"{name} 0" :: ws.map hex8) ++ "\n")
    let mut s := ""
    let mut bad := 0
    let mut k := 0
    for (x, y) in cases do
      -- the fast interpreter, checked against `interp` on the first cases
      let r := Fast.interp Q 1000000000 x
      if k < 3 && x.length < 64 then
        if (interp Q 10000000 x).map (fun (o, ev) => (o, peakF (ev ++ [MemEvent.alloc (mainSlots Q + 3)]))) !=
            r.map (fun (o, ev) => (o, peakF (ev ++ [MemEvent.alloc (mainSlots Q + 3)]))) then
          IO.println s!"{name}: FAST INTERPRETER DIFFERS on {hx x}"
      k := k + 1
      match r with
      | some (o, ev) =>
        if o != y then bad := bad + 1
        s := s ++ s!"{hx x} {hx y} {8 * peakF (ev ++ [.alloc (mainSlots Q + 3)])}\n"
      | none => bad := bad + 1
    IO.FS.writeFile s!"Testing/asm/ir-words/{name}.cases" s
    IO.println s!"{name}: {ws.length} words, {cases.length} cases, interpreter output != Lean: {bad} ({(← IO.monoMsNow) - t0} ms)"

def emitRW (name : String) (P : Prog VReg) (retLen : Bool) (cases : List (List UInt8 × List UInt8 × Nat)) : IO Unit :=
  emitR name P retLen (cases.map fun (x, y, _) => (x, y))

/-! ## inputs -/

def rndN (i j : Nat) : Nat := rnd i j
def genT : Nat → Nat → BinTree UInt64
  | 0, _ => .leaf
  | d + 1, s => if rndN s 1 % 4 == 0 then .leaf else
    .branch (genT d (rndN s 2 % 1000)) (UInt64.ofNat (rndN s 3 % 256)) (genT d (rndN s 4 % 1000))
def trees : List (BinTree UInt64) := [.leaf, .branch .leaf 7 .leaf] ++ (List.range 48).map fun i => genT (i % 6 + 1) (i + 3)
def words (i : Nat) : List UInt64 := (List.range (i % 9)).map fun j => UInt64.ofNat (rndN i (j + 1))
def bytes (i : Nat) : List UInt8 := (List.range (i % 23)).map fun j => UInt8.ofNat (rndN i (j + 7) % (if i % 3 == 0 then 8 else 256))
def genP : Nat → Pos | 0 => .one | n + 1 => .succ (genP n)

def appIn (xs ys : List UInt8) : List UInt8 := xs.flatMap (fun b => [1, b]) ++ [0] ++ ys

def cases50 (f : Nat → List UInt8) : List (List UInt8) := (List.range 50).map f

def run (name : String) (P : Prog) (main : List UInt8 → List UInt8) (ins : List (List UInt8)) : IO Unit :=
  emitR name (lowerP P) false (ins.map fun x => (x, main x))

#eval do
  run "s3_mirror" S3Mirror.P mirrorMain (trees.map encT)
  run "s3_graft" S3Graft.P graftMain (cases50 fun i => encT (trees.getD i .leaf) ++ encT (trees.getD ((i * 7 + 3) % 50) .leaf))
  run "s3_posplus" S3PosPlus.P posPlusMain (cases50 fun i => encP (genP (rndN i 1 % 40)) ++ encP (genP (rndN i 2 % 40)))
  run "s3_eqtree" S3EqTree.P eqTreeMain (cases50 fun i =>
    let t := trees.getD i .leaf; encT t ++ encT (if i % 2 == 0 then t else trees.getD ((i * 7 + 3) % 50) .leaf))
  run "s3_tailrev" S3TailRev.P tailRevMain (cases50 fun i => encW (words i))
  run "s3_nontailrev" S3NonTailRev.P nonTailRevMain (cases50 fun i => encW (words i))
  run "s3_filter" S3Filter.P Proven.Frontx.BookOut.filterGt3 (cases50 bytes)
  run "s3_append" S3Append.P appendMain (cases50 fun i => appIn (bytes i) (bytes (i + 50)))
  run "s3_swap" S3Swap.P swapMain (cases50 fun i => encW (words (i * 9 + 2 + i % 3)))
  run "s3_weekend" S3Weekend.P weekendMain (cases50 fun i => if i == 49 then [] else [UInt8.ofNat (i % 9)])
  run "s3_replacex" S3ReplaceX.P replaceXMain (cases50 fun i => encW (words (i * 9 + 3 + i % 5)))
  run "s3_fromoption" S3FromOption.P fromOptionMain (cases50 fun i => encW (words (i * 9 + i % 4)))
  run "s3_small" S3Small.P smallMain (cases50 fun i => if i == 49 then [] else [UInt8.ofNat (i % 3)])
  run "s3_find" S3Find.P findMain (cases50 bytes)
  run "s3_pttree" S3PtTree.P ptTreeMain (trees.map encT)
