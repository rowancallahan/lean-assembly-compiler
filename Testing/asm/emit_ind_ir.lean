/- IR route of the inductive path (`Compiler/Ir/IndLow.lean`, `Riscv/Frontx/IndIr.lean`): for every `frontx_ind`
entry (NOTES §17/§21/§24/§25/§28) the RTL program `IndLow.lower` of the entry's program (the same `indProgM`
arguments as its `.code`), its words (`Ir.compile`: allocation, layout, emission with calls), and per case the
input, Lean's result and `memoryNeeded` (8 bytes times the peak of the Lin run's events plus the stub's and `main`'s
frame, from the IR interpreter; the interpreter's output is checked against Lean's).  Run:
`lake env lean --tstack=4000000 Testing/asm/emit_ind_ir.lean`, then `python3 Testing/asm/ir_test.py check 50 <name>`
(QEMU + Sail at `memoryNeeded` and `memoryNeeded - 1`). -/
import Riscv.Back.IrTarget
import Compiler.Ir.Lin
import Compiler.Ir.IndLow
import Riscv.Frontx.IndExamples
import Riscv.Frontx.Ind2Examples
import Riscv.Frontx.IndCmpExamples
import Riscv.Frontx.ExprExamples
open Proven.Frontx
open Proven (leN)
open Proven.Ir Proven.Mach.Riscv Proven.Top.Alloc
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64

open Lean Elab Term Meta in
/-- the RTL program of an entry's `.code` (`callsCode1W (indProgM sh shO pg hs bi ain a0 nb nl) res 0`) -/
elab "irprog% " n:ident : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo n
  let some (.defnInfo d) := (← getEnv).find? c | throwError "not a definition"
  match d.value.getAppFnArgs with
  | (``Proven.Mach.Riscv.callsCode1W, #[P, _, _]) =>
    let mut P := P
    for _ in [0:4] do
      if P.getAppFn.constName? == some ``Proven.Mach.Ind.indProgM then break
      match ← unfoldDefinition? P with
      | some P' => P := P'.headBeta
      | none => break
    match P.getAppFnArgs with
    | (``Proven.Mach.Ind.indProgM, #[rk, sh, shO, pg, hs, bi, ain, a0, nb, _]) =>
      return mkAppN (mkConst ``Proven.Ir.IndLow.lower) #[rk, sh, shO, pg, hs, bi, ain, a0, nb]
    | (f, _) => throwError s!"not indProgM: {f}"
  | _ => throwError "not callsCode1W"

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
def boolB (b : Bool) : List UInt8 := [if b then 1 else 0]
section
open Proven.Frontx.IndEx
/-- payloads: small, and some at and above `2^64` (the format keeps them mod `2^64`) -/
def payload (i : Nat) : Nat := match i % 7 with
  | 0 => rnd i 1 % 2 ^ 64 | 1 => 2 ^ 64 - 1 | 2 => 2 ^ 64 + 5 | _ => rnd i 2 % 1000
def genT : Nat → Nat → BinTree Nat
  | 0, _ => .leaf
  | d + 1, s => if rnd s d % 4 = 0 then .leaf else .branch (genT d (2 * s + 1)) (payload s) (genT d (2 * s + 2))
def trees : List (BinTree Nat) := [.leaf, .branch .leaf 7 .leaf] ++ (List.range 48).map fun i => genT (i % 6 + 1) (i + 3)
def genP : Nat → Pos | 0 => .one | n + 1 => .succ (genP n)
def poss : List Pos := (List.range 50).map fun i => genP (rnd i 5 % 60)
def lists : List (List Nat) := [[], [3], [2 ^ 64 - 1, 1]] ++ (List.range 47).map fun i =>
  (List.range (rnd i 9 % 25)).map fun j => payload (i * 31 + j)
def genL : Nat → Nat → ConLeche.Level
  | 0, s => if s % 2 = 0 then .zero else .param .anonymous
  | d + 1, s => match rnd s d % 8 with
    | 0 => .zero | 1 => .param .anonymous | 2 | 3 => .succ (genL d (s + 1))
    | 4 | 5 => .max (genL d (2 * s)) (genL d (2 * s + 1)) | _ => .imax (genL d (2 * s)) (genL d (2 * s + 1))
def levels : List ConLeche.Level := (List.range 50).map fun i => genL (i % 9) (i + 1)
def natB (n : Nat) : List UInt8 := leN 8 n
#eval do
  emitR "bt_count" (irprog% BinTree.count.code) false (trees.map fun t => (BTN.enc t, natB t.count))
  emitR "bt_mirror" (irprog% BinTree.mirror.code) true (trees.map fun t => (BTN.enc t, BTN.enc t.mirror))
  emitR "bt_graftleft" (irprog% BinTree.graftLeft.code) true
    ((List.range 50).map fun i => let p := (trees.getD i .leaf, trees.getD ((i * 7 + 3) % 50) .leaf); (BTN.enc2 p, BTN.enc (p.1.graftLeft p.2)))
  emitR "pos_tonat" (irprog% Pos.toNat.code) false (poss.map fun p => (PosT.enc p, natB p.toNat))
  emitR "pos_plus" (irprog% Pos.plus.code) true
    ((List.range 50).map fun i => let p := (poss.getD i .one, poss.getD ((i * 7 + 3) % 50) .one); (PosT.enc2 p, PosT.enc (p.1.plus p.2)))
  emitR "nontail_sum_ln" (irprog% NonTail.sum.code) false (lists.map fun l => (LN.enc l, natB (NonTail.sum l)))
  emitR "tail_sum_ln" (irprog% Tail.sum.code) false (lists.map fun l => (LN.enc l, natB (Tail.sum l)))
  emitR "tail_reverse_ln" (irprog% Tail.reverse.code) true (lists.map fun l => (LN.enc l, LN.enc (Tail.reverse l)))
  emitR "list_append_ln" (irprog% List.append.code) true
    ((List.range 50).map fun i => let p := (lists.getD i [], lists.getD ((i * 7 + 3) % 50) []); (LN.enc2 p, LN.enc (List.append p.1 p.2)))
  emitR "level_hasparam" (irprog% ConLeche.levelHasParam.code) false
    (levels.map fun l => (LevelT.enc l, boolB (ConLeche.levelHasParam l)))
  emitR "level_isneverzero" (irprog% ConLeche.Level.isNeverZero.code) false
    (levels.map fun l => (LevelT.enc l, boolB (ConLeche.Level.isNeverZero l)))
end
-- conditionals and comparisons (`IndCmpExamples.lean`, NOTES section 19): inputs in the subtype (every `Nat` field
-- below `2^64`); keys small (the key `5` is often present) and some near `2^64` (unsigned comparisons)
section
open Proven.Frontx.IndCmp
def key (i : Nat) : Nat := match i % 9 with
  | 0 => 2 ^ 64 - 1 - rnd i 4 % 3 | 1 => rnd i 1 % 2 ^ 63 + 2 ^ 63 | _ => rnd i 2 % 12
/-- binary search trees built by the book's own `insert` -/
def bsts : List (Tree Unit) := [.leaf, Tree.leaf.insert 5 ()] ++ (List.range 48).map fun i =>
  (List.range (rnd i 8 % 40)).foldl (fun t j => t.insert (key (i * 53 + j)) ()) .leaf
def keyLists : List (List Nat) := [[], [5], [2 ^ 64 - 1, 5, 5]] ++ (List.range 47).map fun i =>
  (List.range (rnd i 9 % 30)).map fun j => key (i * 31 + j)
#eval do
  emitR "tree_contains5" (irprog% contains5.code) false (bsts.map fun t => (TU.enc t, boolB (contains5 t)))
  emitR "tree_insert5" (irprog% insert5.code) true (bsts.map fun t => (TU.enc t, TU.enc (insert5 t)))
  emitR "list_elem5" (irprog% elem5.code) false (keyLists.map fun l => (LN.enc l, boolB (elem5 l)))
  emitR "list_erase5" (irprog% erase5.code) true (keyLists.map fun l => (LN.enc l, LN.enc (erase5 l)))
-- enumerations: every value (every pair), repeated to 50 cases
def days : List Weekday := [.monday, .tuesday, .wednesday, .thursday, .friday, .saturday, .sunday]
def ords : List Ordering := [.lt, .eq, .gt]
def cyc {α : Type} (xs : List α) : List α := (List.range 50).flatMap fun i => (xs.drop (i % xs.length)).take 1
#eval do
  emitR "weekday_isweekend_a" (irprog% A.Weekday.isWeekend.code) false
    ((cyc days).map fun d => (WD.enc d, boolB (A.Weekday.isWeekend d)))
  emitR "weekday_isweekend_b" (irprog% B.Weekday.isWeekend.code) false
    ((cyc days).map fun d => (WD.enc d, boolB (B.Weekday.isWeekend d)))
  emitR "ordering_swap" (irprog% Ordering.swap.code) true ((cyc ords).map fun o => (OrdT.enc o, OrdT.enc o.swap))
  emitR "ordering_then" (irprog% Ordering.then.code) true
    ((cyc (ords.flatMap fun a => ords.map fun b => (a, b))).map fun p => (OrdT.enc2 p, OrdT.enc (p.1.then p.2)))
  emitR "ordering_isle" (irprog% Ordering.isLE.code) false ((cyc ords).map fun o => (OrdT.enc o, boolB o.isLE))
  emitR "ordering_iseq" (irprog% Ordering.isEq.code) false ((cyc ords).map fun o => (OrdT.enc o, boolB o.isEq))
end
-- inductives, part 2 (`Ind2Examples.lean`, NOTES section 21): first line `indw <L>`, the work block per case: the
-- theorem's space with this input's cells (`Ind.spaceA m nl (fun _ => cells)`; the theorem's `cellsSup` is at
-- least that), or `Ind.spaceA 1 16 (fun n => M * n)` for one function
section
open Proven.Frontx.IndEx Proven.Frontx.IndCmp
def spW (m nl cells : Nat) (x : List UInt8) : Nat := Proven.Frontx.Ind.spaceA m nl (fun _ => cells) x.length
def possS : List Pos := (List.range 50).map fun i => genP (rnd i 5 % 40)
def posPairs : List (Pos × Pos) := (List.range 50).map fun i => (possS.getD i .one, possS.getD ((i * 7 + 3) % 50) .one)
/-- trees with payloads below `2^64` (the subtype of `eqBinTree`); every third pair equal, every third one payload apart -/
def genS : Nat → Nat → BinTree Nat
  | 0, _ => .leaf
  | d + 1, s => if rnd s d % 4 = 0 then .leaf else .branch (genS d (2 * s + 1)) (key s) (genS d (2 * s + 2))
/-- the payload of the rightmost node, plus one -/
def bump : BinTree Nat → BinTree Nat
  | .leaf => .leaf
  | .branch l x .leaf => .branch l ((x + 1) % 2 ^ 64) .leaf
  | .branch l x r => .branch l x (bump r)
def treePairs : List (BinTree Nat × BinTree Nat) := (List.range 50).map fun i =>
  let t := genS (i % 6 + 1) (i + 3)
  match i % 3 with | 0 => (t, t) | 1 => (t, genS (i % 5 + 1) (i + 11)) | _ => (t, bump t)
def keyTrees : List (Tree Unit × Nat) := (List.range 50).map fun i => (bsts.getD i .leaf, if i % 3 = 0 then 5 else key (i * 17 + 1))
def lvPairs : List (ConLeche.Level × ConLeche.Level) := (List.range 50).map fun i => (levels.getD i .zero, levels.getD ((i * 7 + 3) % 50) .zero)
def ordB (o : Ordering) : List UInt8 := OrdT.enc o
def smallT : BinTree Nat → Bool
  | .leaf => true | .branch l x r => decide (x < 2 ^ 64) && smallT l && smallT r
#eval do
  emitRW "pos_mul" (irprog% Pos.mul.code) true (posPairs.map fun p =>
    (PosT.enc2 p, PosT.enc (p.1.mul p.2), spW 2 16 (Pos.mul.ind.pg.al (PosT.emb p.1) 0 (PosT.emb p.2)) (PosT.enc2 p)))
  emitRW "nontail_reverse_ln" (irprog% NonTail.reverse.code) true (lists.map fun l =>
    (Proven.Frontx.IndEx.LN.enc l, Proven.Frontx.IndEx.LN.enc (NonTail.reverse l), spW 2 17 (NonTail.reverse.ind.pg.al (Proven.Frontx.IndEx.LN.emb l) 0 .z) (Proven.Frontx.IndEx.LN.enc l)))
  emitR "eq_bintree" (irprog% eqBinTree.code) false
    (treePairs.map fun p => (BTN.enc2 p, boolB (eqBinTree p.1 p.2)))
  emitR "pos_comp" (irprog% Pos.comp.code) true (posPairs.map fun p => (PosT.enc2 p, ordB (p.1.comp p.2)))
  emitRW "tree_containsk" (irprog% containsK.code) false (keyTrees.map fun (p : Tree Unit × Nat) =>
    let x := TU.enc p.1 ++ leN 8 p.2; (x, boolB (containsK p.1 p.2), Proven.Frontx.Ind.spaceA 1 16 (fun n => containsK.ind.pg.M * n) x.length))
  emitRW "tree_findk" (irprog% findK.code) true (keyTrees.map fun (p : Tree Unit × Nat) =>
    let x := TU.enc p.1 ++ leN 8 p.2; (x, OU.enc (findK p.1 p.2), Proven.Frontx.Ind.spaceA 1 16 (fun n => findK.ind.pg.M * n) x.length))
  emitR "level_combining" (irprog% ConLeche.Level.combining.code) true
    (lvPairs.map fun (p : ConLeche.Level × ConLeche.Level) => (LevelT.enc2 p, LevelT.enc (ConLeche.Level.combining p.1 p.2)))
  emitRW "level_simplify" (irprog% ConLeche.Level.simplify.code) true (levels.map fun l =>
    (LevelT.enc l, LevelT.enc l.simplify, spW 2 20 (ConLeche.Level.simplify.ind.pg.al (LevelT.emb l) 0 .z) (LevelT.enc l)))
end

namespace ExprG
open Proven Proven.Frontx.ExprEx
def strs : List String := ["", "a", "x", "Nat", "succ", "é", "λ", "∀x", "Nat.add", "a\x00b"]
def genN : Nat → Nat → ConLeche.Name
  | 0, _ => .anonymous
  | d + 1, s => match rnd s d % 3 with
    | 0 => .str (genN d (s + 1)) (strs.getD (rnd s 7 % strs.length) "")
    | 1 => .num (genN d (s + 2)) (match rnd s 3 % 4 with | 0 => 0 | 1 => 2 ^ 64 - 1 | 2 => 7 | _ => rnd s 9)
    | _ => .anonymous
def genL : Nat → Nat → ConLeche.Level
  | 0, s => if s % 2 = 0 then .zero else .param (genN (s % 3) s)
  | d + 1, s => match rnd s d % 6 with
    | 0 => .zero | 1 => .param (genN (s % 3) s) | 2 => .succ (genL d (s + 1))
    | 3 => .max (genL d (2 * s)) (genL d (2 * s + 1)) | 4 => .imax (genL d (2 * s)) (genL d (2 * s + 1))
    | _ => .succ .zero
def genLs (n s : Nat) : List ConLeche.Level := (List.range n).map fun j => genL (j % 3) (s + j)
/-- bound-variable indices near the binder depths (`0`, `1`, `2`, `3`) and large ones (`2^64 - 1`) -/
def idx (s : Nat) : Nat := match rnd s 5 % 7 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 2 ^ 64 - 1 | 5 => 5 | _ => rnd s 2 % 9
/-- expressions of depth at most `d`: every constructor, with names, level lists, literals -/
def genE : Nat → Nat → ConLeche.Expr
  | 0, s => match rnd s 0 % 6 with
    | 0 => .bvar (idx s) | 1 => .sort (genL 2 s) | 2 => .const (genN 2 s) (genLs (s % 3) s)
    | 3 => .lit (.natVal (idx (s + 1))) | 4 => .lit (.strVal (strs.getD (s % strs.length) ""))
    | _ => .bvar (s % 3)
  | d + 1, s => match rnd s d % 10 with
    | 0 => .bvar (idx s)
    | 1 => .fvar (idx (s + 3)) (genE d (s + 1))
    | 2 => .app (genE d (2 * s + 1)) (genE d (2 * s + 2))
    | 3 => .lam (genE d (2 * s + 1)) (genE d (2 * s + 2))
    | 4 => .forallE (genE d (2 * s + 1)) (genE d (2 * s + 2))
    | 5 => .letE (genE d (3 * s + 1)) (genE d (3 * s + 2)) (genE d (3 * s + 3))
    | 6 => .proj (genN 2 s) (idx s) (genE d (s + 5))
    | 7 => .const (genN 3 s) (genLs (s % 4) s)
    | 8 => .lit (.strVal (strs.getD (s % strs.length) ""))
    | _ => .app (genE d (2 * s + 3)) (.bvar (s % 4))
def exprs : List ConLeche.Expr := [.bvar 0, .bvar 1, .fvar 0 (.sort .zero), .lam (.sort .zero) (.bvar 0),
  .lam (.sort .zero) (.bvar 1), .letE (.bvar 0) (.bvar 1) (.bvar 2), .proj .anonymous 0 (.bvar 0)] ++
  (List.range 53).map fun i => genE (i % 6 + 1) (i + 1)
def exprPairs : List (ConLeche.Expr × ConLeche.Expr) := exprs.zip
  ((List.range exprs.length).map fun i => match i % 3 with
    | 0 => .fvar 7 (.sort .zero) | 1 => .const (genN 2 i) (genLs 2 i) | _ => genE (i % 3) (i + 9))

#eval do
  emitRW "expr_hasfvar" (irprog% ConLeche.Expr.hasFvar.code) false (exprs.map fun e =>
    (TExpr.enc e, boolB e.hasFvar, spW 1 16 (ConLeche.Expr.hasFvar.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitRW "expr_closed0" (irprog% closed0.code) false (exprs.map fun e =>
    (TExpr.enc e, boolB (closed0 e), spW 1 16 (closed0.ind.pg.al (TExpr.emb e) 0 .z) (TExpr.enc e)))
  emitRW "expr_inst1" (irprog% inst1.code) true (exprPairs.map fun p =>
    (TExpr.enc2 p, TExpr.enc (inst1 p.1 p.2), spW 1 19 (inst1.ind.pg.al (TExpr.emb p.1) 0 (TExpr.emb p.2)) (TExpr.enc2 p)))
/-- the words of the depth argument of `scopedD`: around the indices of `exprs` -/
def depths : List Nat := (List.range exprs.length).map fun i => match i % 5 with
  | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 ^ 64 - 1 | _ => rnd i 1 % 8
def w1 (e : ConLeche.Expr) (b : Bool) (pg : Nat) : List UInt8 × List UInt8 × Nat :=
  (TExpr.enc e, boolB b, spW 1 16 pg (TExpr.enc e))
def wN (e : ConLeche.Expr) (n : Nat) (pg : Nat) : List UInt8 × List UInt8 × Nat :=
  (TExpr.enc e, leN 8 n, spW 1 16 pg (TExpr.enc e))
def wT (e r : ConLeche.Expr) (pg : Nat) : List UInt8 × List UInt8 × Nat :=
  (TExpr.enc e, TExpr.enc r, spW 1 16 pg (TExpr.enc e))
#eval do
  emitRW "expr_sizef" (irprog% ConLeche.Expr.sizeF.code) false (exprs.map fun e =>
    wN e e.sizeF (ConLeche.Expr.sizeF.ind.pg.al (TExpr.emb e) 0 .z))
  emitRW "expr_scopedd" (irprog% scopedD.code) false ((exprs.zip depths).map fun (e, d) =>
    let x := TExpr.enc e ++ leN 8 d
    (x, boolB (scopedD e d), Proven.Frontx.Ind.spaceA 1 16 (fun _ => scopedD.ind.pg.al (TExpr.emb e) (BitVec.ofNat 64 d) .z) x.length))
  emitRW "expr_isforalle" (irprog% ConLeche.Expr.isForallE.code) false (exprs.map fun e =>
    w1 e e.isForallE (ConLeche.Expr.isForallE.ind.pg.al (TExpr.emb e) 0 .z))
  emitRW "expr_getappfn" (irprog% ConLeche.Expr.getAppFn.code) true (exprs.map fun e =>
    wT e e.getAppFn (ConLeche.Expr.getAppFn.ind.pg.al (TExpr.emb e) 0 .z))
  emitRW "expr_piresult" (irprog% ConLeche.Expr.piResult.code) true (exprs.map fun e =>
    wT e e.piResult (ConLeche.Expr.piResult.ind.pg.al (TExpr.emb e) 0 .z))
  emitRW "expr_fvartyped" (irprog% ConLeche.Expr.fvarTypeD.code) true (exprs.map fun e =>
    wT e e.fvarTypeD (ConLeche.Expr.fvarTypeD.ind.pg.al (TExpr.emb e) 0 .z))
  emitRW "expr_numargs" (irprog% ConLeche.Expr.numArgs.code) false (exprs.map fun e =>
    wN e e.numArgs (ConLeche.Expr.numArgs.ind.pg.al (TExpr.emb e) 0 .z))
  emitRW "expr_islit" (irprog% ConLeche.Expr.isLit.code) false (exprs.map fun e =>
    w1 e e.isLit (ConLeche.Expr.isLit.ind.pg.al (TExpr.emb e) 0 .z))
#eval! (exprs.length, (exprs.map ConLeche.Expr.hasFvar).count true, (exprs.map closed0).count true,
  (exprPairs.map fun p => TExpr.enc (inst1 p.1 p.2) == TExpr.enc p.1).count true)

end ExprG
