/- Self-run of `Nano.SelfHost.binary` (the binary of `Nano.selfHosted`, Nano/SelfHostFinal.lean) and per-stage run of
lexA. `binary` is noncomputable (`S3.words`); `binaryC` below is a computable definition and `binaryC_eq` PROVES
`binary = binaryC` from the stage files' kernel-checked literals (`words_eq'`: allocation `*_hQ`, layout fixpoint
`*_hL`/`*_fix`, `2 ≤ rounds`). Writes, under Testing/asm/ir-words/:
* nano_self.words / .cases: the words of `binaryC`; per source: input, expected = code of `nanoCompileA (nanoElab src)`,
  K0 = max(intermediate lengths, lexA's memoryNeeded, the expM/asm spaces), domain flag, name, and the intermediate
  results `stage2a (lexB src)`, `serU u`, `inlB (serU u)` (inputs/outputs of the 2b and inliner stages);
* nano_lexA.words / .cases: lexA's words (the first component of `binaryC`), input, `stage2a (lexB src)`, memoryNeeded;
* nano_s2b.words, nano_sinl.words: the 2b and inliner components of `binaryC` (memoryNeeded of these two is found on
  QEMU by the driver: the interpreted IR interpreter takes minutes per KB of input).
Driver: Testing/nano/selfrun/selfrun_test.py. The Fast interpreter below is copied from Testing/nano/emit_ps3_p2.lean. -/
import Riscv.Back.IrTarget
import Compiler.Ir.Lin
import Nano.SelfHostFinal
import Riscv.Back.S3Top
open Proven.Ir Proven.Mach.Riscv Proven.Top.Alloc
open Proven.S3

def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64

def compileT (P : Prog VReg) : Option (List (BitVec 32) × Prog Nat) :=
  match alloc P with
  | some Q => (rvT.emitP Q (rvT.layout Q 3 ⟨[], [], 0⟩)).map fun c => (rvT.words c, Q)  -- the layout is at its fixpoint after 2 rounds (Nano/ParseS3BStage.lean)
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

open Nano Nano.U Nano.Link Nano.SelfHost Nano.S3Stage

def wLex : List (BitVec 32) := ((rvT.emitP Nano.LS.lexA_Q Nano.LS.lexA_L2).map rvT.words).getD []
def w2b : List (BitVec 32) := ((rvT.emitP Nano.PS.stage2B_Q Nano.PS.stage2B_L2).map rvT.words).getD []
def wInl : List (BitVec 32) := ((rvT.emitP Nano.IS.inlS3_Q Nano.IS.inlS3_L2).map rvT.words).getD []
/-- the linked binary, computable -/
def binaryC : List (BitVec 32) := link (link (link (link wLex w2b) wInl) Nano.Self.nanoExpM.code) Nano.Self.nanoAsm.code

/-- **the words tested are the words of the theorem** -/
theorem binaryC_eq : binary = binaryC := by
  unfold binary binaryC wLex w2b wInl
  rw [words_eq' 2 Nano.LS.lexA_hQ Nano.LS.lexA_hm Nano.LS.lexA_hL Nano.LS.lexA_fix,
    words_eq' 2 Nano.PS.stage2B_hQ Nano.PS.stage2B_hm Nano.PS.stage2B_hL Nano.PS.stage2B_fix,
    words_eq' 2 Nano.IS.inlS3_hQ Nano.IS.inlS3_hm Nano.IS.inlS3_hL Nano.IS.inlS3_fix]

#print axioms binaryC_eq
#print axioms Nano.selfHosted

/-- memoryNeeded of an S3 stage on one input (the Fast interpreter), and its output -/
def need (Q : Proven.Ir.Prog Nat) (x : List UInt8) : List UInt8 × Nat :=
  match Fast.interp Q 1000000000 x with
  | some (o, ev) => (o, 8 * peakF (ev ++ [.alloc (mainSlots Q + 3)]))
  | none => panic! "stage interpreter failed"

def logL (m : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "Testing/nano/selfrun/emit.log" .append
  h.putStrLn m; h.flush

#eval show IO Unit from do
  let dir : System.FilePath := (← IO.getEnv "NANO_DIR").get!
  let files := (← dir.readDir).map (·.path) |>.toList
  let files := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  assert! wLex.length > 0 && w2b.length > 0 && wInl.length > 0
  IO.FS.writeFile "Testing/asm/ir-words/nano_self.words" (String.intercalate "\n" ("nano_self 1" :: binaryC.map hex8) ++ "\n")
  IO.FS.writeFile "Testing/asm/ir-words/nano_lexA.words" (String.intercalate "\n" ("nano_lexA 1" :: wLex.map hex8) ++ "\n")
  IO.FS.writeFile "Testing/asm/ir-words/nano_s2b.words" (String.intercalate "\n" ("nano_s2b 1" :: w2b.map hex8) ++ "\n")
  IO.FS.writeFile "Testing/asm/ir-words/nano_sinl.words" (String.intercalate "\n" ("nano_sinl 1" :: wInl.map hex8) ++ "\n")
  IO.println s!"binaryC: {binaryC.length} words (lexA {wLex.length}, 2b {w2b.length}, inl {wInl.length}, expM {Nano.Self.nanoExpM.code.length}, asm {Nano.Self.nanoAsm.code.length})"
  let sm := 8 * (Nano.Self.nanoExpM.slots + 1) + 7
  let sa := 8 * (Nano.Self.nanoAsm.slots + 1) + 7
  let mut sS := ""
  let mut sL := ""
  let mut nIn := 0
  let mut nOut := 0
  for f in files do
    let src := (← IO.FS.readBinFile f).toList
    let t0 ← IO.monoMsNow
    -- lexA alone: every input
    let a := Nano.PS.stage2a (Nano.B.lexB src)
    let (oA, mA) := need Nano.LS.lexA_Q src
    assert! oA == a
    sL := sL ++ s!"{hx src} {hx a} {mA}\n"
    logL s!"{f.fileName.get!} {src.length} B: lexA {(← IO.monoMsNow) - t0} ms"
    match nanoElabU src, nanoElab src with
    | some u, some p =>
      match nanoCompileA p with
      | some c =>
        let s2 := serU u
        let i := inlB s2
        let e := mexp i
        assert! asm e == c.code
        logL s!"  spec chain {(← IO.monoMsNow) - t0} ms ({a.length}, {s2.length}, {i.length}, {e.length}, code {c.code.length} B)"
        let lens := [a.length, s2.length, i.length, e.length]
        let K := (lens ++ [mA, sm, sa]).foldl max 0
        let dom := u.all (·.1 < 256) && u.length ≤ 65536 && lens.all (· ≤ 2 ^ 20) &&
          nest p.2 ≤ 400 && chain p.2 ≤ 2500
        if dom then nIn := nIn + 1 else nOut := nOut + 1
        logL s!"  all stages {(← IO.monoMsNow) - t0} ms"
        sS := sS ++ s!"{hx src} {hx c.code} {K} {if dom then 1 else 0} {f.fileName.get!} {hx a} {hx s2} {hx i}\n"
      | none => nOut := nOut + 1
    | _, _ => nOut := nOut + 1
  IO.FS.writeFile "Testing/asm/ir-words/nano_self.cases" sS
  IO.FS.writeFile "Testing/asm/ir-words/nano_lexA.cases" sL
  IO.println s!"sources {files.length}: in Domain {nIn}, outside (elab/nanoCompileA rejects or bounds) {nOut}"
