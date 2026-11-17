/- Tests of nano's S3 back end (`Nano/S3*.lean`, `Testing/notes/NANO_S3.md`), driven by `Testing/asm/nano_s3_test.py`.
Programs: the sources listed in `Testing/asm/ir-words/nano_s3_list.txt` (written by the driver: corpus, Int64 corpus,
edge sources, random sources; each through `nanoElabT`) and random `Ex` trees (as in `emit_nano.lean`: lets, calls,
out-of-range variables, large frames).  Per program and input, every link of the chain is checked on the Lean side:
L1 `(tr1P p).eval = p.eval`, L2 `(tr2P (tr1P p)).eval = p.eval`, L3 (a test evaluator of S3 expressions on
`tr3 (idVars n)`) = `p.eval`, L4 (the test evaluator on `main` of `nanoToS3 p`, bytes in, bytes out) = `nanoRun p`,
and the IR interpreter of `lowerP (nanoToS3 p)` = `nanoRun p`.  Then the words (`Ir.compile`) and cases (input, result,
`memoryNeeded`) go to `Testing/asm/ir-words/nano_s3_<i>.{words,cases}` for QEMU / Sail. Exits 1 on any mismatch. -/
import Nano.S3Top
import Nano.Elab
import Riscv.Back.IrTarget
import Compiler.Ir.Lin
open Proven (leN)
open Proven.Ir Proven.Mach.Riscv Proven.Top.Alloc Nano Nano.S3
open Proven.S3 (V Var Vars Expr Ty Sig bytesV bytesOut lowerP)

def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j + 12345) % 2^64

/-! ## a test evaluator of S3 expressions (no calls) -/
partial def evS {S : Sig} : {Γ : List Ty} → {τ : Ty} → Expr S Γ τ → List V → Option V
  | _, _, .var x, env => env[x.idx]?
  | _, _, .lit c, _ => some (.w c)
  | _, _, .blit c, _ => some (.w (Proven.S3.bv c))
  | _, _, .bin o a b, env => match env[a.idx]?, env[b.idx]? with
    | some (.w x), some (.w y) => some (.w (o.eval x y))
    | _, _ => none
  | _, _, .cmp c a b, env => match env[a.idx]?, env[b.idx]? with
    | some (.w x), some (.w y) => some (.w (Proven.S3.bv (c.eval x y)))
    | _, _ => none
  | _, _, .bnot a, env => match env[a.idx]? with
    | some (.w x) => some (.w (x ^^^ 1))
    | _ => none
  | _, _, .let_ e₁ e₂, env => (evS e₁ env).bind fun v => evS e₂ (v :: env)
  | _, _, .ite c e₁ e₂, env => match env[c.idx]? with
    | some (.w x) => if x ≠ 0 then evS e₁ env else evS e₂ env
    | _ => none
  | _, _, .mk _ j xs, env => (xs.get env).map (.c j)
  | _, _, @Expr.cas _ _ _ i x arms, env => match env[x.idx]? with
    | some (.c j fs) => if h : j < S.nc i then evS (arms ⟨j, h⟩) (fs ++ env) else none
    | _ => none
  | _, _, .call _ _ _, _ => none

/-! ## random nano programs (as `emit_nano.lean`) -/
def word (s : Nat) : UInt64 := match s % 6 with
  | 0 => UInt64.ofNat (rnd s 1) | 1 => 0xFFFFFFFFFFFFFFFF | 2 => 0 | 3 => 0x8000000000000000
  | _ => UInt64.ofNat (rnd s 2 % 1000)

def mkArgs : List Ex → Ex
  | [] => .anil
  | e :: es => .acons e (mkArgs es)

def rgenE : Nat → Nat → Nat → Ex
  | 0, nv, s => if nv > 0 && rnd s 3 % 3 != 0 then .var (rnd s 4 % (nv + 1)) else .num (word s)
  | d + 1, nv, s => match rnd s d % 9 with
    | 0 => .num (word s)
    | 1 => .var (rnd s 5 % (nv + 1))
    | 2 => .add (rgenE d nv (2 * s + 1)) (rgenE d nv (2 * s + 2))
    | 3 => .sub (rgenE d nv (2 * s + 1)) (rgenE d nv (2 * s + 2))
    | 4 => .mul (rgenE d nv (2 * s + 1)) (rgenE d nv (2 * s + 2))
    | 5 | 6 => .let_ (rgenE d nv (2 * s + 1)) (rgenE d (nv + 1) (2 * s + 2))
    | _ =>
      let k := rnd s 6 % 3
      .call (rgenE d k (3 * s + 5)) (mkArgs ((List.range k).map fun j => rgenE d nv (3 * s + 7 + 11 * j)))

def rgenBig : Nat → Nat → Nat → Ex
  | 0, nv, s => if nv > 0 then .var (rnd s 4 % nv) else .num (word s)
  | d + 1, nv, s => match rnd s d % 5 with
    | 0 => .add (rgenBig d nv (2 * s + 1)) (rgenBig d nv (2 * s + 2))
    | 1 => .sub (rgenBig d nv (2 * s + 1)) (rgenBig d nv (2 * s + 2))
    | 2 => .mul (rgenBig d nv (2 * s + 1)) (rgenBig d nv (2 * s + 2))
    | 3 => .let_ (rgenBig d nv (2 * s + 1)) (rgenBig d (nv + 1) (2 * s + 2))
    | _ => .call (rgenBig d 2 (2 * s + 1)) (mkArgs [rgenBig d nv (2 * s + 2), .num (word s)])

def randProgs : List Prog :=
  (List.range 6).map (fun i => (i % 5, rgenBig (i + 5) (i % 4) (i * 13 + 3))) ++
  (List.range 40).map fun i => (i % 5, rgenE (i % 7 + 1) (i % 4) (i * 7 + 1))

def randInputs (p : Prog) (i : Nat) : List (List UInt64) :=
  (List.range 8).map fun j => (List.range p.1).map fun a => word (rnd i (j * 5 + a))

/-! ## IR -/
def compileT (P : Proven.Ir.Prog VReg) : Option (List (BitVec 32) × Proven.Ir.Prog Nat) :=
  match alloc P with
  | some Q => (rvT.lin Q).map fun c => (rvT.words c, Q)
  | none => none

def mainSlots (Q : Proven.Ir.Prog Nat) : Nat := ((Q.funcs[Q.main]?).map (·.slots)).getD 0

def peakF (E : List MemEvent) : Nat :=
  (E.reverse.foldl (fun (c, m) e => match e with
    | .alloc n => (c + n, max m (c + n)) | .free n => (c - n, max m (c - n))) (0, 0)).2

/-! ## per program -/
def encWs' (args : List UInt64) : List UInt8 := (args.map fun a => leN 8 a.toNat).flatten

/-- (mismatches, cases) -/
def emitP (name : String) (p : Prog) (ins : List (List UInt64)) : IO (Nat × Nat) := do
  let P := nanoToS3 p
  let Q := lowerP P
  let mut bad := 0
  let mut s := ""
  let some (ws, Qn) := compileT Q | IO.println s!"{name}: COMPILE FAILED"; return (1, 0)
  unless Proven.Top.wordBytes ws == (((compileW Q).map fun (w, _) => Proven.Top.wordBytes w).getD []) do
    IO.println s!"{name}: words != compileW (the code of Ir.compile)"; bad := bad + 1
  for args in ins do
    let r0 := p.eval args
    let x := encWs' args
    let y := nanoRun p x
    let ok1 := (tr1P p).eval args == r0
    let ok2 := (tr2P (tr1P p)).eval args == r0
    let r3 := evS (tr3 (S := S0) (idVars p.1) (tr2 (tr1 p.2))) (args.reverse.map fun w => V.w w.toBitVec)
    let ok3 := match r3, r0 with
      | some (.w v), some v0 => v == v0.toBitVec
      | _, _ => false
    let ok4 := ((evS (P.body P.main) [bytesV x]).bind bytesOut) == y
    match y, interp Q 100000000 x with
    | some yv, some (o, ev) =>
      let okI := o == yv
      unless ok1 && ok2 && ok3 && ok4 && okI do
        IO.println s!"{name}: MISMATCH on {hx x}: L1 {ok1} L2 {ok2} L3 {ok3} L4 {ok4} IR {okI}"
        bad := bad + 1
      s := s ++ s!"{hx x} {hx yv} {8 * peakF (ev ++ [.alloc (mainSlots Qn + 3)])}\n"
    | _, _ => IO.println s!"{name}: no result on {hx x}"; bad := bad + 1
  IO.FS.writeFile s!"Testing/asm/ir-words/{name}.words" (String.intercalate "\n" (s!"{name} 0" :: ws.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/ir-words/{name}.cases" s
  return (bad, ins.length)

def parseIns (fs : List String) : List (List UInt64) :=
  fs.map fun f => if f == "-" then [] else (f.splitOn ",").map fun w => UInt64.ofNat w.toNat!

def runMain : IO UInt32 := do
  let mut names : Array String := #[]
  let mut bad := 0
  let mut cases := 0
  let mut rejected := 0
  let mut k := 0
  let lines := (← IO.FS.readFile "Testing/asm/ir-words/nano_s3_list.txt").splitOn "\n" |>.filter (· ≠ "")
  for l in lines do
    match l.splitOn " " with
    | path :: fs =>
      let src ← IO.FS.readBinFile path
      match nanoElabT src.toList with
      | some (_, p) =>
        let name := s!"nano_s3_{k}"
        let (b, c) ← emitP name p (parseIns fs)
        bad := bad + b; cases := cases + c; names := names.push name; k := k + 1
      | none => rejected := rejected + 1
    | [] => pure ()
  for (p, i) in randProgs.zipIdx do
    let name := s!"nano_s3_{k}"
    let (b, c) ← emitP name p (randInputs p i)
    bad := bad + b; cases := cases + c; names := names.push name; k := k + 1
  IO.FS.writeFile "Testing/asm/ir-words/nano_s3_names.txt" (String.intercalate "\n" names.toList ++ "\n")
  IO.println s!"nano-s3 links: {names.size} programs ({rejected} sources rejected by nanoElabT), {cases} cases, mismatches {bad}"
  return if bad == 0 then 0 else 1

#eval do let r ← runMain; if r != 0 then throw (IO.userError "nano-s3 link test FAILED")
