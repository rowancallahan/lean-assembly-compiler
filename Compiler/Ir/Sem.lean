/- Small-step semantics of the IR (`Testing/notes/IR_DESIGN.md` §2.2, §2.3): `step` is a function (so `#eval` runs
RTL / LTL / Lin programs), `run` runs it with fuel, `run_det` says every terminating run has one result.

Memory is address-free and unbounded: the input and output byte blocks, and one flat list of 8-byte cells carved
into blocks by a block table (an access outside its block is stuck).  `alloc` always succeeds and records
`MemEvent.alloc n`; `free` records `MemEvent.free n` and kills the block; a call records its frame
(`alloc (slots + 1)`) and its return `free (slots + 1)`.  Fresh cells are uninitialised (reading one is stuck);
registers start at `.w 0`.  The output block grows on write; a run's output is defined when every byte of the
written prefix was written.

Pure Lean (core only). -/
import Compiler.Ir.Syntax
import Compiler.AllocSpec

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

/-- memory: input bytes, the written prefix of the output, the cells, the block table -/
structure Mem where
  inp : List UInt8
  out : List (Option UInt8)
  cells : List (Option Val)
  /-- cell block `k + 2`: first cell, size, live -/
  blks : List (Nat × Nat × Bool)

def Mem.init (input : List UInt8) : Mem := ⟨input, [], [], []⟩

/-- a live cell block: its first cell and size -/
def Mem.blk (m : Mem) : Nat → Option (Nat × Nat)
  | 0 | 1 => none
  | k + 2 => match m.blks[k]? with
    | some (st, sz, true) => some (st, sz)
    | _ => none

/-- write byte `i` of the output (growing it) -/
def setOut (out : List (Option UInt8)) (i : Nat) (v : UInt8) : List (Option UInt8) :=
  if i < out.length then out.set i (some v) else out ++ List.replicate (i - out.length) none ++ [some v]

/-- the output bytes: defined when every byte of the written prefix was written -/
def Mem.output (m : Mem) : Option (List UInt8) := m.out.mapM id

section
variable {ρ : Type} [DecidableEq ρ]

def upd (g : ρ → Val) (x : ρ) (v : Val) : ρ → Val := fun y => if y = x then v else g y

/-- assign in order (the last of equal locations wins) -/
def setMany (g : ρ → Val) : List ρ → List Val → ρ → Val
  | x :: xs, v :: vs => setMany (upd g x v) xs vs
  | _, _ => g

def Arg.eval (g : ρ → Val) : Arg ρ → Val
  | .r x => g x
  | .i c => .w c

def Arg.word (g : ρ → Val) (a : Arg ρ) : Option (BitVec 64) :=
  match a.eval g with
  | .w x => some x
  | .p _ _ => none

def Rhs.eval (m : Mem) (g : ρ → Val) : Rhs ρ → Option Val
  | .arg a => some (a.eval g)
  | .op o a b => match a.word g, b.word g with
    | some x, some y => some (.w (o.eval x y))
    | _, _ => none
  | .mop mo a b => match a.word g, b.word g with
    | some x, some y => some (.w (mo.eval x y))
    | _, _ => none
  | .padd p i => match g p, i.word g with
    | .p b o, some k => match m.blk b with
      | some (_, sz) => if o + k.toNat ≤ sz then some (.p b (o + k.toNat)) else none
      | none => none
    | _, _ => none

/-- a pointer is not zero; other comparisons with pointers are stuck -/
def nullTest (c : Cond) : Option Bool :=
  match c with
  | .eq => some false
  | .ne => some true
  | _ => none

def Tst.eval (g : ρ → Val) (t : Tst ρ) : Option Bool :=
  match t.a.eval g, t.b.eval g with
  | .w x, .w y => some (t.c.eval x y)
  | .p _ _, .w y => if y = 0 then nullTest t.c else none
  | .w x, .p _ _ => if x = 0 then nullTest t.c else none
  | .p _ _, .p _ _ => none

/-- one instruction other than `call`: new registers, memory, events (newest first) -/
def Inst.exec (m : Mem) (g : ρ → Val) : Inst ρ → Option ((ρ → Val) × Mem × List MemEvent)
  | .let_ d e => match e.eval m g with
    | some v => some (upd g d v, m, [])
    | none => none
  | .ldb d p i => match i.word g, g p with
    | some k, .p 0 0 => match m.inp[k.toNat]? with
      | some b => some (upd g d (.w (b.toBitVec.setWidth 64)), m, [])
      | none => none
    | some k, .p 1 0 => match m.out[k.toNat]? with
      | some (some b) => some (upd g d (.w (b.toBitVec.setWidth 64)), m, [])
      | _ => none
    | _, _ => none
  | .stb v p i => match v.word g, i.word g, g p with
    | some x, some k, .p 1 0 => some (g, { m with out := setOut m.out k.toNat (UInt8.ofBitVec (x.setWidth 8)) }, [])
    | _, _, _ => none
  | .ld d p k => match g p with
    | .p b o => match m.blk b with
      | some (c0, sz) => if o + k < sz then
          (match m.cells[c0 + o + k]? with
           | some (some v) => some (upd g d v, m, [])
           | _ => none)
        else none
      | none => none
    | .w _ => none
  | .st v p k => match g p with
    | .p b o => match m.blk b with
      | some (c0, sz) => if o + k < sz then
          some (g, { m with cells := m.cells.set (c0 + o + k) (some (v.eval g)) }, [])
        else none
      | none => none
    | .w _ => none
  | .alloc d n => match n.word g with
    | some c => some (upd g d (.p (m.blks.length + 2) 0),
        { m with cells := m.cells ++ List.replicate c.toNat none, blks := m.blks ++ [(m.cells.length, c.toNat, true)] },
        [.alloc c.toNat])
    | none => none
  | .free p => match g p with
    | .p (k + 2) 0 => match m.blk (k + 2) with
      | some (c0, sz) => some (g, { m with blks := m.blks.set k (c0, sz, false) }, [.free sz])
      | none => none
    | _ => none
  | .call _ _ _ => none

end

/-- an activation: function, block, instruction index, registers, where the caller wants the results -/
structure Frame (ρ : Type) where
  f : FId
  l : Lbl
  pc : Nat
  regs : ρ → Val
  dst : List ρ

structure State (ρ : Type) where
  stack : List (Frame ρ)
  mem : Mem
  /-- memory events, newest first -/
  ev : List MemEvent

/-- the end of a run: returned values, memory, events -/
structure Result where
  vs : List Val
  mem : Mem
  ev : List MemEvent

inductive Outcome (ρ : Type) where
  | next (s : State ρ)
  | done (r : Result)
  | stuck

section
variable {ρ : Type} [DecidableEq ρ]

/-- enter block `l` of `F` with the arguments `vs` -/
def jump (F : Func ρ) (fr : Frame ρ) (l : Lbl) (vs : List Val) : Option (Frame ρ) :=
  match F.blocks.lookup l with
  | some B => if vs.length = B.params.length then some { fr with l := l, pc := 0, regs := setMany fr.regs B.params vs }
      else none
  | none => none

def termStep (F : Func ρ) (fr : Frame ρ) (rest : List (Frame ρ)) (m : Mem) (ev : List MemEvent) :
    Term ρ → Outcome ρ
  | .jmp l as => match jump F fr l (as.map (Arg.eval fr.regs)) with
    | some fr' => .next ⟨fr' :: rest, m, ev⟩
    | none => .stuck
  | .br t l₁ a₁ l₂ a₂ => match t.eval fr.regs with
    | some true => match jump F fr l₁ (a₁.map (Arg.eval fr.regs)) with
      | some fr' => .next ⟨fr' :: rest, m, ev⟩
      | none => .stuck
    | some false => match jump F fr l₂ (a₂.map (Arg.eval fr.regs)) with
      | some fr' => .next ⟨fr' :: rest, m, ev⟩
      | none => .stuck
    | none => .stuck
  | .switch x ls d => match fr.regs x with
    | .w k => match jump F fr (ls[k.toNat]?.getD d) [] with
      | some fr' => .next ⟨fr' :: rest, m, ev⟩
      | none => .stuck
    | .p _ _ => .stuck
  | .ret vs => match rest with
    | [] => .done ⟨vs.map (Arg.eval fr.regs), m, ev⟩
    | c :: rest' => if vs.length = c.dst.length then
        .next ⟨{ c with regs := setMany c.regs c.dst (vs.map (Arg.eval fr.regs)) } :: rest', m,
          .free (F.slots + 1) :: ev⟩
      else .stuck

/-- **one step** -/
def step (P : Prog ρ) (s : State ρ) : Outcome ρ :=
  match s.stack with
  | [] => .stuck
  | fr :: rest => match P.funcs[fr.f]? with
    | none => .stuck
    | some F => match F.blocks.lookup fr.l with
      | none => .stuck
      | some B => match B.body[fr.pc]? with
        | some (.call ds g as) => match P.funcs[g]? with
          | some G => if as.length = G.params.length then
              .next ⟨⟨g, G.entry, 0, setMany (fun _ => .w 0) G.params (as.map (Arg.eval fr.regs)), ds⟩ ::
                { fr with pc := fr.pc + 1 } :: rest, s.mem, .alloc (G.slots + 1) :: s.ev⟩
            else .stuck
          | none => .stuck
        | some i => match i.exec s.mem fr.regs with
          | some (g', m', e) => .next ⟨{ fr with pc := fr.pc + 1, regs := g' } :: rest, m', e ++ s.ev⟩
          | none => .stuck
        | none => termStep F fr rest s.mem s.ev B.term

/-- **runs with fuel** -/
def run (P : Prog ρ) : Nat → State ρ → Option Result
  | 0, _ => none
  | n + 1, s => match step P s with
    | .next s' => run P n s'
    | .done r => some r
    | .stuck => none

/-- the start: `main` with its parameters `(input, input length, output)` -/
def init (P : Prog ρ) (input : List UInt8) : State ρ :=
  match P.funcs[P.main]? with
  | some F => ⟨[⟨P.main, F.entry, 0,
      setMany (fun _ => .w 0) F.params [.p 0 0, .w (BitVec.ofNat 64 input.length), .p 1 0], []⟩],
      Mem.init input, []⟩
  | none => ⟨[], Mem.init input, []⟩

def Runs (P : Prog ρ) (s : State ρ) (r : Result) : Prop := ∃ n, run P n s = some r

theorem run_succ (P : Prog ρ) (n : Nat) (s : State ρ) : run P (n + 1) s =
    match step P s with
    | .next s' => run P n s'
    | .done r => some r
    | .stuck => none := rfl

theorem run_mono {P : Prog ρ} : ∀ {n : Nat} {s : State ρ} {r : Result}, run P n s = some r →
    ∀ k, run P (n + k) s = some r
  | 0, _, _, h, _ => nomatch h
  | n + 1, s, r, h, k => by
    rw [show n + 1 + k = (n + k) + 1 by omega, run_succ]
    rw [run_succ] at h
    split at h
    · exact run_mono h k
    · exact h
    · exact nomatch h

/-- **determinism**: two terminating runs have the same result -/
theorem run_det {P : Prog ρ} {n n' : Nat} {s : State ρ} {r r' : Result} (h : run P n s = some r)
    (h' : run P n' s = some r') : r = r' := by
  have a := run_mono h n'
  have b := run_mono h' n
  rw [Nat.add_comm] at b
  rw [a] at b
  exact Option.some.inj b

theorem Runs.det {P : Prog ρ} {s : State ρ} {r r' : Result} (h : Runs P s r) (h' : Runs P s r') : r = r' :=
  let ⟨_, a⟩ := h; let ⟨_, b⟩ := h'; run_det a b

/-- the first step of a run -/
theorem run_next {P : Prog ρ} {n : Nat} {s s' : State ρ} {r : Result} (hs : step P s = .next s')
    (h : run P n s = some r) : ∃ m, n = m + 1 ∧ run P m s' = some r := by
  cases n with
  | zero => exact nomatch h
  | succ m => rw [run_succ, hs] at h; exact ⟨m, rfl, h⟩

end

/-! ## The meaning of a program -/

/-- the result of the run from the input, if it terminates -/
noncomputable def Prog.result (P : Prog VReg) (input : List UInt8) : Option Result :=
  open Classical in if h : ∃ r, Runs P (init P input) r then some (Classical.choose h) else none

theorem Prog.result_eq {P : Prog VReg} {input : List UInt8} {r : Result} (h : Runs P (init P input) r) :
    P.result input = some r := by
  unfold Prog.result
  rw [dif_pos ⟨r, h⟩]
  exact congrArg some (Runs.det (Classical.choose_spec ⟨r, h⟩) h)

theorem Prog.result_some {P : Prog VReg} {input : List UInt8} {r : Result} (h : P.result input = some r) :
    Runs P (init P input) r := by
  unfold Prog.result at h
  split at h
  · next hx => rw [← Option.some.inj h]; exact Classical.choose_spec hx
  · exact nomatch h

/-- **the meaning**: the output bytes of the run from the input -/
noncomputable def Prog.meaning (P : Prog VReg) (input : List UInt8) : Option (List UInt8) :=
  (P.result input).bind fun r => r.mem.output

noncomputable instance : Proven.Top.Program (Prog VReg) := ⟨Prog.meaning⟩

/-- an interpreter for tests: the output and the events (`none`: stuck or out of fuel) -/
def interp (P : Prog VReg) (fuel : Nat) (input : List UInt8) : Option (List UInt8 × List MemEvent) :=
  match run P fuel (init P input) with
  | some r => r.mem.output.map fun o => (o, r.ev)
  | none => none

end Proven.Ir
