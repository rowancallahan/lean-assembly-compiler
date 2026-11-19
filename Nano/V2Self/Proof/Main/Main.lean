/- Nano/V2Self/Proof/Main/Main: the END-TO-END statement for C's driver `m x = g41 x (o41 (y16 (s10 x)))` (build_self_S.py).
(1) `Sem`: the meaning of ParSpec's resolved program (`List DefA`) on an input, word level, with buffer capacity κ;
(2) `ImplementsC`: bytes `B` loaded as RV64 code (Sail, `Spec/Implements1.lean` conventions) implement `f`, where the run
    may also end in out-of-memory, but only below a per-input work size `space x`;
(3) the stage hypotheses `ParStage` (parser, = `ParInv.ParserSound`), `OwnStage` (O's ownership stage o41 accepts only
    `LinearK` programs) and `GenStage` (codegen + machine bridge, for linear programs); the lexer is proved
    (`LexSpec.s10_sound`);
(4) `compiler_correct`: m x ≠ [] → ∃ ts p, Lexes x ts ∧ ParsesProgram ts p ∧ LinearK p ∧ ImplementsC (m x) (Sem κ p).
Notes: Testing/notes/NANO_V2_MAIN.md. -/
import Nano.V2Self.Proof.Lex.Lex2Sound
import Nano.V2Self.C.Par1
import Nano.V2Self.C.Gen
import Nano.V2Self.C.Own
import Nano.V2Self.Proof.Own.OwnSpec
import Nano.V2Self.Proof.Parser.ParInv
import Nano.V2Self.Proof.Lex.MainTokWF
import Nano.V2Self.Proof.Parser.ParSerLen
import Spec.Implements1

namespace NanoMain
open ParSpec

/-- C's driver, verbatim from `Testing/nano/v2self/build_self_S.py` (not in `C/Main.lean`, which holds the old chain) -/
def mC (x : List UInt8) : List UInt8 := C.g41 x (C.o41 (C.y16 (C.s10 x)))

/-! ## the meaning of a resolved program -/

/-- a slot value: a word, or a buffer (`Buf`, and `List UInt8` other than the input, as words; `put` pushes the word,
the final output keeps the low byte, like Lean's `put` = push `b.toUInt8`) -/
inductive W | w (x : UInt64) | b (l : List UInt64)
  deriving DecidableEq, Repr

/-- why evaluation stopped: a buffer reached its capacity κ (the machine reports −2), or the AST is ill-formed
(never for a parsed program; see `NANO_V2_MAIN.md`) -/
inductive Stop | cap | stuck
  deriving DecidableEq, Repr

/-- a node's result: a value (`inl`, flat words) or a CONTINUE payload (`inr`) -/
abbrev Out := Except Stop (List W ⊕ List W)

structure Ctx where
  inp : List UInt8
  κ : Nat
  /-- meanings of the defs before the current one -/
  defs : List (List W → Except Stop (List W))

def setSlots (env : List W) (k : Nat) (vs : List W) : Except Stop (List W) :=
  if k + vs.length ≤ env.length then .ok (env.take k ++ vs ++ env.drop (k + vs.length)) else .error .stuck

def binop (op : Nat) (a b : UInt64) : Except Stop UInt64 :=
  match op with
  | 1 => .ok (a + b) | 2 => .ok (a - b) | 3 => .ok (a * b) | 4 => .ok (a &&& b) | 5 => .ok (a ||| b)
  | 6 => .ok (a <<< b) | 7 => .ok (a >>> b) | 8 => .ok (a ^^^ b) | _ => .error .stuck

def push (κ : Nat) (l : List UInt64) (v : UInt64) : Except Stop (List W) :=
  if l.length < κ then .ok [.b (l ++ [v])] else .error .cap

/-- prims (Gen's numbering); arguments flat, the input argument already dropped -/
def prim (cx : Ctx) (p : Nat) (as : List W) : Except Stop (List W) :=
  match p, as with
  | 1, [] => .ok [.w cx.inp.length.toUInt64]
  | 2, [.w i] => .ok [.w (cx.inp.getD i.toNat 0).toUInt64]
  | 3, [] => .ok [.w cx.inp.length.toUInt64]
  | 4, [.b o, .w v] => push cx.κ o v
  | 5, [] => .ok [.b []]
  | 6, [.b l] => .ok [.w l.length.toUInt64]
  | 7, [.b l, .w i] => .ok [.w (l.getD i.toNat 0)]
  | 8, [.b l, .w i, .w v] => .ok [.b (l.set i.toNat v)]
  | 9, [.b l, .w v] => push cx.κ l v
  | _, _ => .error .stuck

def val (r : Out) : Except Stop (List W) :=
  match r with | .ok (.inl v) => .ok v | .ok (.inr _) => .error .stuck | .error e => .error e

/-- the fuel loop: zero arm at fuel 0, else the step arm with slot 0 = fuel − 1; a CONTINUE writes slots 1.. -/
def loopRun (fz fs : List W → Out) : Nat → List W → Except Stop (List W)
  | 0, env => val (fz env)
  | n + 1, env => do
    let env1 ← setSlots env 0 [.w (UInt64.ofNat n)]
    match ← fs env1 with
    | .inl v => pure v
    | .inr st => loopRun fz fs n (← setSlots env1 1 st)

mutual
def ev (cx : Ctx) : Nd → List W → Out
  | .const v, _ => .ok (.inl [.w v])
  | .loc s w, env => if s + w ≤ env.length then .ok (.inl ((env.drop s).take w)) else .error .stuck
  | .bin op a b, env => do
    match ← val (ev cx a env), ← val (ev cx b env) with
    | [.w x], [.w y] => return .inl [.w (← binop op x y)]
    | _, _ => .error .stuck
  | .ite c a b t e, env => do
    match ← val (ev cx a env), ← val (ev cx b env) with
    | [.w x], [.w y] =>
      if c = 1 then (if x = y then ev cx t env else ev cx e env)
      else if c = 2 then (if x < y then ev cx t env else ev cx e env)
      else .error .stuck
    | _, _ => .error .stuck
  | .letE s w v b, env => do
    let x ← val (ev cx v env)
    if x.length = w then ev cx b (← setSlots env s x) else .error .stuck
  | .pair cs, env => return .inl (← evL cx cs env)
  | .call i as, env => do
    let xs ← evL cx as env
    match cx.defs[i]? with
    | some f => return .inl (← f xs)
    | none => .error .stuck
  | .prim p as, env => do return .inl (← prim cx p (← evL cx as env))
  | .loop z s, env =>
    match env with
    | .w n :: _ => return .inl (← loopRun (fun e => ev cx z e) (fun e => ev cx s e) n.toNat env)
    | _ => .error .stuck
  | .cont e, env => do return .inr (← val (ev cx e env))
def evL (cx : Ctx) : List Nd → List W → Except Stop (List W)
  | [], _ => .ok []
  | n :: r, env => do return (← val (ev cx n env)) ++ (← evL cx r env)
end

/-- one def's meaning, given the meanings of the earlier defs -/
def defMean (inp : List UInt8) (κ : Nat) (ms : List (List W → Except Stop (List W))) (d : DefA) :
    List W → Except Stop (List W) := fun ps =>
  if ps.length = d.npw ∧ d.npw ≤ d.nslots then do
    let v ← val (ev ⟨inp, κ, ms⟩ d.body (ps ++ List.replicate (d.nslots - d.npw) (.w 0)))
    if v.length = d.nres then pure v else .error .stuck
  else .error .stuck

def means (inp : List UInt8) (κ : Nat) : List (List W → Except Stop (List W)) → List DefA → List (List W → Except Stop (List W))
  | ms, [] => ms
  | ms, d :: r => means inp κ (ms ++ [defMean inp κ ms d]) r

/-- **the meaning of a program** on input `inp`: main (the last def, no parameters) returns the output buffer;
its words' low bytes are the output -/
def Sem (κ : Nat) (p : List DefA) (inp : List UInt8) : Except Stop (List UInt8) :=
  match (means inp κ [] p).getLast? with
  | some f => match f [] with
    | .ok [.b l] => .ok (l.map UInt64.toUInt8)
    | .ok _ => .error .stuck
    | .error e => .error e
  | none => .error .stuck

/-- Gen's buffer capacity (`C.g_999`) -/
def κC : Nat := 524288

/-! ## the machine contract -/
open Proven

def a0Ok (y : List UInt8) : BitVec 64 := if y = [] then 1 else 0
def a0Oom : BitVec 64 := BitVec.ofInt 64 (-1)
def a0Cap : BitVec 64 := BitVec.ofInt 64 (-2)

/-- what a finished run shows for the semantic result `r`; `oomOK`: work memory below the bound, so out-of-memory
(a0 = −1, a1 = 0, nothing outside the output block and the work block written) is also allowed -/
def Outcome (s : St) (ra : BitVec 64) (output work : Region) (r : Except Stop (List UInt8)) (oomOK : Prop)
    (s' : St) : Prop :=
  s'.regs.get? .PC = some ra ∧ abiSavedKept s s' ∧ Cfg s' ∧
  ((match r with
    | .ok y => s'.regs.get? .x10 = some (a0Ok y) ∧ s'.regs.get? .x11 = some (BitVec.ofNat 64 y.length) ∧
        bytesAt s' output.base y.length = y.map (some ·.toBitVec) ∧
        unchangedOutside s s' [⟨output.base, y.length⟩, work]
    | .error .cap => s'.regs.get? .x10 = some a0Cap ∧ s'.regs.get? .x11 = some 0 ∧
        unchangedOutside s s' [output, work]
    | .error .stuck => True) ∨
   (oomOK ∧ s'.regs.get? .x10 = some a0Oom ∧ s'.regs.get? .x11 = some 0 ∧ unchangedOutside s s' [output, work]))

/-- **`B` (bytes, 4 per instruction word, little endian) implements `f`**: calling convention and hosting as
`Proven.Implements1With` (a0 input, a1 length, a2 work base, a3 output, sp = work top, ra), inputs of at most `maxLen`
bytes, output block large enough for an ok result.  There is ONE work-size bound per input (`space`, existential):
with at least `space x` bytes of work memory the run never reports out-of-memory. -/
def ImplementsCW (B : List UInt8) (f : List UInt8 → Except Stop (List UInt8)) (space : List UInt8 → Nat)
    (maxLen : Nat := 2 ^ 20) : Prop :=
  ∀ (x : List UInt8) (s : St) (entry ra : BitVec 64) (input output work : Region),
    let codeR : Region := ⟨entry.toNat, B.length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 → B.length % 4 = 0 →
    bytesAt s entry.toNat B.length = B.map (some ·.toBitVec) →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 work.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → (∀ y, f x = .ok y → y.length ≤ output.len) → work.base % 8 = 0 →
    (∀ r ∈ [input, output, work, codeR], r.inRAM) → [input, output, work, codeR].Pairwise disjoint →
    Mapped s output → Mapped s work →
    runsTo s (Outcome s ra output work (f x) (work.len < space x))

/-- `ImplementsCW` for some work bound -/
def ImplementsC (B : List UInt8) (f : List UInt8 → Except Stop (List UInt8)) (maxLen : Nat := 2 ^ 20) : Prop :=
  ∃ space : List UInt8 → Nat, ImplementsCW B f space maxLen

/-! ## the stage hypotheses -/

/-- the parser (boxes B/C): `ParInv.ParserSound` for well-formed token streams below 2^24 words (F: `ParInv.parserSound`) -/
def ParStage : Prop := ∀ ts : List UInt64, ParSpec.TokWF ts → ts.length < 2 ^ 24 → ParInv.ParserSound ts

/-- O's ownership discipline with slot kinds 0 (word) / 1 (owned) / 2 (read-only) -/
def LinearK (p : List DefA) : Prop := ∃ Ks, OwnSpec.progOk [] [] Ks p = true ∧ ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2

/-- size bounds O's stage needs (= `OwnWF.Bnd`): `serialize` writes numbers mod 2^64 -/
def BndP (p : List DefA) : Prop := p.length < 2 ^ 64 ∧ ∀ d ∈ p, d.nslots < 2 ^ 20 ∧ d.nres < 2 ^ 64

/-- the ownership stage (box O, `OwnP.own_stage`): on a parsed program within `BndP` whose serialization is below 2^64
words, a non-empty result of `o41` certifies `LinearK` -/
def OwnStage : Prop := ∀ (ts : List UInt64) (p : List DefA), ParsesProgram ts p → BndP p → (serialize p).length < 2 ^ 64 →
  C.o41 (serialize p) ≠ [] → LinearK p

/-- the size bounds `BndP` (box O: the parser's width cap `nx + w < 2^20`, pending) -/
def BndStage : Prop := ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p → ts.length < 2 ^ 24 →
  C.g41 c (serialize p) ≠ [] → BndP p

/-- codegen (box A: g41's output is the code of the AST; box E: that code runs on Sail as `Sem`): for every parsed
linear program `p`, a non-empty result of Gen on `serialize p` implements `Sem κC p` -/
def GenStage : Prop :=
  ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p → ts.length < 2 ^ 24 → LinearK p →
    C.g41 c (serialize p) ≠ [] → ImplementsC (C.g41 c (serialize p)) (Sem κC p)

/-! ## facts used by the composition -/

/-- `o41` returns its input or nothing -/
theorem o41_ne (x : Buf) (h : C.o41 x ≠ []) : C.o41 x = x := by
  have key : ∀ r : UInt64, (if (r == 1) = true then x else bnew) ≠ [] → (if (r == 1) = true then x else bnew) = x := by
    intro r hr
    by_cases hc : (r == 1) = true
    · rw [if_pos hc]
    · rw [if_neg hc] at hr; exact absurd rfl hr
  exact key _ h

theorem g41_nil (c : List UInt8) : C.g41 c [] = [] := by
  simp [C.g41, C.g42, bget]

theorem refParse_nil : refParse [] = none := by decide

theorem op_ne : ∀ e ∈ LexSpec.opTable, e.1.length ≥ 1 := by decide

theorem isD_isW (c : UInt8) (h : LexSpec.isD c = true) : LexSpec.isW c = true := by
  have : ∀ n : Fin 256, LexSpec.isD (UInt8.ofFin n) = true → LexSpec.isW (UInt8.ofFin n) = true := by decide +kernel
  exact this c.toFin h

theorem sum2 (L : List UInt8) : (L.map (fun _ => (2 : Nat))).sum = 2 * L.length := by
  induction L <;> simp_all; omega

theorem step_len (l : List UInt8) (e : List UInt64) (r : List UInt8) (h : LexSpec.step l = some (e, r)) :
    e.length + 9 * r.length ≤ 9 * l.length := by
  match l, h with
  | c :: rr, h =>
    simp only [LexSpec.step] at h
    split at h
    · cases h; simp; omega
    · split at h
      · rename_i s k hf
        cases h
        have hm := List.mem_of_find?_eq_some hf
        have h1 := op_ne _ hm
        simp at h1 ⊢; omega
      · have hw : ((c :: rr).takeWhile LexSpec.isW).length + ((c :: rr).dropWhile LexSpec.isW).length = rr.length + 1 := by
          have := List.takeWhile_append_dropWhile (p := LexSpec.isW) (l := c :: rr)
          have := congrArg List.length this; simp only [List.length_append] at this; simpa using this
        have hc : ∀ hc : LexSpec.isW c = true, ((c :: rr).takeWhile LexSpec.isW).length ≥ 1 := by
          intro hc; simp [hc]
        split at h
        · split at h
          · cases h; have := hc (isD_isW c ‹_›); simp [LexSpec.le8]; omega
          · cases h
        · split at h
          · cases h; have := hc ‹_›
            split
            · simp; omega
            · simp only [List.length_cons, List.length_append, List.length_flatMap, List.length_nil]
              simp [sum2]; omega
          · cases h

/-- the lexer's output is at most 9 words per input byte -/
theorem lexes_len {x : List UInt8} {ts : List UInt64} (h : LexSpec.Lexes x ts) : ts.length ≤ 9 * x.length := by
  induction h with
  | nil => simp
  | cons hs _ ih => have := step_len _ _ _ hs; simp only [List.length_append]; omega

/-! ## the end-to-end theorem -/

/-- **C is sound on success**: if the driver emits code for source `x` (at most 2^20 bytes), then `x` lexes (Lex2Spec) and
parses (ParSpec) to a program `p`, and the emitted bytes implement `p`'s meaning on Sail (outcomes: the result, the
capacity trap when `Sem` reports it, out-of-memory only below the work bound). -/
theorem compiler_correct (HP : ParStage) (HO : OwnStage) (HB : BndStage) (HG : GenStage) (x : List UInt8) (hx : x.length ≤ 2 ^ 20)
    (h : mC x ≠ []) :
    ∃ ts p, LexSpec.Lexes x ts ∧ ParsesProgram ts p ∧ LinearK p ∧ ImplementsC (mC x) (Sem κC p) := by
  have hy0 : C.o41 (C.y16 (C.s10 x)) ≠ [] := fun e => h (by simp only [mC, e, g41_nil])
  have hoe := o41_ne _ hy0
  have hy : C.y16 (C.s10 x) ≠ [] := by rw [← hoe]; exact hy0
  by_cases h0 : C.s10 x = []
  · obtain ⟨p, hp, -⟩ := HP _ ⟨[], by rw [h0]; exact ParSpec.TokL.nil⟩ (by simp [h0]) hy
    rw [h0] at hp; simp [ParsesProgram, refParse_nil] at hp
  · have hL := LexSpec.s10_sound x (by omega) _ rfl h0
    have hb := lexes_len hL
    obtain ⟨p, hp, he⟩ := HP _ (lexes_tokWF hL) (by omega) hy
    have hg : C.g41 x (serialize p) ≠ [] := by rw [← he, ← hoe]; exact h
    have hts : (C.s10 x).length < 2 ^ 24 := by omega
    have hbd := HB x _ p hp hts hg
    have hsl : (serialize p).length < 2 ^ 64 := by have := ParSerLen.ser_lt hp hts; omega
    have hlin : LinearK p := HO _ p hp hbd hsl (by rw [← he]; exact hy0)
    refine ⟨_, p, hL, hp, hlin, ?_⟩
    have := HG x _ p hp hts hlin hg
    rw [mC, hoe, he]; exact this

end NanoMain
