/- Nano/Main/Sem: the machine-independent half of the end-to-end statement (split out of Main.lean):
the driver `mC`, the meaning `Sem` of a resolved program (word level, buffer capacity κ, `κC`), the stage hypotheses
`ParStage`/`LinearK`/`BndP`/`OwnStage`/`BndStage`, and the lexer/driver facts.  No machine model here; the RV64
contract (`Outcome`, `ImplementsCW`, `GenStage`, `compiler_correct`) stays in Main.lean.-/
import Nano.Lexer.Lex2Sound
import Nano.Parser.Par1
import Nano.Lexer.Dsg
import Nano.Codegen.Gen
import Nano.Ownership.Own
import Nano.Ownership.OwnSpec
import Nano.Parser.ParInv
import Nano.Lexer.MainTokWF
import Nano.Parser.ParSerLen
import Nano.Parser.NumC

namespace NanoMain
open ParSpec

/-- C's driver, verbatim from `Testing/nano/v2self/build_self_S.py` (not in `C/Main.lean`, which holds the old chain) -/
def mC (x : List UInt8) : List UInt8 := C.g41 x (C.o41 (C.u10 (C.y16 (C.t10 (C.s10 x)))))

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

/-! ## facts used by the composition -/

/-- `o41` returns its input or nothing -/
theorem o41_ne (x : Buf) (h : C.o41 x ≠ []) : C.o41 x = x := by
  have key : ∀ r : UInt64, (if (r == 1) = true then x else bnew) ≠ [] → (if (r == 1) = true then x else bnew) = x := by
    intro r hr
    by_cases hc : (r == 1) = true
    · rw [if_pos hc]
    · rw [if_neg hc] at hr; exact absurd rfl hr
  exact key _ h

/-- `u10` returns its input or nothing -/
theorem u10_ne (x : Buf) (h : C.u10 x ≠ []) : C.u10 x = x := by
  unfold C.u10 at *
  by_cases hc : (C.u11 x == 1) = true
  · rw [if_pos hc]
  · rw [if_neg hc] at h; exact absurd rfl h

theorem g41_nil (c : List UInt8) : C.g41 c [] = [] := by
  simp [C.g41, C.g42, bget]

theorem refParse_nil : refParse [] = none := by decide

theorem op_ne : ∀ e ∈ LexSpec.opTable, e.1.length ≥ 1 := by decide

theorem isD_isW (c : UInt8) (h : LexSpec.isD c = true) : LexSpec.isW c = true := by
  have : ∀ n : Fin 256, LexSpec.isD (UInt8.ofFin n) = true → LexSpec.isW (UInt8.ofFin n) = true := by decide +kernel
  exact this c.toFin h

theorem sum2 (L : List UInt8) : (L.map (fun _ => (2 : Nat))).sum = 2 * L.length := by
  induction L <;> simp_all; omega

theorem blockEnd_len : ∀ (d : Nat) (l t : List UInt8), LexSpec.blockEnd d l = some t → t.length ≤ l.length
  | _, [], _, h => by simp [LexSpec.blockEnd] at h
  | _, [_], _, h => by simp [LexSpec.blockEnd] at h
  | d, c :: c' :: r, t, h => by
    simp only [LexSpec.blockEnd] at h
    split at h
    · split at h
      · cases h; simp; omega
      · have := blockEnd_len _ r t h; simp; omega
    · split at h
      · have := blockEnd_len _ r t h; simp; omega
      · have := blockEnd_len _ (c' :: r) t h; simp at this ⊢; omega

theorem docWs_len : ∀ (f : Nat) (l t : List UInt8), LexSpec.docWs f l = some t → t.length ≤ l.length
  | 0, _, _, h => by simp [LexSpec.docWs] at h
  | _ + 1, [], t, h => by simp [LexSpec.docWs] at h; subst h; simp
  | f + 1, c :: r, t, h => by
    simp only [LexSpec.docWs] at h
    split at h
    · have := docWs_len f r t h; simp; omega
    split at h
    · cases h
    split at h
    · have := docWs_len f _ t h; have := (List.dropWhile_suffix (· != 10) (l := r)).length_le; simp; omega
    split at h
    · obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.1 h
      have := docWs_len f u t hd; have := blockEnd_len 0 _ _ hu
      have : r.tail.tail.length ≤ r.length := by simp only [List.length_tail]; omega
      simp; omega
    · cases h; simp

theorem attrEnd_len : ∀ (l w : List UInt8) (d : Bool) (t : List UInt8), LexSpec.attrEnd l w d = some t → t.length < l.length
  | [], _, _, _, h => by simp [LexSpec.attrEnd] at h
  | b :: r, w, d, t, h => by
    simp only [LexSpec.attrEnd] at h
    split at h
    · split at h
      · cases h
      · have := attrEnd_len r _ _ t h; simp; omega
    · split at h
      · cases h
      · split at h
        · have := attrEnd_len r _ _ t h; simp; omega
        · split at h
          · split at h
            · have := attrEnd_len r _ _ t h; simp; omega
            · cases h
          · split at h
            · split at h
              · cases h; simp
              · cases h
            · cases h

theorem dw_len {p : UInt8 → Bool} (l : List UInt8) : (l.dropWhile p).length ≤ l.length :=
  (List.dropWhile_suffix p).length_le

theorem scopeLine_len (k : Nat) (r n e : List UInt8) (h : LexSpec.scopeLine k r = some (n, e)) :
    n.length + e.length ≤ r.length := by
  unfold LexSpec.scopeLine at h
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  · have h1 := List.takeWhile_append_dropWhile (p := LexSpec.isW) (l := r.dropWhile (· == 32))
    have h2 := congrArg List.length h1; simp only [List.length_append] at h2
    have := dw_len (p := (· == 32)) r
    have := dw_len (p := (· == 32)) ((r.dropWhile (· == 32)).dropWhile LexSpec.isW)
    omega

theorem step_len (l : List UInt8) (e : List UInt64) (r : List UInt8) (h : LexSpec.step l = some (e, r)) :
    e.length + 9 * r.length ≤ 9 * l.length := by
  match l, h with
  | c :: rr, h =>
    simp only [LexSpec.step] at h
    have htl : rr.tail.length ≤ rr.length := by cases rr <;> simp
    split at h
    · cases h; simp; omega
    split at h
    · cases h; have := dw_len (p := (· != 10)) rr.tail; simp; omega
    split at h
    · obtain ⟨t, hb, he⟩ := Option.bind_eq_some_iff.1 h
      have he' : e = [] ∧ r = t := by split at he <;> simp_all
      obtain ⟨rfl, rfl⟩ := he'
      have htt : rr.tail.tail.length ≤ rr.tail.length := by cases rr.tail <;> simp
      split at hb
      · obtain ⟨u, hu, hd⟩ := Option.bind_eq_some_iff.1 hb
        have := docWs_len _ _ _ hu; have := blockEnd_len 0 _ _ hd; simp; omega
      · have := blockEnd_len 0 _ _ hb; simp; omega
    split at h
    · obtain ⟨t, hb, he⟩ := Option.bind_eq_some_iff.1 h
      have he' : e = [] ∧ r = t := by split at he <;> simp_all
      obtain ⟨rfl, rfl⟩ := he'
      have := attrEnd_len _ _ _ _ hb; simp; omega
    split at h
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
        · have := hc ‹_›
          split at h
          · cases h
          split at h
          · obtain ⟨⟨n, e'⟩, hs, he⟩ := Option.map_eq_some_iff.1 h
            cases he
            have := scopeLine_len _ _ _ _ hs
            have : ∀ o, (LexSpec.scopeTok o n).length ≤ 2 * n.length + 3 := fun o => by
              unfold LexSpec.scopeTok; split <;> simp [List.length_flatMap, sum2] <;> omega
            refine Nat.le_trans (Nat.add_le_add_right (this _) _) ?_
            simp only [List.length_cons]; omega
          split at h
          · split at h
            · cases h; simp; omega
            · cases h
          cases h
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

end NanoMain
