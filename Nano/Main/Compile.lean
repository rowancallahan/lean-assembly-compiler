/- C as a compiler, machine-independent (split out of MainTop): source texts `SrcC` and their meaning `srcRun`
(lex, parse, `Sem κC`), the explicit work bound `spaceC` (`max 16 ∘ Msp`), `compileC` (C's driver `mC`), and
`compiler_correctG` (lexer, parser and ownership stages: an accepted text's code is Gen's code for a parsed linear
program). -/
import Nano.Parser.MainTyP
import Nano.Parser.ParInvRun
import Nano.Ownership.OwnStage
import Nano.Base.Compiler.AllocSpec
import Nano.Run.RunsDef
namespace NanoMain
open Proven.Top Proven.Top.Alloc ParSpec

theorem lexes_det : ∀ {x : List UInt8} {t t' : List UInt64}, LexSpec.Lexes x t → LexSpec.Lexes x t' → t = t'
  | _, _, _, .nil, h => by
    cases h with
    | nil => rfl
    | cons hs _ => simp [LexSpec.step] at hs
  | _, _, _, .cons hs h1, h => by
    cases h with
    | nil => simp [LexSpec.step] at hs
    | cons hs' h2 =>
      rw [hs] at hs'; simp only [Option.some.injEq, Prod.mk.injEq] at hs'; obtain ⟨rfl, rfl⟩ := hs'
      rw [lexes_det h1 h2]

/-- a source text -/
structure SrcC where
  text : List UInt8

open Classical in
/-- the program a text denotes (Lex2Spec, then ParSpec) -/
noncomputable def pOf (x : List UInt8) : Option (List DefA) :=
  if h : ∃ p, ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts p then some (Classical.choose h) else none

theorem pOf_eq {x : List UInt8} {ts : List UInt64} {p : List DefA} (hl : LexSpec.Lexes x ts) (hp : ParsesProgram ts p) :
    pOf x = some p := by
  have h : ∃ p, ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts p := ⟨p, ts, hl, hp⟩
  unfold pOf; rw [dif_pos h]
  obtain ⟨ts', hl', hp'⟩ := Classical.choose_spec h
  rw [lexes_det hl hl'] at hp
  unfold ParsesProgram at hp hp'; rw [hp'] at hp; cases hp; rfl

/-- **the meaning of a text** on an input -/
noncomputable def srcRun (s : SrcC) (inp : List UInt8) : Option (List UInt8) :=
  (pOf s.text).bind fun p => (Sem κC p inp).toOption

noncomputable instance : Program SrcC := ⟨srcRun⟩
/-- **the work bound of C's code for a text**: EXPLICIT, the exact threshold `Msp` (RunsDef: the least work size with
which main never runs out of room, at least 16), bounded by `Msp_le` -/
noncomputable def spaceC (x : List UInt8) : List UInt8 → Nat :=
  match pOf x with
  | some p => fun inp => max 16 (Msp p inp)
  | none => fun _ => 0

/-- **C as a compiler** -/
noncomputable def compileC (s : SrcC) : Option CompiledA :=
  if mC s.text ≠ [] ∧ s.text.length ≤ 2 ^ 20 then some ⟨mC s.text, 1, fun inp => [.alloc (spaceC s.text inp)]⟩
  else none

theorem toOption_some {r : Except Stop (List UInt8)} {y : List UInt8} (h : r.toOption = some y) : r = .ok y := by
  cases r <;> simp [Except.toOption] at h; rw [h]
/-- the parser stage, discharged (F) -/
theorem parStage : ParStage := fun _ hW hts => ParInv.parserSound hW hts

/-- the ownership stage, discharged (O) -/
theorem ownStage : OwnStage := fun _ _ hp hb hl h => OwnP.own_stage hp hb hl h

/-- as `compiler_correct`, for any property `Q` of Gen's code and the program that codegen provides -/
theorem compiler_correctG (HB : BndStage) (Q : List UInt8 → List DefA → Prop)
    (HG : ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p → ts.length < 2 ^ 24 → LinearK p →
      C.g41 c (serialize p) ≠ [] → Q (C.g41 c (serialize p)) p)
    (x : List UInt8) (hx : x.length ≤ 2 ^ 20) (h : mC x ≠ []) :
    ∃ ts p, LexSpec.Lexes x ts ∧ ParsesProgram ts p ∧ LinearK p ∧ Q (mC x) p := by
  have hy0 : C.o41 (C.y16 (C.s10 x)) ≠ [] := fun e => h (by simp only [mC, e, g41_nil])
  have hoe := o41_ne _ hy0
  have hy : C.y16 (C.s10 x) ≠ [] := by rw [← hoe]; exact hy0
  by_cases h0 : C.s10 x = []
  · obtain ⟨p, hp, -⟩ := parStage _ ⟨[], by rw [h0]; exact ParSpec.TokL.nil⟩ (by simp [h0]) hy
    rw [h0] at hp; simp [ParsesProgram, refParse_nil] at hp
  · have hL := LexSpec.s10_sound x (by omega) _ rfl h0
    have hb := lexes_len hL
    obtain ⟨p, hp, he⟩ := parStage _ (lexes_tokWF hL) (by omega) hy
    have hg : C.g41 x (serialize p) ≠ [] := by rw [← he, ← hoe]; exact h
    have hts : (C.s10 x).length < 2 ^ 24 := by omega
    have hbd := HB x _ p hp hts hg
    have hsl : (serialize p).length < 2 ^ 64 := by have := ParSerLen.ser_lt hp hts; omega
    have hlin : LinearK p := ownStage _ p hp hbd hsl (by rw [← he]; exact hy0)
    refine ⟨_, p, hL, hp, hlin, ?_⟩
    have := HG x _ p hp hts hlin hg
    rw [mC, hoe, he]; exact this

/-- the field bounds `DB` (fields < 2^32, `NB`) for every program Gen accepts -/
def DBStage : Prop := ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p →
  ts.length < 2 ^ 24 → LinearK p → C.g41 c (serialize p) ≠ [] → ∀ d ∈ p, Templates.DB d

/-- **`memoryNeeded` is finite and bounded**: for a text denoting a parsed linear program, C's explicit work bound is
at most D's uniform work bound `gen_R` + 30 bytes -/
theorem spaceC_le {x : List UInt8} {ts : List UInt64} {p : List DefA} (hpo : pOf x = some p)
    (hp : ParsesProgram ts p) (hL : LinearK p) (inp : List UInt8) (hin : inp.length ≤ 2 ^ 20) :
    spaceC x inp ≤ Classical.choose (gen_R hp hL inp hin) + 30 := by
  have hR := Classical.choose_spec (gen_R hp hL inp hin)
  have := Msp_le hp inp _ fun T base len h8 h32 hle => by
    obtain ⟨h1, h2⟩ := hR T base len h8 h32 hle
    exact ⟨fun y hy => by obtain ⟨a, l, H', e, -⟩ := h1 y hy; exact ⟨_, _, e⟩, h2⟩
  have h16 := Msp_ge p inp
  unfold spaceC; rw [hpo]; simp only; omega

end NanoMain
