/- **Emission checked in pieces** (for the kernel checks of large programs, e.g. Nano/ParseS3BStage.lean):
`emitFsQ` runs `emitFs` keeping only the position, so `emitFsQ` on `A ++ B` is `A` then `B`
(`emitFsQ_append`, `emitFsQ_append_of`), each checked by its own `decide +kernel`; `emitP_lt` gives the
hypothesis `hE` of `Nano.S3Stage.compiles_len` from them. -/
import Legacy.Compiler.Ir.Emit

namespace Proven.Ir.Target
open Proven.Mach
set_option autoImplicit false
variable (T : Target)

/-- `emitFs`, keeping only the position after the functions -/
def emitFsQ (P : Prog Nat) (L : Lay) : FId → Nat → List (Func Nat) → Option Nat
  | _, q, [] => some q
  | f, q, F :: Fs => if L.fq.getD f 0 = q then
      match T.emitF (P.env L) F (L.posF f) L.ex q (L.fq.getD (f + 1) L.ex) with
      | some c => emitFsQ P L (f + 1) (q + T.len c) Fs
      | none => none
    else none

theorem emitFsQ_append (P : Prog Nat) (L : Lay) (A B : List (Func Nat)) : ∀ (f q : Nat),
    T.emitFsQ P L f q (A ++ B) = (T.emitFsQ P L f q A).bind fun q₁ => T.emitFsQ P L (f + A.length) q₁ B := by
  induction A with
  | nil => intro f q; simp [emitFsQ]
  | cons F A ih =>
    intro f q
    simp only [List.cons_append, emitFsQ, List.length_cons]
    split
    · split
      · rw [ih]; simp only [Nat.add_assoc, Nat.add_comm 1]
      · rfl
    · rfl

theorem emitFsQ_append_of (P : Prog Nat) (L : Lay) (A B : List (Func Nat)) {f q q₁ f₁ : Nat}
    (hA : T.emitFsQ P L f q A = some q₁) (hf : f + A.length = f₁) :
    T.emitFsQ P L f q (A ++ B) = T.emitFsQ P L f₁ q₁ B := by
  rw [emitFsQ_append, hA, Option.bind_some, hf]

theorem len_append (a b : List EOp) : T.len (a ++ b) = T.len a + T.len b := by
  simp [len, words_append]

theorem emitFs_of_Q (P : Prog Nat) (L : Lay) : ∀ (Fs : List (Func Nat)) (f q : Nat),
    T.emitFsQ P L f q Fs = some L.ex → ∃ c, T.emitFs P L f q Fs = some c ∧ q + T.len c = L.ex := by
  intro Fs
  induction Fs with
  | nil =>
    intro f q h
    simp only [emitFsQ, Option.some.injEq] at h
    exact ⟨[], by simp [emitFs, h], by simp [len, words, h]⟩
  | cons F Fs ih =>
    intro f q h
    simp only [emitFsQ] at h
    split at h
    · rename_i hq
      split at h
      · rename_i c hc
        obtain ⟨d, hd, hl⟩ := ih (f + 1) (q + T.len c) h
        refine ⟨c ++ d, ?_, ?_⟩
        · simp only [emitFs, if_pos hq, hc, hd, Option.map_some]
        · rw [len_append, ← Nat.add_assoc]; exact hl
      · exact nomatch h
    · exact nomatch h

/-- the emission's length check from the stub's length `q0`, the functions checked by `emitFsQ` (in pieces, by
`emitFsQ_append`) and the exit -/
theorem emitP_lt (P : Prog Nat) (L : Lay) (q0 : Nat)
    (hm : ((P.funcs[P.main]?).map (·.params.length)) = some 3)
    (hs : (T.emitStub L.ex (((P.funcs[P.main]?).map (·.slots)).getD 0) (L.fq.getD P.main 0)).map T.len = some q0)
    (hF : T.emitFsQ P L 0 q0 P.funcs = some L.ex) (hx : L.ex + T.len [.exit] < 2 ^ 17) :
    ((T.emitP P L).map fun c => decide ((T.words c).length < 2 ^ 17)) = some true := by
  obtain ⟨c, hc, hl⟩ := T.emitFs_of_Q P L P.funcs 0 q0 hF
  cases h : T.emitStub L.ex (((P.funcs[P.main]?).map (·.slots)).getD 0) (L.fq.getD P.main 0) with
  | none => rw [h] at hs; exact nomatch hs
  | some st =>
    rw [h] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    subst hs
    simp only [emitP, hm, if_true, h, hc, Option.map_some, Option.some.injEq, decide_eq_true_eq]
    have : (T.words (st ++ c ++ [.exit])).length = T.len (st ++ c ++ [.exit]) := rfl
    rw [this, len_append, len_append, hl]
    exact hx

end Proven.Ir.Target
