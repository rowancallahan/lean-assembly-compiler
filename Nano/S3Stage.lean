/- An S3-compiled stage as a link of nano's self-hosting composition (`Nano.Link.link_stage`, list form, result
length in `a1`): from the generated `computes` of `s3_compile`/`s3_compileB` and two kernel-evaluated facts about
the concrete program (its signature is small, the IR compiler accepts it), the machine theorem
`Implements1With (·.data.toList) id (S3.words P) (f ∘ ·.data.toList) (spaceP P) (2 ^ 20) true`, through the adapter
`Proven.S3.implements1_spaceOf` (Riscv/Back/S3Impl1.lean). `Testing/notes/NANO_PARSE_S3.md`. -/
import Riscv.Back.S3Impl1
import Nano.Link

namespace Nano.S3Stage
open Proven Proven.S3 Proven.Top Proven.Top.Alloc

/-- a decidable form of `Small` -/
def smallB (S : Sig) : Bool :=
  S.dts.all fun cs => decide (cs.length < 2 ^ 32) && cs.all fun fs => decide (fs.length < 2 ^ 32)

theorem lget_all {α : Type} (Pr : α → Prop) (d : α) (hd : Pr d) :
    ∀ (l : List α) (i : Nat), (∀ x ∈ l, Pr x) → Pr (lget d l i)
  | [], _, _ => by simp [lget]; exact hd
  | a :: _, 0, h => by simp only [lget]; exact h a (by simp)
  | _ :: l, i + 1, h => by simp only [lget]; exact lget_all Pr d hd l i fun x hx => h x (by simp [hx])

theorem small_of {S : Sig} (h : smallB S = true) : Small S := by
  unfold smallB at h
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have hc := lget_all (fun cs : List (List Ty) => cs.length < 2 ^ 32 ∧ ∀ fs ∈ cs, fs.length < 2 ^ 32) []
    (by simp) S.dts
  intro i
  obtain ⟨h1, h2⟩ := hc i h
  exact ⟨h1, fun j => lget_all (fun fs : List Ty => fs.length < 2 ^ 32) [] (by simp) _ j h2⟩

/-- `S3.compile` from the IR compiler's result -/
theorem compile_of {P : Prog} (hA : Accepted P) {W : List (BitVec 32)} {Q : Ir.Prog Nat}
    (hW : Ir.compileW (lowerP P) = some (W, Q)) : S3.compile P = some ⟨wordBytes W, 8, Ir.events Q⟩ := by
  unfold S3.compile
  rw [if_pos hA]
  unfold Ir.compile
  rw [hW]

/-- the work space of an S3 program's code (`spaceOf` of its compiled form; `0` if it does not compile) -/
noncomputable def spaceP (P : Prog) (n : Nat) : Nat :=
  match S3.compile P with
  | some c => spaceOf c n
  | none => 0

/-- **an S3 stage**: the machine theorem of an S3 program that computes the byte function `f` -/
theorem stage {P : Prog} {f : List UInt8 → List UInt8} (hcomp : Computes P f id id)
    (hsmall : smallB P.S = true) (hmain : (P.S.fn P.main).1.length = 1)
    (hW : (Ir.compileW (lowerP P)).isSome = true) :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words P)
      (fun xs => f xs.data.toList) (spaceP P) (2 ^ 20) true := by
  obtain ⟨⟨W, Q⟩, hWQ⟩ := Option.isSome_iff_exists.mp hW
  have hc := compile_of ⟨small_of hsmall, hmain⟩ hWQ
  have h := implements1_spaceOf hc (fun xs : ByteArray => xs.data.toList) (fun xs => f xs.data.toList)
    (fun xs => hcomp xs.data.toList)
  have hsp : spaceP P = spaceOf ⟨wordBytes W, 8, Ir.events Q⟩ := by
    funext n; unfold spaceP; rw [hc]
  rw [hsp]; exact h

/-- the words of an S3 program, from the IR compiler's result -/
theorem words_of {P : Prog} {W : List (BitVec 32)} {Q : Ir.Prog Nat}
    (hW : Ir.compileW (lowerP P) = some (W, Q)) : S3.words P = W := by
  unfold S3.words; rw [hW]

end Nano.S3Stage
