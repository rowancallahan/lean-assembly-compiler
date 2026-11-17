/- An S3-compiled stage as a link of nano's self-hosting composition (`Nano.Link.link_stage`, list form, result
length in `a1`): from the generated `computes` of `s3_compile`/`s3_compileB` and two kernel-evaluated facts about
the concrete program (its signature is small, the IR compiler accepts it), the machine theorem
`Implements1With (·.data.toList) id (S3.words P) (f ∘ ·.data.toList) (spaceP P) (2 ^ 20) true`, through the adapter
`Proven.S3.implements1_spaceOf` (Riscv/Back/S3Impl1.lean). `Testing/notes/NANO_PARSE_S3.md`. -/
import Lean
import Riscv.Back.S3Impl1
import Nano.Link

/-! ## literals of IR programs and layouts (kernel evaluation of the IR compiler)

The kernel evaluates `Ir.compileW` lazily without sharing: `layout`'s accumulator is re-evaluated at every use, which
blows up (> 9 GB on a 2000-word program). So the allocator's result and the layout are materialized as literal terms
(`irLit%`, `layLit%`: elaborated by evaluation, untrusted), and the kernel checks: `alloc P = some Q` (`decide`), a
few `layStep`s to a fixpoint, and `emitP Q L` on the literals. -/

deriving instance Lean.ToExpr for Proven.Op
deriving instance Lean.ToExpr for Proven.Mach.MOp
deriving instance Lean.ToExpr for Proven.Mach.Cond
deriving instance Lean.ToExpr for Proven.Ir.Arg
deriving instance Lean.ToExpr for Proven.Ir.Rhs
deriving instance Lean.ToExpr for Proven.Ir.Tst
deriving instance Lean.ToExpr for Proven.Ir.Inst
deriving instance Lean.ToExpr for Proven.Ir.Term
deriving instance Lean.ToExpr for Proven.Ir.Block
deriving instance Lean.ToExpr for Proven.Ir.Func
deriving instance Lean.ToExpr for Proven.Ir.Prog
deriving instance Lean.ToExpr for Proven.Ir.Lay
deriving instance DecidableEq for Proven.Ir.Arg
deriving instance DecidableEq for Proven.Ir.Rhs
deriving instance DecidableEq for Proven.Ir.Tst
deriving instance DecidableEq for Proven.Ir.Inst
deriving instance DecidableEq for Proven.Ir.Term
deriving instance DecidableEq for Proven.Ir.Block
deriving instance DecidableEq for Proven.Ir.Func
deriving instance DecidableEq for Proven.Ir.Prog
deriving instance DecidableEq for Proven.Ir.Lay

namespace Nano.S3Stage
open Lean Elab Term Meta in
/-- `irLit% e`: the value of `e : Ir.Prog Nat` as a literal term (untrusted: every use is checked by the kernel) -/
elab "irLit% " t:term : term => do
  let ty := mkApp (Lean.mkConst ``Proven.Ir.Prog) (Lean.mkConst ``Nat)
  let e ← instantiateMVars (← elabTerm t (some ty))
  let v ← unsafe evalExpr (Proven.Ir.Prog Nat) ty e
  return toExpr v

open Lean Elab Term Meta in
/-- `funcLit% e`: the value of `e : Ir.Func Nat` as a literal term (untrusted) -/
elab "funcLit% " t:term : term => do
  let ty := mkApp (Lean.mkConst ``Proven.Ir.Func) (Lean.mkConst ``Nat)
  let e ← instantiateMVars (← elabTerm t (some ty))
  let v ← unsafe evalExpr (Proven.Ir.Func Nat) ty e
  return toExpr v

open Lean Elab Term Meta in
/-- `layLit% e`: the value of `e : Ir.Lay` as a literal term (untrusted) -/
elab "layLit% " t:term : term => do
  let ty := Lean.mkConst ``Proven.Ir.Lay
  let e ← instantiateMVars (← elabTerm t (some ty))
  let v ← unsafe evalExpr Proven.Ir.Lay ty e
  return toExpr v

open Proven Proven.Ir Proven.Mach.Riscv in
theorem layout_add (Q : Ir.Prog Nat) : ∀ (a b : Nat) (L : Lay), rvT.layout Q (a + b) L = rvT.layout Q a (rvT.layout Q b L)
  | a, 0, L => rfl
  | a, b + 1, L => by
    rw [show a + (b + 1) = (a + b) + 1 by omega]
    simp only [Target.layout]
    exact layout_add Q a b _

open Proven Proven.Ir Proven.Mach.Riscv in
theorem layout_fix (Q : Ir.Prog Nat) (L : Lay) (h : rvT.layStep Q L = L) : ∀ k, rvT.layout Q k L = L
  | 0 => rfl
  | k + 1 => by simp only [Target.layout, h]; exact layout_fix Q L h k

open Proven Proven.Ir Proven.Mach.Riscv in
/-- the IR compiler accepts `P0`, from checks on literals -/
theorem compileW_isSome {P0 : Ir.Prog VReg} {Q : Ir.Prog Nat} {L : Lay} (m : Nat) (hQ : Ir.alloc P0 = some Q)
    (hm : m ≤ Target.rounds Q) (hL : rvT.layout Q m ⟨[], [], 0⟩ = L) (hfix : rvT.layStep Q L = L)
    (hE : (rvT.emitP Q L).isSome = true) : (Ir.compileW P0).isSome = true := by
  have hlay : rvT.layout Q (Target.rounds Q) ⟨[], [], 0⟩ = L := by
    rw [show Target.rounds Q = (Target.rounds Q - m) + m by omega, layout_add, hL, layout_fix Q L hfix]
  unfold Ir.compileW
  rw [hQ]
  simp only [Target.lin, hlay]
  cases h : rvT.emitP Q L with
  | none => rw [h] at hE; exact nomatch hE
  | some c => rfl

open Proven Proven.Ir Proven.Mach.Riscv in
/-- the words of an S3 program, from checks on literals -/
theorem words_eq {P : Proven.S3.Prog} {Q : Ir.Prog Nat} {L : Lay} {c : List EOp} (m : Nat) (hQ : Ir.alloc (Proven.S3.lowerP P) = some Q)
    (hm : m ≤ Target.rounds Q) (hL : rvT.layout Q m ⟨[], [], 0⟩ = L) (hfix : rvT.layStep Q L = L)
    (hE : rvT.emitP Q L = some c) : Proven.S3.words P = rvT.words c := by
  have hlay : rvT.layout Q (Target.rounds Q) ⟨[], [], 0⟩ = L := by
    rw [show Target.rounds Q = (Target.rounds Q - m) + m by omega, layout_add, hL, layout_fix Q L hfix]
  unfold Proven.S3.words Ir.compileW
  rw [hQ]
  simp only [Target.lin, hlay, hE, Option.map_some]
open Proven Proven.Ir Proven.Mach.Riscv in
/-- the words of an S3 program, as a computation on the literals -/
theorem words_eq' {P : Proven.S3.Prog} {Q : Ir.Prog Nat} {L : Lay} (m : Nat)
    (hQ : Ir.alloc (Proven.S3.lowerP P) = some Q) (hm : m ≤ Target.rounds Q)
    (hL : rvT.layout Q m ⟨[], [], 0⟩ = L) (hfix : rvT.layStep Q L = L) :
    Proven.S3.words P = ((rvT.emitP Q L).map rvT.words).getD [] := by
  cases h : rvT.emitP Q L with
  | none =>
    have hlay : rvT.layout Q (Target.rounds Q) ⟨[], [], 0⟩ = L := by
      rw [show Target.rounds Q = (Target.rounds Q - m) + m by omega, layout_add, hL, layout_fix Q L hfix]
    unfold Proven.S3.words Ir.compileW
    rw [hQ]; simp only [Target.lin, hlay, h, Option.map_none]; rfl
  | some c => rw [words_eq m hQ hm hL hfix h]; rfl

open Proven Proven.Ir Proven.Mach.Riscv in
/-- the IR compiler accepts the program and its code is shorter than `2 ^ 17` words, from ONE kernel evaluation of
`emitP` on the literals -/
theorem compiles_len {P : Proven.S3.Prog} {Q : Ir.Prog Nat} {L : Lay} (m : Nat)
    (hQ : Ir.alloc (Proven.S3.lowerP P) = some Q) (hm : m ≤ Target.rounds Q)
    (hL : rvT.layout Q m ⟨[], [], 0⟩ = L) (hfix : rvT.layStep Q L = L)
    (hE : ((rvT.emitP Q L).map fun c => decide ((rvT.words c).length < 2 ^ 17)) = some true) :
    (Ir.compileW (Proven.S3.lowerP P)).isSome = true ∧ (Proven.S3.words P).length < 2 ^ 17 := by
  cases h : rvT.emitP Q L with
  | none => rw [h] at hE; exact nomatch hE
  | some c =>
    rw [h] at hE
    simp only [Option.map_some, Option.some.injEq, decide_eq_true_eq] at hE
    exact ⟨compileW_isSome m hQ hm hL hfix (by rw [h]; rfl), by rw [words_eq m hQ hm hL hfix h]; exact hE⟩

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
