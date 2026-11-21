/- The native AArch64 ENCODER as a Lean specification (option E: the native generator is the atom encoder of Gen's J
program; the nano-subset translator is proved equal to this spec).  Input: a J program (`List J`, no RISC-V words:
later the generator's IR).
* `cand`: the atom that starts a J list (longest fused form first); `atomize`: the greedy parse, checked against the
  J list, so `atomize_j : atomize n l = some tl → tl.flatMap NTm.j = l` holds by construction. -/
import Nano.Run.NatImgLaws
namespace JT
open Proven.Top SimW CallProbe ArmEnc

deriving instance DecidableEq for CallProbe.J

/-- the value of Gen's long `li` (`liT`, 8 bytes, top first), read from the `slli; addi` pairs -/
def liBytes : Nat → List J → Nat → Nat
  | k + 1, .slli _ _ _ :: .addi _ _ c :: l, acc => liBytes k l (acc * 256 + c.toNat)
  | _, _, acc => acc

/-- the atom that starts a J list: fused forms first -/
def cand : List J → Option NTm
  | .addi d 0 imm :: .slli d1 d2 8 :: l =>
    if d1 = d ∧ d2 = d then some (.li d (UInt64.ofNat (liBytes 8 (.slli d1 d2 8 :: l) 0))) else some (.addi d 0 imm)
  | .addi d n imm :: _ => some (.addi d n imm)
  | .ld x n 0 :: .ld y m 8 :: _ =>
    if n = m ∧ x ≠ y ∧ x ≠ n ∧ y ≠ n then some (.ldp x y n false) else some (.ld x n 0)
  | .ld y n 8 :: .ld x m 0 :: _ =>
    if n = m ∧ x ≠ y ∧ x ≠ n ∧ y ≠ n then some (.ldp x y n true) else some (.ld y n 8)
  | .ld d n off :: _ => some (.ld d n off)
  | .sd s n off :: _ => some (.sd s n off)
  | .bgeu x y 2 :: .jal 0 off :: _ => some (.cj .geu x y off)
  | .bltu x y 2 :: .jal 0 off :: _ => some (.cj .ltu x y off)
  | .beq r 0 2 :: .jal 0 off :: _ => some (.lpz r off)
  | .beq x y 2 :: .jal 0 off :: _ => some (.cj .eq x y off)
  | .bgeu x y off :: _ => some (.bgeu x y off)
  | .beq r 0 off :: _ => some (.beqz r off)
  | .bne r 0 off :: _ => some (.bnez r off)
  | .alu 1 d n m :: .lbu d1 d2 0 :: _ => if d1 = d ∧ d2 = d then some (.ldrbx d n m) else some (.alu 1 d n m)
  | .alu op d x y :: _ => some (.alu op d x y)
  | .slli 6 6 3 :: .alu 1 5 5 6 :: .ld 14 5 16 :: _ => some .bgetI
  | .slli 6 6 3 :: .alu 1 6 5 6 :: .sd 14 6 16 :: _ => some .bsetI
  | .slli 15 7 3 :: .alu 1 15 15 5 :: _ => some .bpushI
  | .srli d n 3 :: .slli d1 d2 3 :: _ => if d1 = d ∧ d2 = d then some (.align8 d n) else none
  | .jal rd off :: _ => some (.jal rd off)
  | .jalr 0 rs :: _ => some (.jalr rs)
  | .sb s n 0 :: _ => some (.sb s n)
  | _ => none

/-- **the greedy parse** of a J list into atoms (`n` = fuel, the length suffices); every atom is checked against the list -/
def atomize : Nat → List J → Option (List NTm)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, i :: l =>
    match cand (i :: l) with
    | none => none
    | some t =>
      if (i :: l).take t.j.length = t.j then (atomize n ((i :: l).drop t.j.length)).map (t :: ·) else none

/-- the parse is a parse: the atoms' J instructions are the list -/
theorem atomize_j : ∀ (n : Nat) (l : List J) (tl : List NTm), atomize n l = some tl → tl.flatMap NTm.j = l
  | 0, [], tl, h => by simp only [atomize, Option.some.injEq] at h; subst h; rfl
  | n + 1, [], tl, h => by simp only [atomize, Option.some.injEq] at h; subst h; rfl
  | 0, _ :: _, tl, h => by simp [atomize] at h
  | n + 1, i :: l, tl, h => by
    simp only [atomize] at h
    split at h
    · exact absurd h (by simp)
    · rename_i t _
      split at h
      · rename_i hp
        cases hr : atomize n ((i :: l).drop t.j.length) with
        | none => rw [hr] at h; exact absurd h (by simp)
        | some r =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          rw [List.flatMap_cons, atomize_j n _ r hr]
          conv => lhs; rw [← hp]
          exact List.take_append_drop _ _
      · exact absurd h (by simp)

end JT
