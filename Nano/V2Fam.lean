/- nano v2, increment 1: every record of `Nano.V2.genR p` is in one of v1's record families (`Nano.F.Fam`), so v1's
Sail refinement (`Nano/StackSim.lean`) runs it unchanged: the `if` node adds NO new instruction. -/
import Nano.StackFam
import Nano.V2Gen

namespace Nano.V2
open Proven Nano Nano.F

theorem len_code (o : SOp) : o.code.length % 4 = 0 := by
  cases o <;> simp [SOp.code, ld, sd, addSp, r, push, li, binop]

theorem len_ops : ∀ (ops : List SOp), (opsCode ops).length % 4 = 0
  | [] => rfl
  | o :: os => by simp only [opsCode, List.length_append]; have := len_code o; have := len_ops os; omega

theorem af_ops : ∀ (ops : List SOp), (∀ o ∈ ops, allFam o.code = true) → allFam (opsCode ops) = true
  | [], _ => rfl
  | o :: os, h => by
    simp only [opsCode]; rw [allFam_append _ _ (len_code o), h o (by simp), af_ops os (fun x hx => h x (by simp [hx]))]; rfl

theorem af_dup (j : Nat) : allFam (SOp.dup j).code = true := by
  simp only [SOp.code]; rw [allFam_append _ _ (len_ld j), af_ld, af_push]; rfl
theorem af_lit (n : UInt64) : allFam (SOp.lit n).code = true := by
  simp only [SOp.code]; rw [allFam_append _ _ (len_li n), af_li, af_push]; rfl
theorem af_shr (k : Nat) (hk : k < 64) : allFam (SOp.shr k).code = true := by
  simp only [SOp.code, ld, sd, r, List.cons_append, List.nil_append, allFam, Fam]
  have : (k.toUInt8 < 64) = True := by simp [Nat.toUInt8, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]; omega
  simp [this]
theorem af_bin (k : Nat) (hk : k = 24 ∨ k = 32 ∨ k = 40) : allFam (SOp.bin k).code = true := by
  simp only [SOp.code]; rcases hk with rfl | rfl | rfl <;> exact af_binop _ (by decide)
theorem af_slide (k : Nat) : allFam (SOp.slide k).code = true := by
  simp only [SOp.code, List.append_assoc]
  rw [allFam_append _ _ (len_ld 0), allFam_append _ _ (len_addSp k), af_ld, af_addSp, af_sd]; rfl

theorem af_bor : allFam SOp.bor.code = true := by decide
theorem af_shl (k : Nat) (hk : k < 64) : allFam (SOp.shl k).code = true := by
  simp only [SOp.code, ld, sd, r, List.cons_append, List.nil_append, allFam, Fam]
  have : (k.toUInt8 < 64) = True := by simp [Nat.toUInt8, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]; omega
  simp [this]

theorem af_and : ∀ o ∈ andOps, allFam o.code = true := by
  intro o ho; simp only [andOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | exact af_dup _ | exact af_bor | exact af_bin _ (by decide) | exact af_slide _

theorem af_bit (o : BOp) : allFam (opsCode (bitOps o)) = true := by
  apply af_ops
  cases o <;> simp only [bitOps, xorOps, List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] <;> intro o ho
  · exact af_and o ho
  · subst ho; exact af_bor
  · rcases ho with rfl | rfl | rfl | rfl | rfl | ho | ho
    · exact af_dup _
    · exact af_dup _
    · exact af_bor
    · exact af_dup _
    · exact af_dup _
    · exact af_and o ho
    · rcases ho with rfl | rfl
      · exact af_bin _ (by decide)
      · exact af_slide _

theorem af_shop (l : Bool) (k : Nat) : allFam (opsCode [shOp l (k % 64)]) = true := by
  have := Nat.mod_lt k (show 64 > 0 by decide)
  apply af_ops; intro o ho; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; subst ho
  cases l
  · exact af_shr _ this
  · exact af_shl _ this

theorem af_ltu : ∀ o ∈ ltuOps, allFam o.code = true := by
  intro o ho; simp only [ltuOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | exact af_dup _ | exact af_lit _ | exact af_shr _ (by decide) | exact af_bin _ (by decide) | exact af_slide _

theorem af_cmp {k : Cmp} : allFam (opsCode (cmpOps k)) = true := by
  apply af_ops
  cases k <;> simp only [cmpOps, eqOps, ltsOps, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] <;>
    intro o ho
  all_goals first
    | exact af_ltu o ho
    | (rcases ho with rfl | rfl | ho
       · exact af_bin _ (by decide)
       · exact af_lit _
       · exact af_ltu o ho)
    | (rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | ho | ho
       · exact af_dup _
       · exact af_lit _
       · exact af_bin _ (by decide)
       · exact af_dup _
       · exact af_lit _
       · exact af_bin _ (by decide)
       · exact af_ltu o ho
       · simp at ho; subst ho; exact af_slide _)

theorem af_sel : allFam (opsCode selOps) = true := by
  apply af_ops; intro o ho; simp only [selOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact af_dup _
  all_goals exact af_bin _ (by decide)

mutual
theorem len_genE : ∀ (sc : List Nat) (d : Nat) (e : E), (genE sc d e).length % 4 = 0
  | _, _, .num n => by simp only [genE, List.length_append]; have := len_li n; have := len_push; omega
  | _, _, .var _ => by simp only [genE, List.length_append]; have := len_push; simp [ld, r]; omega
  | sc, d, .add a b => by
    simp only [genE, List.length_append]; have := len_genE sc d a; have := len_genE sc (d + 1) b
    have := len_binop 24; omega
  | sc, d, .sub a b => by
    simp only [genE, List.length_append]; have := len_genE sc d a; have := len_genE sc (d + 1) b
    have := len_binop 32; omega
  | sc, d, .mul a b => by
    simp only [genE, List.length_append]; have := len_genE sc d a; have := len_genE sc (d + 1) b
    have := len_binop 40; omega
  | sc, d, .let_ v b => by
    simp only [genE, List.length_append]; have := len_genE sc d v; have := len_genE (d :: sc) (d + 1) b
    simp [ld, addSp, sd, r]; omega
  | sc, d, .call b as => by
    simp only [genE, List.length_append]; have := len_genA sc d as
    have := len_genE (mkSc (cnt as) d) (d + cnt as) b
    simp [ld, addSp, sd, r]; omega
  | sc, d, .ite k a b t e => by
    simp only [genE]
    have := len_genE sc d t; have := len_genE sc (d + 1) b; have := len_genE sc (d + 2) a
    have := len_genE sc d e; have := len_genE sc (d + 1) a; have := len_genE sc (d + 2) b
    have := len_genE sc (d + 2) e; have := len_genE sc (d + 2) t
    have := len_ops (cmpOps k); have := len_ops selOps
    split <;> simp only [List.length_append] <;> omega
  | sc, d, .bit o a b => by
    simp only [genE, List.length_append]; have := len_genE sc d a; have := len_genE sc (d + 1) b
    have := len_ops (bitOps o); omega
  | sc, d, .sh l k a => by
    simp only [genE, List.length_append]; have := len_genE sc d a; have := len_ops [shOp l (k % 64)]; omega
  | _, _, .anil => by simp [genE]
  | _, _, .acons _ _ => by simp [genE]
theorem len_genA : ∀ (sc : List Nat) (d : Nat) (e : E), (genA sc d e).length % 4 = 0
  | sc, d, .acons e r => by
    simp only [genA, List.length_append]; have := len_genE sc d e; have := len_genA sc (d + 1) r; omega
  | _, _, .num _ => by simp [genA] | _, _, .var _ => by simp [genA] | _, _, .add _ _ => by simp [genA]
  | _, _, .sub _ _ => by simp [genA] | _, _, .mul _ _ => by simp [genA] | _, _, .let_ _ _ => by simp [genA]
  | _, _, .call _ _ => by simp [genA] | _, _, .anil => by simp [genA] | _, _, .ite _ _ _ _ _ => by simp [genA]
  | _, _, .bit _ _ _ => by simp [genA] | _, _, .sh _ _ _ => by simp [genA]
end

mutual
theorem af_genE : ∀ (sc : List Nat) (d : Nat) (e : E), allFam (genE sc d e) = true
  | _, _, .num n => by simp only [genE]; rw [allFam_append _ _ (len_li n), af_li, af_push]; rfl
  | _, _, .var _ => by simp only [genE]; rw [allFam_append _ _ (len_ld _), af_ld, af_push]; rfl
  | sc, d, .add a b => by
    simp only [genE]
    rw [allFam_append _ _ (by have := len_genE sc d a; have := len_genE sc (d + 1) b; simp; omega),
      allFam_append _ _ (len_genE sc d a), af_genE sc d a, af_genE sc (d + 1) b, af_binop 24 (by decide)]; rfl
  | sc, d, .sub a b => by
    simp only [genE]
    rw [allFam_append _ _ (by have := len_genE sc d a; have := len_genE sc (d + 1) b; simp; omega),
      allFam_append _ _ (len_genE sc d a), af_genE sc d a, af_genE sc (d + 1) b, af_binop 32 (by decide)]; rfl
  | sc, d, .mul a b => by
    simp only [genE]
    rw [allFam_append _ _ (by have := len_genE sc d a; have := len_genE sc (d + 1) b; simp; omega),
      allFam_append _ _ (len_genE sc d a), af_genE sc d a, af_genE sc (d + 1) b, af_binop 40 (by decide)]; rfl
  | sc, d, .let_ v b => by
    simp only [genE, List.append_assoc]
    rw [allFam_append _ _ (len_genE sc d v), allFam_append _ _ (len_genE (d :: sc) (d + 1) b),
      allFam_append _ _ (len_ld 0), allFam_append _ _ (len_addSp 1), af_genE sc d v, af_genE (d :: sc) (d + 1) b,
      af_ld, af_addSp, af_sd]; rfl
  | sc, d, .call b as => by
    simp only [genE, List.append_assoc]
    rw [allFam_append _ _ (len_genA sc d as), allFam_append _ _ (len_genE (mkSc (cnt as) d) (d + cnt as) b),
      allFam_append _ _ (len_ld 0), allFam_append _ _ (len_addSp _), af_genA sc d as,
      af_genE (mkSc (cnt as) d) (d + cnt as) b, af_ld, af_addSp, af_sd]; rfl
  | sc, d, .ite k a b t e => by
    simp only [genE]
    have l1 := len_genE sc d t; have l2 := len_genE sc (d + 1) b; have l3 := len_genE sc (d + 2) a
    have l4 := len_genE sc d e; have l5 := len_genE sc (d + 1) a; have l6 := len_genE sc (d + 2) b
    have l7 := len_genE sc (d + 2) e; have l8 := len_genE sc (d + 2) t
    have l9 := len_ops (cmpOps k)
    split
    · rw [allFam_append _ _ (by simp only [List.length_append]; omega), allFam_append _ _ (by simp only [List.length_append]; omega),
        allFam_append _ _ (by simp only [List.length_append]; omega), allFam_append _ _ (by simp only [List.length_append]; omega),
        allFam_append _ _ l1, af_genE sc d t, af_genE sc (d + 1) b, af_genE sc (d + 2) a, af_cmp, af_genE sc (d + 2) e, af_sel]; rfl
    · rw [allFam_append _ _ (by simp only [List.length_append]; omega), allFam_append _ _ (by simp only [List.length_append]; omega),
        allFam_append _ _ (by simp only [List.length_append]; omega), allFam_append _ _ (by simp only [List.length_append]; omega),
        allFam_append _ _ l4, af_genE sc d e, af_genE sc (d + 1) a, af_genE sc (d + 2) b, af_cmp, af_genE sc (d + 2) t, af_sel]; rfl
  | sc, d, .bit o a b => by
    simp only [genE]
    rw [allFam_append _ _ (by have := len_genE sc d a; have := len_genE sc (d + 1) b; simp; omega),
      allFam_append _ _ (len_genE sc d a), af_genE sc d a, af_genE sc (d + 1) b, af_bit]; rfl
  | sc, d, .sh l k a => by
    simp only [genE]; rw [allFam_append _ _ (len_genE sc d a), af_genE sc d a, af_shop]; rfl
  | _, _, .anil => by simp [genE, allFam]
  | _, _, .acons _ _ => by simp [genE, allFam]
theorem af_genA : ∀ (sc : List Nat) (d : Nat) (e : E), allFam (genA sc d e) = true
  | sc, d, .acons e r => by
    simp only [genA]; rw [allFam_append _ _ (len_genE sc d e), af_genE sc d e, af_genA sc (d + 1) r]; rfl
  | _, _, .num _ => by simp [genA, allFam] | _, _, .var _ => by simp [genA, allFam]
  | _, _, .add _ _ => by simp [genA, allFam] | _, _, .sub _ _ => by simp [genA, allFam]
  | _, _, .mul _ _ => by simp [genA, allFam] | _, _, .let_ _ _ => by simp [genA, allFam]
  | _, _, .call _ _ => by simp [genA, allFam] | _, _, .anil => by simp [genA, allFam]
  | _, _, .ite _ _ _ _ _ => by simp [genA, allFam]
  | _, _, .bit _ _ _ => by simp [genA, allFam] | _, _, .sh _ _ _ => by simp [genA, allFam]
end

/-- **every record of `genR p` is in a family** -/
theorem af_genR (p : Nano.V2.Prog) : allFam (genR p) = true := by
  simp only [genR, List.append_assoc]
  obtain ⟨h1, h2⟩ := af_pro p.1
  rw [allFam_append _ _ (by decide), allFam_append _ _ (by decide), allFam_append _ _ (by decide),
    allFam_append _ _ h2, allFam_append _ _ (len_genE _ _ _), allFam_append _ _ (len_ld 0),
    allFam_append _ _ (by decide), h1, af_genE, af_ld, af_wr8]; rfl


end Nano.V2
