/- Exactness: the instruction lists of Proof/Expr.lean ARE the words Gen emits.  `encJ` maps a template instruction to
the word C's own encoders (g1–g5, g10–g12) produce; each lemma says: Gen's emitter appends exactly `template.map encJ`.
Together with Proof/Bridge.lean (C's encoders = nano-v2 `I.enc`, which Enc/Sim tie to Sail) this closes the gap between
the abstract-machine statements of Expr.lean and the generated code. -/
import Nano.V2Self.Proof.Expr
import Nano.V2Self.C.Gen
namespace CallProbe
open C

/-- an Int offset as C's two's-complement UInt64 -/
def iu (z : Int) : UInt64 := UInt64.ofNat (z % 2 ^ 64).toNat

def aluF (op : Nat) : UInt64 × UInt64 :=   -- (funct7, funct3) of g31's table
  if op = 1 then (0, 0) else if op = 2 then (32, 0) else if op = 3 then (1, 0) else if op = 4 then (0, 7)
  else if op = 5 then (0, 6) else if op = 6 then (0, 1) else if op = 7 then (0, 5) else (0, 4)

def encJ : J → UInt64
  | .addi rd rs imm => g10 rd.toUInt64 rs.toUInt64 (iu imm)
  | .ld rd rs off => g11 rd.toUInt64 rs.toUInt64 (iu off)
  | .sd r2 r1 off => g12 r2.toUInt64 r1.toUInt64 (iu off)
  | .jal rd off => g5 rd.toUInt64 (iu (4 * off))
  | .bgeu a b off => g4 7 a.toUInt64 b.toUInt64 (iu (4 * off))
  | .alu op rd a b => g1 (aluF op).1 (aluF op).2 rd.toUInt64 a.toUInt64 b.toUInt64
  | .slli rd rs sh => g2 g_19 1 rd.toUInt64 rs.toUInt64 sh.toUInt64
  | .lbu rd rs off => g2 g_3 4 rd.toUInt64 rs.toUInt64 (iu off)
  | .jalr rd rs => g2 g_103 0 rd.toUInt64 rs.toUInt64 0

theorem g31_exact (o : Buf) (p : Nat) (hp : 1 ≤ p) (hp8 : p ≤ 8) :
    g31 o p.toUInt64 = o ++ (binT p).map encJ := by
  unfold g31 g30
  rcases (by omega : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [binT, encJ, bpush, iu, aluF, g10, g11, g12, g1, g2, g3, g4, g_3, g_19, g_16, g_31, g_35, g_51, g_63, g_99, g_103, g_127, g_4095]

theorem iu_toNat (z : Int) : (iu z).toNat = (z % 2 ^ 64).toNat := by
  unfold iu; simp only [UInt64.toNat_ofNat']; omega

/-- C's jump offset `(b − a) <<< 2` (words a = h + 2 → stub word 1) is the template's `jal x0 (tgt − (q+2))`, tgt = 1 -/
theorem jal_off (q : Nat) (hq : q < 2 ^ 32) :
    ((1 : UInt64) - (UInt64.ofNat q + 2)) <<< 2 = iu (4 * (((1 : Nat) : Int) - ((q : Int) + 2))) := by
  apply UInt64.toNat.inj
  rw [iu_toNat]
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_sub, UInt64.toNat_add, Nat.shiftLeft_eq]
  omega

theorem g22_exact (o : Buf) (d : Nat) (hd : d < 32) (ho : o.length < 2 ^ 32) :
    g22 o d.toUInt64 = o ++ (pushA 1 o.length d).map encJ := by
  unfold g22 g13
  have hh : bsize o = o.length.toUInt64 := rfl
  have := jal_off o.length ho
  have i0 : iu 0 = 0 := by decide
  have i8 : iu 8 = 8 := by decide
  have im8 : iu (-8) = g_0 - 8 := by decide
  have i16 : iu (4 * 2) = 8 := by decide
  simp [pushA, push, encJ, bpush, hh, g10, g12, g4, g2, g3, g5, i0, i8, im8, this, g_908, g_0, g_31, g_35, g_99, g_127, g_4095, g_1023, g_255, g_1, g_111]

section prims
local macro "gsimp" : tactic => `(tactic| simp [encJ, bpush, iu, g10, g11, g12, g1, g2, g3, g4, aluF, g_0, g_3, g_16, g_19, g_31, g_35, g_51, g_63, g_99, g_103, g_127, g_4095, g_15, g_1])

theorem g32_len (o : Buf) (u : UInt64) (ho : o.length < 2 ^ 32) : g32 o 1 u = o ++ (lenT 1 o.length).map encJ := by
  unfold g32; simp only [lenT]; have := g22_exact o 29 (by decide) ho; simpa using this

theorem g32_len3 (o : Buf) (u : UInt64) (ho : o.length < 2 ^ 32) : g32 o 3 u = o ++ (lenT 1 o.length).map encJ := by
  unfold g32; simp only [lenT]; have := g22_exact o 29 (by decide) ho; simpa using this

theorem g32_rd (o : Buf) (u : UInt64) : g32 o 2 u = o ++ rdT.map encJ := by
  unfold g32; simp [rdT]; gsimp

theorem g32_bsize (o : Buf) (u : UInt64) : g32 o 6 u = o ++ bsizeT.map encJ := by
  unfold g32; simp [bsizeT]; gsimp

theorem g32_bget (o : Buf) (u : UInt64) : g32 o 7 u = o ++ bgetT.map encJ := by
  unfold g32 g30; simp [bgetT]; gsimp
end prims

end CallProbe
