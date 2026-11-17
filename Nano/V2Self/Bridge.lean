/- Nano/V2Self: the rewritten stage texts equal the Nano/V2S stages (Testing/notes/NANO_V2_CHECKPOINT.md).
Assembler, expander: renames, hex literals as constants and `let` reshaping only. -/
import Nano.V2Self.Asm
import Nano.V2Self.Expand
import Nano.V2S.Asm
import Nano.V2S.Expand

theorem a0_eq : a0 = Nano.V2S.ax0 := rfl
theorem a1_eq : a1 = Nano.V2S.ax1 := rfl
theorem a2_eq : a2 = Nano.V2S.ax2 := rfl
theorem a3_eq (p q t : UInt64) : a3 p q t = Nano.V2S.ax3 p q t := by
  unfold a3 Nano.V2S.ax3; simp only [k0, k128, k240, k64, k2]

theorem a4_eq : ∀ (n : Nat) (x : List UInt8) (i : UInt64) (o : List UInt8), a4 n x i o = Nano.V2S.asmL n x i o
  | 0, x, i, o => rfl
  | n + 1, x, i, o => by
    unfold a4 Nano.V2S.asmL
    simp only [a0_eq, a1_eq, a2_eq, a3_eq, a4_eq n]
    rfl

theorem a5_eq (x : List UInt8) : a5 x = Nano.V2S.asmV x := a4_eq _ _ _ _

theorem e0_eq (p q : UInt64) (o : List UInt8) : e0 p q o = Nano.V2S.mexpOp p q o := rfl

theorem e1_eq : ∀ (n : Nat) (x : List UInt8) (i : UInt64) (o : List UInt8), e1 n x i o = Nano.V2S.mexpL n x i o
  | 0, x, i, o => rfl
  | n + 1, x, i, o => by
    unfold e1 Nano.V2S.mexpL
    simp only [e0_eq, e1_eq n]
    rfl

theorem e2_eq (x : List UInt8) : e2 x = Nano.V2S.mexpV x := e1_eq _ _ _ _
