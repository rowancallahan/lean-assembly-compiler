/- Machine bridge (Opus box E): the remaining closing fragments under the heap contract (HeapEV's Fin1/Fin2):
BIN (`binT op`, all 8 ops) and RD (`rdT`, input bytes kept by `Inv`). -/
import Nano.V2Self.Proof.Machine.EVXL
namespace Templates
open CallProbe

def aluF2 (op : Nat) : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) := fun a b _ H => some (aluf op a b, H)

def rdF1 (c29 : UInt64) (inp : Nat → UInt64) : UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun i _ H => some (if i.toNat < c29.toNat then inp i.toNat else 0, H)

/-- the input facts the invariant carries: base t3 = c28, length t4 = c29, bytes `inp` -/
def InpOK (Inv : St → Prop) (c28 c29 : UInt64) (inp : Nat → UInt64) : Prop :=
  ∀ s, Inv s → s.x 28 = c28 ∧ s.x 29 = c29 ∧ (∀ i, i < c29.toNat → lbm s.m (c28.toNat + i) = inp i) ∧
    c28.toNat + c29.toNat < 2 ^ 63

end Templates
