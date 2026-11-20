/- Machine bridge (Opus box E): the start code on the J machine, shared definitions: `Entry` (the state at main's
entry: heap base t5 = a2 + 16, expression stack t6 = sp rounded down to 8, ra / s0 saved at a2 / a2 + 8, input
registers t3 / t4), the copy loop `loopJ`, `KeepT`, `At` helpers.  Run theorems: StartSafe.lean / StartAllS.lean. -/
import Nano.V2Self.Proof.Machine.StartCode
namespace Templates
open CallProbe

theorem At.get {C : List J} {h : Nat} {l : List J} (hC : At C h l) (j : Nat) (hj : j < l.length) :
    C[h + j]? = l[j]? := hC j hj

/-- the state at main's entry -/
structure Entry (s0 s1 : St) (S : Nat) : Prop where
  x0 : s1.x 0 = 0
  x1 : s1.x 1 = UInt64.ofNat (s0.b + s0.w * (S + 12))
  x8 : s1.x 8 = s0.x 8
  x12 : s1.x 12 = s0.x 12
  x13 : s1.x 13 = s0.x 13
  x28 : s1.x 28 = s0.x 10
  x29 : s1.x 29 = s0.x 11
  x30 : s1.x 30 = UInt64.ofNat ((s0.x 12).toNat + 16)
  x31 : s1.x 31 = (s0.x 2 >>> 3) <<< 3
  m : s1.m = upd (upd s0.m (s0.x 12).toNat (s0.x 1)) ((s0.x 12).toNat + 8) (s0.x 8)
  b : s1.b = s0.b
  wk : s1.wk = s0.wk

/-- the copy loop of the start code (words S+21 .. S+27) -/
def loopJ : List J := [.beq 7 0 7, .ld 15 6 0, .sb 15 14 0, .addi 6 6 8, .addi 14 14 1, .addi 7 7 (-1), .jal 0 (-6)]

theorem At.dt {C : List J} {p : Nat} {l : List J} (h : At C p l) (k n : Nat) (hk : k + n ≤ l.length) :
    At C (p + k) ((l.drop k).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [Nat.add_assoc, h (k + i) (by omega)]
  simp [List.getElem?_take, show i < n by omega]

theorem Star.pc_step {C : List J} {a : Nat × St} {p p' : Nat} {t : St} (h : step C a = some (p, t)) (e : p = p') :
    step C a = some (p', t) := e ▸ h

/-- the cells the tail reads after main: ra / s0 save slots and the result buffer's byte words -/
def KeepT (A2 P N : Nat) (c : Nat) : Prop := c = A2 ∨ c = A2 + 8 ∨ ∃ j, j < N ∧ c = P + 16 + 8 * j

end Templates
