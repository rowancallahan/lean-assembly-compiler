/- The J-level layout and safe runs, machine-independent (split out of SimW/SimX: no Sail model here).
`LayW`: code base and words, work cells `[lo, hi)`, input/output bytes, the entry memory `m0`; `wok`/`io`/`bok`/`sok`:
which addresses a J load/store may touch; `Safe`/`SafeX`: the side conditions of one J step that a target needs;
`SStar`/`SStarX`: J runs whose every step satisfies them.  Names stay in namespace `SimW`. -/
import Nano.V2Self.Proof.Machine.Call

namespace SimW

structure LayW where
  base : Nat
  W : List Nat
  lo : Nat
  hi : Nat
  /-- input bytes `[ib, ib + il)` (read by lbu) and output bytes `[ob, ob + ol)` (written by sb) -/
  ib : Nat := 0
  il : Nat := 0
  ob : Nat := 0
  ol : Nat := 0
  /-- the Sail memory at the start: bytes outside the work cells and the output bytes keep it -/
  m0 : Nat → Option (BitVec 8) := fun _ => none

def wok (K : LayW) (a : Nat) : Prop := K.lo ≤ a ∧ a + 8 ≤ K.hi ∧ a % 8 = 0

/-- an output byte -/
def outB (K : LayW) (a : Nat) : Prop := K.ob ≤ a ∧ a < K.ob + K.ol
/-- an input or output byte -/
def io (K : LayW) (a : Nat) : Prop := (K.ib ≤ a ∧ a < K.ib + K.il) ∨ outB K a
/-- a byte lbu may read: in a work cell, or an input/output byte -/
def bok (K : LayW) (a : Nat) : Prop := wok K (a - a % 8) ∨ io K a
/-- a byte sb may write: in a work cell, or an output byte -/
def sok (K : LayW) (a : Nat) : Prop := wok K (a - a % 8) ∨ outB K a

/-- the side conditions of one J step that the Sail step needs (ranges, no wrap, work cells, aligned return) -/
def Safe (K : LayW) (C : List CallProbe.J) : Nat × CallProbe.St → Prop
  | (pc, s) => match C[pc]? with
    | some (.addi rd rs imm) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ imm ∧ imm < 2048 ∧
        0 ≤ ((s.x rs).toNat : Int) + imm ∧ ((s.x rs).toNat : Int) + imm < 2 ^ 64
    | some (.ld rd rs off) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧
        0 ≤ ((s.x rs).toNat : Int) + off ∧ wok K (CallProbe.ea (s.x rs) off)
    | some (.sd b a off) => b < 32 ∧ a < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧
        0 ≤ ((s.x a).toNat : Int) + off ∧ wok K (CallProbe.ea (s.x a) off)
    | some (.bgeu a b o) => a < 32 ∧ b < 32 ∧ (o = 2 ∨ o = 3 ∨ o = 4)
    | some (.beq a b o) => a < 32 ∧ b < 32 ∧ o = 2
    | some (.bltu a b o) => a < 32 ∧ b < 32 ∧ o = 2
    | some (.jal rd off) => rd < 32 ∧ -2 ^ 18 ≤ off ∧ off < 2 ^ 18 ∧ 0 ≤ (pc : Int) + off ∧ (pc : Int) + off < C.length
    | some (.jalr rd rs) => rd = 0 ∧ rs < 32 ∧ ∃ j, (s.x rs).toNat = K.base + 4 * j
    | some (.alu op rd a b) => rd < 32 ∧ a < 32 ∧ b < 32 ∧ (1 ≤ op ∧ op ≤ 8) ∧ rd ≠ 0
    | some (.slli rd rs sh) => rd < 32 ∧ rs < 32 ∧ sh < 64
    | some (.lbu rd rs off) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧ 0 ≤ ((s.x rs).toNat : Int) + off ∧
        bok K (CallProbe.ea (s.x rs) off)
    | _ => False

/-- J runs whose every step is `Safe` -/
inductive SStar (K : LayW) (C : List CallProbe.J) : Nat × CallProbe.St → Nat × CallProbe.St → Prop
  | refl (a) : SStar K C a a
  | head {a b c} : Safe K C a → CallProbe.step C a = some b → SStar K C b c → SStar K C a c

def SafeX (K : LayW) (C : List CallProbe.J) : Nat × CallProbe.St → Prop
  | (pc, s) => match C[pc]? with
    | some (.addi rd rs imm) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ imm ∧ imm < 2048 ∧
        0 ≤ ((s.x rs).toNat : Int) + imm ∧ ((s.x rs).toNat : Int) + imm < 2 ^ 64
    | some (.ld rd rs off) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧
        0 ≤ ((s.x rs).toNat : Int) + off ∧ wok K (CallProbe.ea (s.x rs) off)
    | some (.sd b a off) => b < 32 ∧ a < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧
        0 ≤ ((s.x a).toNat : Int) + off ∧ wok K (CallProbe.ea (s.x a) off)
    | some (.bgeu a b o) => a < 32 ∧ b < 32 ∧ (o = 2 ∨ o = 3 ∨ o = 4)
    | some (.beq a b o) => a < 32 ∧ b < 32 ∧ (o = 2 ∨ o = 7)
    | some (.bltu a b o) => a < 32 ∧ b < 32 ∧ o = 2
    | some (.jal rd off) => rd < 32 ∧ -2 ^ 18 ≤ off ∧ off < 2 ^ 18 ∧ 0 ≤ (pc : Int) + off ∧ (pc : Int) + off < C.length
    | some (.jalr rd rs) => rd = 0 ∧ rs < 32 ∧ ∃ j, (s.x rs).toNat = K.base + 4 * j
    | some (.alu op rd a b) => rd < 32 ∧ a < 32 ∧ b < 32 ∧ (1 ≤ op ∧ op ≤ 8) ∧ rd ≠ 0
    | some (.slli rd rs sh) => rd < 32 ∧ rs < 32 ∧ sh < 64
    | some (.lbu rd rs off) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧ 0 ≤ ((s.x rs).toNat : Int) + off ∧
        bok K (CallProbe.ea (s.x rs) off)
    | some (.srli rd rs sh) => rd < 32 ∧ rs < 32 ∧ sh < 64
    | some (.bne a b o) => a < 32 ∧ b < 32 ∧ o = 4
    | some (.sb b a off) => b < 32 ∧ a < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧ 0 ≤ ((s.x a).toNat : Int) + off ∧
        sok K (CallProbe.ea (s.x a) off)
    | none => False

theorem safeX_of {K : LayW} {C : List CallProbe.J} {a : Nat × CallProbe.St} (h : Safe K C a) : SafeX K C a := by
  obtain ⟨pc, s⟩ := a
  simp only [Safe] at h; simp only [SafeX]
  cases hc : C[pc]? with
  | none => rw [hc] at h; exact h.elim
  | some i =>
    rw [hc] at h
    cases i <;> simp only at h ⊢ <;> first | exact h | exact h.elim | exact ⟨h.1, h.2.1, Or.inl h.2.2⟩

inductive SStarX (K : LayW) (C : List CallProbe.J) : Nat × CallProbe.St → Nat × CallProbe.St → Prop
  | refl (a) : SStarX K C a a
  | head {a b c} : SafeX K C a → CallProbe.step C a = some b → SStarX K C b c → SStarX K C a c

theorem SStarX.of {K : LayW} {C : List CallProbe.J} {a b : Nat × CallProbe.St} (h : SStar K C a b) : SStarX K C a b := by
  induction h with
  | refl a => exact .refl a
  | head hS hs _ ih => exact .head (safeX_of hS) hs ih

theorem SStarX.trans {K : LayW} {C : List CallProbe.J} {a b c : Nat × CallProbe.St} (h1 : SStarX K C a b)
    (h2 : SStarX K C b c) : SStarX K C a c := by
  induction h1 with
  | refl => exact h2
  | head hS hs _ ih => exact .head hS hs (ih h2)

end SimW
