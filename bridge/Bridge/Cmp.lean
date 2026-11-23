/- Bridge.Cmp: comparisons.  (1) `Nat.ble` / `Nat.beq` on canonical numerals, from their recursion theorems.
(2) UInt64 `==` (the emitted `@BEq.beq UInt64 (instBEqOfDecidableEq UInt64 instDecidableEqUInt64)`) on encodings,
by a transfer whose theorem has two PROP-TYPED binders (Bool guards `Nat.blt a N = true`): the guard's proof element
is `pt`, which inhabits the guard's denotation `eqv ⟦blt a N⟧ ⟦true⟧` once `blt` is computed (DENOTES-S2's open gap).
Stored theorems (stated with `Nat.zero`/`Nat.succ`): `ble0 : ∀ m, Nat.ble Nat.zero m = true`,
`bleS0 : ∀ n, Nat.ble (Nat.succ n) Nat.zero = false`, `bleSS : ∀ n m, Nat.ble (Nat.succ n) (Nat.succ m) = Nat.ble n m`,
`beq00 : Nat.beq Nat.zero Nat.zero = true`, `beq0S : ∀ m, Nat.beq Nat.zero (Nat.succ m) = false`,
`beqS0 : ∀ n, Nat.beq (Nat.succ n) Nat.zero = false`, `beqSS : ∀ n m, Nat.beq (Nat.succ n) (Nat.succ m) = Nat.beq n m`,
`bltDef : ∀ n m, Nat.blt n m = Nat.ble (Nat.succ n) m`, and
`br_beq : ∀ a b : Nat, Nat.blt a 18446744073709551616 = true → Nat.blt b 18446744073709551616 = true →
  (UInt64.ofNat a == UInt64.ofNat b) = Nat.beq a b`.

STATUS: proved, no sorry. -/
import Bridge.Add

namespace Bridge.Cmp
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota2 Bridge.Asm Bridge.Add

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def tB : E := .const "Bool" []
def tt : E := .const "Bool.true" []
def ff : E := .const "Bool.false" []
def sc (a : E) : E := .app (.const "Nat.succ" []) a
def nz : E := .const "Nat.zero" []
def bin2 (f : String) (a b : E) : E := .app (.app (.const f []) a) b
def nnb : E := .forallE tNat (.forallE tNat tB false) false

variable (M) in
def boolEnc (b : Bool) : S := if b then M.cval "Bool.true" [] else M.cval "Bool.false" []

structure CmpEnv (env : List Const) : Prop where
  bool : HasTy env "Bool" [] (.sort 1)
  btrue : HasTy env "Bool.true" [] tB
  bfalse : HasTy env "Bool.false" [] tB
  ble : HasTy env "Nat.ble" [] nnb
  beq : HasTy env "Nat.beq" [] nnb
  blt : HasTy env "Nat.blt" [] nnb
  ble0 : HasTy env "ble0" [] (piN [(tNat, false)] (eqE 1 tB (bin2 "Nat.ble" nz (.bvar 0)) tt))
  bleS0 : HasTy env "bleS0" [] (piN [(tNat, false)] (eqE 1 tB (bin2 "Nat.ble" (sc (.bvar 0)) nz) ff))
  bleSS : HasTy env "bleSS" [] (piN [(tNat, false), (tNat, false)]
    (eqE 1 tB (bin2 "Nat.ble" (sc (.bvar 1)) (sc (.bvar 0))) (bin2 "Nat.ble" (.bvar 1) (.bvar 0))))
  beq00 : HasTy env "beq00" [] (eqE 1 tB (bin2 "Nat.beq" nz nz) tt)
  beq0S : HasTy env "beq0S" [] (piN [(tNat, false)] (eqE 1 tB (bin2 "Nat.beq" nz (sc (.bvar 0))) ff))
  beqS0 : HasTy env "beqS0" [] (piN [(tNat, false)] (eqE 1 tB (bin2 "Nat.beq" (sc (.bvar 0)) nz) ff))
  beqSS : HasTy env "beqSS" [] (piN [(tNat, false), (tNat, false)]
    (eqE 1 tB (bin2 "Nat.beq" (sc (.bvar 1)) (sc (.bvar 0))) (bin2 "Nat.beq" (.bvar 1) (.bvar 0))))
  bltDef : HasTy env "bltDef" [] (piN [(tNat, false), (tNat, false)]
    (eqE 1 tB (bin2 "Nat.blt" (.bvar 1) (.bvar 0)) (bin2 "Nat.ble" (sc (.bvar 1)) (.bvar 0))))

variable (L : SetLaws O)
include L

theorem bool_mem (HC : CmpEnv env) (ρ : Nat → S) (b : Bool) : O.mem (boolEnc M b) (M.cval "Bool" []) := by
  cases b
  · exact mem_ty M L HC.bfalse (ρ := ρ) .const
  · exact mem_ty M L HC.btrue (ρ := ρ) .const

theorem nnb_app (_H : EncEnv env) (_HC : CmpEnv env) {f : String} (hf : HasTy env f [] nnb) {ρ : Nat → S} {x y : S}
    (hx : O.mem x (M.cval "Nat" [])) (hy : O.mem y (M.cval "Nat" [])) :
    O.mem (O.app (O.app (M.cval f []) x) y) (M.cval "Bool" []) := by
  have dP : D O M.cval ρ nnb _ := .pi .const (fun _ _ => .pi .const (fun _ _ => .const) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (mem_ty M L hf dP) hx (np rfl)) hy (np rfl)

/-- `Nat.ble` on canonical numerals -/
theorem ble_set (H : EncEnv env) (HC : CmpEnv env) (ρ : Nat → S) :
    ∀ a b, O.app (O.app (M.cval "Nat.ble" []) (natEnc M a)) (natEnc M b) = boolEnc M (decide (a ≤ b)) := by
  have hBu := univ1 (M := M) (L := L) H HC.bool ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have hS : ∀ k, natEnc M (k + 1) = O.app (M.cval "Nat.succ" []) (natEnc M k) := fun _ => rfl
  intro a
  induction a with
  | zero =>
    intro b
    obtain ⟨ty, hc, hty⟩ := HC.ble0
    rw [show decide (0 ≤ b) = true by simp]
    exact transferN L M hc (ls := []) hty ρ (.cons .const (hn b) .nil) .const (.app (.app .const .const) .bvar) .const
      hBu (nnb_app (ρ := ρ) L H HC HC.ble (hn 0) (hn b)) (bool_mem L HC ρ true)
  | succ a ih =>
    intro b
    cases b with
    | zero =>
      obtain ⟨ty, hc, hty⟩ := HC.bleS0
      rw [show decide (a + 1 ≤ 0) = false by simp]
      exact transferN L M hc (ls := []) hty ρ (.cons .const (hn a) .nil) .const
        (.app (.app .const (.app .const .bvar)) .const) .const
        hBu (nnb_app (ρ := ρ) L H HC HC.ble (hn (a + 1)) (hn 0)) (bool_mem L HC ρ false)
    | succ b =>
      obtain ⟨ty, hc, hty⟩ := HC.bleSS
      rw [show decide (a + 1 ≤ b + 1) = decide (a ≤ b) by simp, ← ih b]
      exact transferN L M hc (ls := []) hty ρ (.cons .const (hn a) (.cons .const (hn b) .nil)) .const
        (.app (.app .const (.app .const .bvar)) (.app .const .bvar)) (.app (.app .const .bvar) .bvar)
        hBu (nnb_app (ρ := ρ) L H HC HC.ble (hn (a + 1)) (hn (b + 1))) (nnb_app (ρ := ρ) L H HC HC.ble (hn a) (hn b))

/-- `Nat.beq` on canonical numerals -/
theorem beq_set (H : EncEnv env) (HC : CmpEnv env) (ρ : Nat → S) :
    ∀ a b, O.app (O.app (M.cval "Nat.beq" []) (natEnc M a)) (natEnc M b) = boolEnc M (a == b) := by
  have hBu := univ1 (M := M) (L := L) H HC.bool ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  intro a
  induction a with
  | zero =>
    intro b
    cases b with
    | zero =>
      obtain ⟨ty, hc, hty⟩ := HC.beq00
      exact transferN L M hc (ls := []) (ts := []) hty ρ .nil .const (.app (.app .const .const) .const) .const
        hBu (nnb_app (ρ := ρ) L H HC HC.beq (hn 0) (hn 0)) (bool_mem L HC ρ true)
    | succ b =>
      obtain ⟨ty, hc, hty⟩ := HC.beq0S
      rw [show ((0 : Nat) == b + 1) = false by simp]
      exact transferN L M hc (ls := []) hty ρ (.cons .const (hn b) .nil) .const
        (.app (.app .const .const) (.app .const .bvar)) .const
        hBu (nnb_app (ρ := ρ) L H HC HC.beq (hn 0) (hn (b + 1))) (bool_mem L HC ρ false)
  | succ a ih =>
    intro b
    cases b with
    | zero =>
      obtain ⟨ty, hc, hty⟩ := HC.beqS0
      rw [show (a + 1 == (0 : Nat)) = false by simp]
      exact transferN L M hc (ls := []) hty ρ (.cons .const (hn a) .nil) .const
        (.app (.app .const (.app .const .bvar)) .const) .const
        hBu (nnb_app (ρ := ρ) L H HC HC.beq (hn (a + 1)) (hn 0)) (bool_mem L HC ρ false)
    | succ b =>
      obtain ⟨ty, hc, hty⟩ := HC.beqSS
      rw [show (a + 1 == b + 1) = (a == b) by simp, ← ih b]
      exact transferN L M hc (ls := []) hty ρ (.cons .const (hn a) (.cons .const (hn b) .nil)) .const
        (.app (.app .const (.app .const .bvar)) (.app .const .bvar)) (.app (.app .const .bvar) .bvar)
        hBu (nnb_app (ρ := ρ) L H HC HC.beq (hn (a + 1)) (hn (b + 1))) (nnb_app (ρ := ρ) L H HC HC.beq (hn a) (hn b))

/-- `Nat.blt` on canonical numerals -/
theorem blt_set (H : EncEnv env) (HC : CmpEnv env) (ρ : Nat → S) (a b : Nat) :
    O.app (O.app (M.cval "Nat.blt" []) (natEnc M a)) (natEnc M b) = boolEnc M (decide (a < b)) := by
  have hBu := univ1 (M := M) (L := L) H HC.bool ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  obtain ⟨ty, hc, hty⟩ := HC.bltDef
  have key : O.app (O.app (M.cval "Nat.blt" []) (natEnc M a)) (natEnc M b) =
      O.app (O.app (M.cval "Nat.ble" []) (natEnc M (a + 1))) (natEnc M b) :=
    transferN L M hc (ls := []) hty ρ (.cons .const (hn a) (.cons .const (hn b) .nil)) .const
    (.app (.app .const .bvar) .bvar) (.app (.app .const (.app .const .bvar)) .bvar)
    hBu (nnb_app (ρ := ρ) L H HC HC.blt (hn a) (hn b)) (nnb_app (ρ := ρ) L H HC HC.ble (hn (a + 1)) (hn b))
  rw [key]
  exact (ble_set L H HC ρ (a + 1) b).trans (by simp [Nat.lt_iff_add_one_le])

end Bridge.Cmp
