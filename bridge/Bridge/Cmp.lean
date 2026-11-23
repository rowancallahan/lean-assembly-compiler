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

namespace Bridge.Cmp
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota2 Bridge.Asm Bridge.Add

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def nLit : E := litNat UInt64.size
/-- the emitted UInt64 `==`: `@BEq.beq UInt64 (instBEqOfDecidableEq UInt64 instDecidableEqUInt64) a b` -/
def beqU (a b : E) : E :=
  .app (.app (.app (.app (.const "BEq.beq" [0]) tU)
    (.app (.app (.const "instBEqOfDecidableEq" [0]) tU) (.const "instDecidableEqUInt64" []))) a) b
def guard (a : E) : E := eqE 1 tB (bin2 "Nat.blt" a nLit) tt

structure BeqEnv (env : List Const) : Prop where
  beqC : HasTy env "BEq" [0] (.forallE (.sort 1) (.sort 1) false)
  deq : HasTy env "DecidableEq" [1] (.forallE (.sort 1) (.sort 1) false)
  beqH : HasTy env "BEq.beq" [0] (.forallE (.sort 1) (.forallE (.app (.const "BEq" [0]) (.bvar 0))
    (.forallE (.bvar 1) (.forallE (.bvar 2) tB false) false) false) false)
  ofDec : HasTy env "instBEqOfDecidableEq" [0] (.forallE (.sort 1) (.forallE (.app (.const "DecidableEq" [1]) (.bvar 0))
    (.app (.const "BEq" [0]) (.bvar 1)) false) false)
  decU : HasTy env "instDecidableEqUInt64" [] (.app (.const "DecidableEq" [1]) tU)
  brBeq : HasTy env "br_beq" [] (piN [(tNat, false), (tNat, false), (guard (.bvar 1), false), (guard (.bvar 1), false)]
    (eqE 1 tB (beqU (ofN (.bvar 3)) (ofN (.bvar 2))) (bin2 "Nat.beq" (.bvar 3) (.bvar 2))))

variable (L : SetLaws O)
include L

/-- `BEq.beq UInt64 inst X Y ∈ Bool` -/
theorem beqU_mem (H : EncEnv env) (_HC : CmpEnv env) (HB : BeqEnv env) {ρ : Nat → S} {X Y : S}
    (hX : O.mem X (M.cval "UInt64" [])) (hY : O.mem Y (M.cval "UInt64" [])) :
    O.mem (O.app (O.app (O.app (O.app (M.cval "BEq.beq" [0]) (M.cval "UInt64" []))
      (O.app (O.app (M.cval "instBEqOfDecidableEq" [0]) (M.cval "UInt64" [])) (M.cval "instDecidableEqUInt64" []))) X) Y)
      (M.cval "Bool" []) := by
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have dD : D O M.cval ρ (.app (.const "DecidableEq" [1]) tU) _ := .app .const .const
  have hDec := mem_ty M L HB.decU dD
  have dI : D O M.cval ρ (.forallE (.sort 1) (.forallE (.app (.const "DecidableEq" [1]) (.bvar 0))
      (.app (.const "BEq" [0]) (.bvar 1)) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.app (M.cval "DecidableEq" [1]) a) fun _ => O.app (M.cval "BEq" [0]) a) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .app .const .bvar) (np rfl)) (np rfl)
  have hI := L.app_mem_piR (L.app_mem_piR (mem_ty M L HB.ofDec dI) hUu (np rfl)) hDec (np rfl)
  have dH : D O M.cval ρ (.forallE (.sort 1) (.forallE (.app (.const "BEq" [0]) (.bvar 0))
      (.forallE (.bvar 1) (.forallE (.bvar 2) tB false) false) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.app (M.cval "BEq" [0]) a) fun _ => O.piR 1 a fun _ =>
        O.piR 1 a fun _ => M.cval "Bool" []) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar (fun _ _ => .const)
      (np rfl)) (np rfl)) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HB.beqH dH) hUu (np rfl)) hI (np rfl))
    hX (np rfl)) hY (np rfl)

/-- the literal `18446744073709551616` denotes `natEnc 2^64` -/
theorem nLit_D (H : EncEnv env) (HL : LitEnv env) (HN : InstN env)
    (hb : HasTy env "br_litN" [] (piN [(tNat, false)] (eqE 1 tNat
      (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0)))
      (.bvar 0)))) (ρ : Nat → S) : D O M.cval ρ nLit (natEnc M UInt64.size) := by
  obtain ⟨R, hR⟩ : ∃ R, D O M.cval ρ nLit R :=
    ⟨_, .app (.app (.app .const .const) (lit_denotes M ρ _)) (.app .const (lit_denotes M ρ _))⟩
  have := litN_field (M := M) (ρ := ρ) L H HL HN hb (k := UInt64.size) (R := R) hR
  rwa [this] at hR

/-- **the guard's proof element**: for `a < 2^64`, `pt` inhabits `⟦Nat.blt a 2^64 = true⟧` -/
theorem guard_mem (H : EncEnv env) (HL : LitEnv env) (HN : InstN env) (HC : CmpEnv env)
    (hb : HasTy env "br_litN" [] (piN [(tNat, false)] (eqE 1 tNat
      (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0)))
      (.bvar 0)))) {ρ : Nat → S} {i a : Nat} (hi : ρ i = natEnc M a) (ha : a < UInt64.size) :
    ∃ G, D O M.cval ρ (guard (.bvar i)) G ∧ O.mem O.pt G := by
  have hBu := univ1 (M := M) (L := L) H HC.bool ρ
  have hlt := blt_set (M := M) L H HC ρ a UInt64.size
  rw [show decide (a < UInt64.size) = true by simpa using ha] at hlt
  have hblt : O.mem (O.app (O.app (M.cval "Nat.blt" []) (natEnc M a)) (natEnc M UInt64.size)) (M.cval "Bool" []) := by
    rw [hlt]; exact bool_mem L HC ρ true
  refine ⟨_, .app (.app (.app .const .const) (.app (.app .const .bvar) (nLit_D L H HL HN hb ρ))) .const, ?_⟩
  rw [hi, M.eq_equality 1 ρ _ _ _ _ .const hBu hblt (mem_ty M L HC.btrue (ρ := ρ) .const)]
  exact L.pt_mem_eqv (by rw [hlt]; rfl)

/-- **UInt64 `==` on encodings** -/
theorem beqU_set (H : EncEnv env) (HL : LitEnv env) (HN : InstN env) (HC : CmpEnv env) (HB : BeqEnv env)
    (hb : HasTy env "br_litN" [] (piN [(tNat, false)] (eqE 1 tNat
      (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0)))
      (.bvar 0)))) (ρ : Nat → S) (x y : UInt64) :
    O.app (O.app (O.app (O.app (M.cval "BEq.beq" [0]) (M.cval "UInt64" []))
      (O.app (O.app (M.cval "instBEqOfDecidableEq" [0]) (M.cval "UInt64" [])) (M.cval "instDecidableEqUInt64" [])))
      (encM M (.w x))) (encM M (.w y)) = boolEnc M (x == y) := by
  have hBu := univ1 (M := M) (L := L) H HC.bool ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "UInt64.ofNat" []) a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  let ρ2 := push (natEnc M y.toNat) (push (natEnc M x.toNat) ρ)
  obtain ⟨G1, hG1, hp1⟩ := guard_mem (ρ := ρ2) (i := 1) L H HL HN HC hb rfl x.toNat_lt_size
  obtain ⟨G2, hG2, hp2⟩ := guard_mem (ρ := push O.pt ρ2) (i := 1) L H HL HN HC hb rfl y.toNat_lt_size
  obtain ⟨ty, hc, hty⟩ := HB.brBeq
  have key := transferN L M hc (ls := []) hty ρ
    (.cons .const (hn _) (.cons .const (hn _) (.cons hG1 hp1 (.cons hG2 hp2 .nil)))) .const
    (.app (.app (.app (.app .const .const) (.app (.app .const .const) .const)) (.app .const .bvar)) (.app .const .bvar))
    (.app (.app .const .bvar) .bvar) hBu
    (beqU_mem (ρ := ρ) L H HC HB (ofMem _ (hn _)) (ofMem _ (hn _)))
    (nnb_app (ρ := ρ) L H HC HC.beq (hn _) (hn _))
  simp only [push] at key
  show O.app (O.app _ (O.app (M.cval "UInt64.ofNat" []) (natEnc M x.toNat)))
    (O.app (M.cval "UInt64.ofNat" []) (natEnc M y.toNat)) = _
  rw [key, beq_set L H HC ρ]
  have : (x.toNat == y.toNat) = (x == y) := by
    cases h : x == y
    · have : x ≠ y := by simpa using h
      have : x.toNat ≠ y.toNat := fun e => this (UInt64.toNat_inj.mp e)
      simpa using this
    · have : x = y := by simpa using h
      subst this; simp
  rw [this]

end Bridge.Cmp
