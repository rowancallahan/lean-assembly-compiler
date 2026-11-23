/- Bridge.Arith: `.bin` for `-` (op 2) and `*` (op 3), DISCHARGED (value and head typing).  Generic typing of the
heterogeneous-operator heads (`HSub.hSub`, `HMul.hMul`; same shape as `HAdd.hAdd`, with `outParam`).  Stored
theorems (Nat ones with `Nat.zero`/`Nat.succ`): `sub_n0 : n - zero = n`, `sub_ss : succ n - succ m = n - m`,
`sub_0s : zero - succ m = zero`, `br_sub : ∀ a b, Nat.blt b 2^64 = true → ofNat a - ofNat b = ofNat (a + (2^64 - b))`,
`mul_n0 : n * zero = zero`, `mul_ns : n * succ m = n * m + n`, `br_mul : ofNat a * ofNat b = ofNat (a * b)`.

STATUS: proved, no sorry. -/
import Bridge.Final5

namespace Bridge.Arith
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Asm Bridge.Add Bridge.Final
  Bridge.Call Bridge.Len Bridge.Cmp Bridge.Final5

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

/-- a heterogeneous operator `f : {α β γ} [H α β γ] → α → β → γ` with homogeneous instance `hi : {α} [K α] → H α α α`
and the `K` instances for Nat and UInt64 -/
structure OpEnv (env : List Const) (f H hi K kN kU : String) : Prop where
  cls : HasTy env H [0, 0, 0] (.forallE (.sort 1) (.forallE (.sort 1)
    (.forallE (.app (.const "outParam" [2]) (.sort 1)) (.sort 1) false) false) false)
  fH : HasTy env f [0, 0, 0] (.forallE (.sort 1) (.forallE (.sort 1)
    (.forallE (.app (.const "outParam" [2]) (.sort 1))
      (.forallE (.app (.app (.app (.const H [0, 0, 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
        (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) false) false) false) false) false) false)
  k : HasTy env K [0] (.forallE (.sort 1) (.sort 1) false)
  hiT : HasTy env hi [0] (.forallE (.sort 1) (.forallE (.app (.const K [0]) (.bvar 0))
    (.app (.app (.app (.const H [0, 0, 0]) (.bvar 1)) (.bvar 1)) (.bvar 1)) false) false)
  kNat : HasTy env kN [] (.app (.const K [0]) tNat)
  kU64 : HasTy env kU [] (.app (.const K [0]) tU)

/-- `@f T T T (hi T I) a b` -/
def opE (f hi : String) (T : E) (I : String) (a b : E) : E :=
  .app (.app (.app (.app (.app (.app (.const f [0, 0, 0]) T) T) T) (.app (.app (.const hi [0]) T) (.const I []))) a) b

variable (M) in
/-- the set of `@f T T T (hi T I)` -/
def opS (f hi : String) (T : S) (I : String) : S :=
  O.app (O.app (O.app (O.app (M.cval f [0, 0, 0]) T) T) T) (O.app (O.app (M.cval hi [0]) T) (M.cval I []))

variable (L : SetLaws O)
include L

theorem op_mem {f H hi K kN kU : String} (HA : AddEnv env) (HO : OpEnv env f H hi K kN kU) {ρ : Nat → S} {T : S}
    {I : String} (hT : O.mem T (O.univ 1)) (hI : O.mem (M.cval I []) (O.app (M.cval K [0]) T)) {X Y : S}
    (hX : O.mem X T) (hY : O.mem Y T) : O.mem (O.app (O.app (opS M f hi T I) X) Y) T := by
  have hOP := outParam_type (M := M) L HA ρ
  have dTy : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1)
      (.forallE (.app (.const "outParam" [2]) (.sort 1))
        (.forallE (.app (.app (.app (.const H [0, 0, 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) false) false) false) false) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.univ 1) fun b => O.piR 1 (O.app (M.cval "outParam" [2]) (O.univ 1)) fun c =>
        O.piR 1 (O.app (O.app (O.app (M.cval H [0, 0, 0]) a) b) c) fun _ =>
          O.piR 1 a fun _ => O.piR 1 b fun _ => c) :=
    .pi .sort (fun _ _ => .pi .sort (fun _ _ => .pi (.app .const .sort) (fun _ _ => .pi (.app (.app (.app .const .bvar)
      .bvar) .bvar) (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar (fun _ _ => .bvar) (np rfl)) (np rfl)) (np rfl))
      (np rfl)) (np rfl)) (np rfl)
  have dI : D O M.cval ρ (.forallE (.sort 1) (.forallE (.app (.const K [0]) (.bvar 0))
      (.app (.app (.app (.const H [0, 0, 0]) (.bvar 1)) (.bvar 1)) (.bvar 1)) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.app (M.cval K [0]) a) fun _ =>
        O.app (O.app (O.app (M.cval H [0, 0, 0]) a) a) a) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .app (.app (.app .const .bvar) .bvar) .bvar) (np rfl)) (np rfl)
  have hInst := L.app_mem_piR (L.app_mem_piR (mem_ty M L HO.hiT dI) hT (np rfl)) hI (np rfl)
  have hT' : O.mem T (O.app (M.cval "outParam" [2]) (O.univ 1)) := by rw [hOP]; exact hT
  have g := L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HO.fH dTy) hT (np rfl)) hT (np rfl))
    hT' (np rfl)) hInst (np rfl)
  exact L.app_mem_piR (L.app_mem_piR g hX (np rfl)) hY (np rfl)

omit L in
theorem opS_D {f hi : String} {I : String} (ρ : Nat → S) (Tn : String) :
    D O M.cval ρ (.app (.app (.app (.app (.const f [0, 0, 0]) (.const Tn [])) (.const Tn [])) (.const Tn []))
      (.app (.app (.const hi [0]) (.const Tn [])) (.const I []))) (opS M f hi (M.cval Tn []) I) :=
  .app (.app (.app (.app .const .const) .const) .const) (.app (.app .const .const) .const)

/-- `+` on Nat numerals (from `add0`/`addS`) -/
theorem add_set (H : EncEnv env) (HA : AddEnv env) (ρ : Nat → S) :
    ∀ a b, O.app (O.app (opS M "HAdd.hAdd" "instHAdd" (M.cval "Nat" []) "instAddNat") (natEnc M a)) (natEnc M b) =
      natEnc M (a + b) := by
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hnat := natEnc_mem' (M := M) (L := L) H ρ
  have dAddN : D O M.cval ρ (.app (.const "Add" [0]) tNat) _ := .app .const .const
  have hAN := hAdd_mem (M := M) L HA (ρ := ρ) hNu (mem_ty M L HA.addNat dAddN)
  let ADD := opS M "HAdd.hAdd" "instHAdd" (M.cval "Nat" []) "instAddNat"
  have addMem : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) → O.mem (O.app (O.app ADD a) b) (M.cval "Nat" []) :=
    fun a b ha hb => L.app_mem_piR (L.app_mem_piR hAN ha (np rfl)) hb (np rfl)
  have dS : D O M.cval ρ (.forallE tNat tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have sMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "Nat.succ" []) a) (M.cval "Nat" []) :=
    fun a ha => mem_app' L dS (mem_ty M L H.succ dS) .const ha .const
  have dAddNE : ∀ ρ', D O M.cval ρ' (hAdd tNat (instH tNat "instAddNat")) ADD := fun _ =>
    .app (.app (.app (.app .const .const) .const) .const) (.app (.app .const .const) .const)
  have hz : ∀ a, O.mem a (M.cval "Nat" []) → O.app (O.app ADD a) (M.cval "Nat.zero" []) = a := by
    intro a ha
    obtain ⟨ty, hc, hty⟩ := HA.add0
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha .nil) .const (.app (.app (dAddNE _) .bvar) .const) .bvar
      hNu (addMem _ _ ha (hnat 0)) ha
  have hs : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) →
      O.app (O.app ADD a) (O.app (M.cval "Nat.succ" []) b) = O.app (M.cval "Nat.succ" []) (O.app (O.app ADD a) b) := by
    intro a b ha hb
    obtain ⟨ty, hc, hty⟩ := HA.addS
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha (.cons .const hb .nil)) .const
      (.app (.app (dAddNE _) .bvar) (.app .const .bvar)) (.app .const (.app (.app (dAddNE _) .bvar) .bvar))
      hNu (addMem _ _ ha (sMem _ hb)) (sMem _ (addMem _ _ ha hb))
  exact add_nat (O := O) (M.cval "Nat.zero" []) (M.cval "Nat.succ" []) ADD (M.cval "Nat" []) (natEnc M) rfl
    (fun _ => rfl) hnat hz hs

/-! ## `-` -/

def subN (a b : E) : E := opE "HSub.hSub" "instHSub" tNat "instSubNat" a b
def subU (a b : E) : E := opE "HSub.hSub" "instHSub" tU "instSubUInt64" a b
def mulN (a b : E) : E := opE "HMul.hMul" "instHMul" tNat "instMulNat" a b
def mulU (a b : E) : E := opE "HMul.hMul" "instHMul" tU "instMulUInt64" a b

structure SubEnv (env : List Const) : Prop where
  op : OpEnv env "HSub.hSub" "HSub" "instHSub" "Sub" "instSubNat" "instSubUInt64"
  n0 : HasTy env "sub_n0" [] (piN [(tNat, true)] (eqE 1 tNat (subN (.bvar 0) nz) (.bvar 0)))
  ss : HasTy env "sub_ss" [] (piN [(tNat, true), (tNat, true)]
    (eqE 1 tNat (subN (sc (.bvar 1)) (sc (.bvar 0))) (subN (.bvar 1) (.bvar 0))))
  zs : HasTy env "sub_0s" [] (piN [(tNat, true)] (eqE 1 tNat (subN nz (sc (.bvar 0))) nz))
  br : HasTy env "br_sub" [] (piN [(tNat, true), (tNat, true), (guard (.bvar 0), true)]
    (eqE 1 tU (subU (ofN (.bvar 2)) (ofN (.bvar 1))) (ofN (addN (.bvar 2) (subN nLit (.bvar 1))))))

structure MulEnv (env : List Const) : Prop where
  op : OpEnv env "HMul.hMul" "HMul" "instHMul" "Mul" "instMulNat" "instMulUInt64"
  n0 : HasTy env "mul_n0" [] (piN [(tNat, true)] (eqE 1 tNat (mulN (.bvar 0) nz) nz))
  ns : HasTy env "mul_ns" [] (piN [(tNat, true), (tNat, true)]
    (eqE 1 tNat (mulN (.bvar 1) (sc (.bvar 0))) (addN (mulN (.bvar 1) (.bvar 0)) (.bvar 1))))
  br : HasTy env "br_mul" [] (piN [(tNat, true), (tNat, true)]
    (eqE 1 tU (mulU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (mulN (.bvar 1) (.bvar 0)))))

theorem sub_set (H : EncEnv env) (HA : AddEnv env) (HS : SubEnv env) (ρ : Nat → S) :
    ∀ a b, O.app (O.app (opS M "HSub.hSub" "instHSub" (M.cval "Nat" []) "instSubNat") (natEnc M a)) (natEnc M b) =
      natEnc M (a - b) := by
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have hI := mem_ty M L HS.op.kNat (ρ := ρ) (.app .const .const)
  have sm : ∀ a b, O.mem (O.app (O.app (opS M "HSub.hSub" "instHSub" (M.cval "Nat" []) "instSubNat") (natEnc M a))
      (natEnc M b)) (M.cval "Nat" []) := fun a b => op_mem L HA HS.op (ρ := ρ) hNu hI (hn a) (hn b)
  have dS : ∀ ρ', D O M.cval ρ' (opE "HSub.hSub" "instHSub" tNat "instSubNat" (.bvar 0) (.bvar 0)) _ := fun ρ' =>
    .app (.app (opS_D (f := "HSub.hSub") (hi := "instHSub") (I := "instSubNat") ρ' "Nat") .bvar) .bvar
  intro a b
  induction b generalizing a with
  | zero =>
    obtain ⟨ty, hc, hty⟩ := HS.n0
    exact transferN L M hc (ls := []) hty ρ (.cons .const (hn a) .nil) .const
      (.app (.app (opS_D _ _) .bvar) .const) .bvar hNu (sm a 0) (hn a)
  | succ b ih =>
    cases a with
    | zero =>
      obtain ⟨ty, hc, hty⟩ := HS.zs
      rw [show 0 - (b + 1) = 0 by omega]
      exact transferN L M hc (ls := []) hty ρ (.cons .const (hn b) .nil) .const
        (.app (.app (opS_D _ _) .const) (.app .const .bvar)) .const hNu (sm 0 (b + 1)) (hn 0)
    | succ a =>
      obtain ⟨ty, hc, hty⟩ := HS.ss
      rw [show a + 1 - (b + 1) = a - b by omega, ← ih a]
      exact transferN L M hc (ls := []) hty ρ (.cons .const (hn a) (.cons .const (hn b) .nil)) .const
        (.app (.app (opS_D _ _) (.app .const .bvar)) (.app .const .bvar)) (.app (.app (opS_D _ _) .bvar) .bvar)
        hNu (sm (a + 1) (b + 1)) (sm a b)

theorem mul_set (H : EncEnv env) (HA : AddEnv env) (HM : MulEnv env) (ρ : Nat → S) :
    ∀ a b, O.app (O.app (opS M "HMul.hMul" "instHMul" (M.cval "Nat" []) "instMulNat") (natEnc M a)) (natEnc M b) =
      natEnc M (a * b) := by
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have hI := mem_ty M L HM.op.kNat (ρ := ρ) (.app .const .const)
  have mm : ∀ a b, O.mem (O.app (O.app (opS M "HMul.hMul" "instHMul" (M.cval "Nat" []) "instMulNat") (natEnc M a))
      (natEnc M b)) (M.cval "Nat" []) := fun a b => op_mem L HA HM.op (ρ := ρ) hNu hI (hn a) (hn b)
  have dAddN : D O M.cval ρ (.app (.const "Add" [0]) tNat) _ := .app .const .const
  have hAN := hAdd_mem (M := M) L HA (ρ := ρ) hNu (mem_ty M L HA.addNat dAddN)
  have hadd := add_set (M := M) L H HA ρ
  intro a b
  induction b with
  | zero =>
    obtain ⟨ty, hc, hty⟩ := HM.n0
    exact transferN L M hc (ls := []) hty ρ (.cons .const (hn a) .nil) .const
      (.app (.app (opS_D _ _) .bvar) .const) .const hNu (mm a 0) (hn 0)
  | succ b ih =>
    obtain ⟨ty, hc, hty⟩ := HM.ns
    have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn a) (.cons .const (hn b) .nil)) .const
      (.app (.app (opS_D _ _) .bvar) (.app .const .bvar))
      (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) .bvar) .bvar)) .bvar) hNu (mm a (b + 1))
      (L.app_mem_piR (L.app_mem_piR hAN (mm a b) (np rfl)) (hn a) (np rfl))
    simp only [push] at key
    show O.app _ (O.app (M.cval "Nat.succ" []) (natEnc M b)) = _
    rw [key, ih, hadd]; rfl

/-- **`-` (op 2)** -/
theorem sub_field (E : Env5 env sig P) (HS : SubEnv env) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S)
    (x y : UInt64) :
    O.app (O.app (opS M "HSub.hSub" "instHSub" (M.cval "UInt64" []) "instSubUInt64") (encM M (.w x))) (encM M (.w y)) =
      encM M (.w (x - y)) := by
  have H := E.enc
  have HA := E.add
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "UInt64.ofNat" []) a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  have hIU := mem_ty M L HS.op.kU64 (ρ := ρ) (.app .const .const)
  have hIN := mem_ty M L HS.op.kNat (ρ := ρ) (.app .const .const)
  have dAddN : D O M.cval ρ (.app (.const "Add" [0]) tNat) _ := .app .const .const
  have hAN := hAdd_mem (M := M) L HA (ρ := ρ) hNu (mem_ty M L HA.addNat dAddN)
  let ρ3 := push (natEnc M y.toNat) (push (natEnc M x.toNat) ρ)
  obtain ⟨G, hG, hp⟩ := guard_mem (ρ := ρ3) (i := 0) L H E.lit E.instN E.cmp hbl rfl y.toNat_lt_size
  have hsubN := op_mem L HA HS.op (ρ := ρ) hNu hIN (hn UInt64.size) (hn y.toNat)
  have hsum := L.app_mem_piR (L.app_mem_piR hAN (hn x.toNat) (np rfl)) hsubN (np rfl)
  obtain ⟨ty, hc, hty⟩ := HS.br
  have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn _) (.cons .const (hn _) (.cons hG hp .nil))) .const
    (.app (.app (opS_D _ _) (.app .const .bvar)) (.app .const .bvar))
    (.app .const (.app (.app (.app (.app (.app (.app .const .const) .const) .const) (.app (.app .const .const) .const)) .bvar)
      (.app (.app (opS_D _ _) (Cmp.nLit_D L H E.lit E.instN hbl _)) .bvar))) hUu
    (op_mem L HA HS.op (ρ := ρ) hUu hIU (ofMem _ (hn _)) (ofMem _ (hn _))) (ofMem _ hsum)
  simp only [push] at key
  show O.app (O.app _ (O.app (M.cval "UInt64.ofNat" []) (natEnc M x.toNat)))
    (O.app (M.cval "UInt64.ofNat" []) (natEnc M y.toNat)) = O.app (M.cval "UInt64.ofNat" []) (natEnc M (x - y).toNat)
  rw [key, sub_set L H HA HS ρ, show O.app (O.app (O.app (O.app (O.app (O.app (M.cval "HAdd.hAdd" [0, 0, 0])
    (M.cval "Nat" [])) (M.cval "Nat" [])) (M.cval "Nat" [])) (O.app (O.app (M.cval "instHAdd" [0]) (M.cval "Nat" []))
    (M.cval "instAddNat" []))) (natEnc M x.toNat)) (natEnc M (UInt64.size - y.toNat)) = natEnc M (x.toNat + (UInt64.size - y.toNat))
    from add_set (M := M) L H HA ρ _ _, wrap_mod L H E.lit E.instN hbl HA ρ]
  congr 2
  rw [UInt64.toNat_sub, Nat.add_comm]

/-- **`*` (op 3)** -/
theorem mul_field (E : Env5 env sig P) (HM : MulEnv env) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S)
    (x y : UInt64) :
    O.app (O.app (opS M "HMul.hMul" "instHMul" (M.cval "UInt64" []) "instMulUInt64") (encM M (.w x))) (encM M (.w y)) =
      encM M (.w (x * y)) := by
  have H := E.enc
  have HA := E.add
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "UInt64.ofNat" []) a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  have hIU := mem_ty M L HM.op.kU64 (ρ := ρ) (.app .const .const)
  have hIN := mem_ty M L HM.op.kNat (ρ := ρ) (.app .const .const)
  obtain ⟨ty, hc, hty⟩ := HM.br
  have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn x.toNat) (.cons .const (hn y.toNat) .nil)) .const
    (.app (.app (opS_D _ _) (.app .const .bvar)) (.app .const .bvar))
    (.app .const (.app (.app (opS_D _ _) .bvar) .bvar)) hUu
    (op_mem L HA HM.op (ρ := ρ) hUu hIU (ofMem _ (hn _)) (ofMem _ (hn _)))
    (ofMem _ (op_mem L HA HM.op (ρ := ρ) hNu hIN (hn _) (hn _)))
  simp only [push] at key
  show O.app (O.app _ (O.app (M.cval "UInt64.ofNat" []) (natEnc M x.toNat)))
    (O.app (M.cval "UInt64.ofNat" []) (natEnc M y.toNat)) = O.app (M.cval "UInt64.ofNat" []) (natEnc M (x * y).toNat)
  rw [key, mul_set L H HA HM ρ, wrap_mod L H E.lit E.instN hbl HA ρ, UInt64.toNat_mul]

end Bridge.Arith
