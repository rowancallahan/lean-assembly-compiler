/- Bridge.Shift: `.bin` for `<<<` (op 6) and `>>>` (op 7), DISCHARGED.  Stored theorems: `pow_z : Nat.pow n zero =
succ zero`, `pow_s : Nat.pow n (succ m) = Nat.pow n m * n`, the guarded characterizations
`mod_char : ∀ q r b, Nat.blt r b = true → (q * b + r) % b = r` and `div_char : ∀ q r b, Nat.blt r b = true →
(q * b + r) / b = q`, and `br_shl : ofNat a <<< ofNat b = ofNat (a * Nat.pow 2 (b % 64))`,
`br_shr : ∀ a b, Nat.blt a 2^64 = true → ofNat a >>> ofNat b = ofNat (a / Nat.pow 2 (b % 64))`.

STATUS: proved, no sorry. -/
import Bridge.Final6

namespace Bridge.Shift
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Asm Bridge.Add Bridge.Final
  Bridge.Call Bridge.Len Bridge.Cmp Bridge.Final5 Bridge.Arith Bridge.Bytes Bridge.Final6

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

/-- an operator head with only its typing (no instances required) -/
structure OpCore (env : List Const) (f H hi K : String) : Prop where
  fH : HasTy env f [0, 0, 0] (.forallE (.sort 1) (.forallE (.sort 1)
    (.forallE (.app (.const "outParam" [2]) (.sort 1))
      (.forallE (.app (.app (.app (.const H [0, 0, 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
        (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) false) false) false) false) false) false)
  hiT : HasTy env hi [0] (.forallE (.sort 1) (.forallE (.app (.const K [0]) (.bvar 0))
    (.app (.app (.app (.const H [0, 0, 0]) (.bvar 1)) (.bvar 1)) (.bvar 1)) false) false)

def modN (a b : E) : E := opE "HMod.hMod" "instHMod" tNat "Nat.instMod" a b
def divN (a b : E) : E := opE "HDiv.hDiv" "instHDiv" tNat "Nat.instDiv" a b
def shlU (a b : E) : E := opE "HShiftLeft.hShiftLeft" "instHShiftLeftOfShiftLeft" tU "instShiftLeftUInt64" a b
def shrU (a b : E) : E := opE "HShiftRight.hShiftRight" "instHShiftRightOfShiftRight" tU "instShiftRightUInt64" a b
def powE (a b : E) : E := bin2 "Nat.pow" a b

structure ShiftEnv (env : List Const) : Prop where
  modC : OpCore env "HMod.hMod" "HMod" "instHMod" "Mod"
  modI : HasTy env "Nat.instMod" [] (.app (.const "Mod" [0]) tNat)
  divC : OpCore env "HDiv.hDiv" "HDiv" "instHDiv" "Div"
  divI : HasTy env "Nat.instDiv" [] (.app (.const "Div" [0]) tNat)
  shlC : OpCore env "HShiftLeft.hShiftLeft" "HShiftLeft" "instHShiftLeftOfShiftLeft" "ShiftLeft"
  shlI : HasTy env "instShiftLeftUInt64" [] (.app (.const "ShiftLeft" [0]) tU)
  shrC : OpCore env "HShiftRight.hShiftRight" "HShiftRight" "instHShiftRightOfShiftRight" "ShiftRight"
  shrI : HasTy env "instShiftRightUInt64" [] (.app (.const "ShiftRight" [0]) tU)
  powH : HasTy env "Nat.pow" [] (.forallE tNat (.forallE tNat tNat false) false)
  powZ : HasTy env "pow_z" [] (piN [(tNat, true)] (eqE 1 tNat (powE (.bvar 0) nz) (sc nz)))
  powS : HasTy env "pow_s" [] (piN [(tNat, true), (tNat, true)]
    (eqE 1 tNat (powE (.bvar 1) (sc (.bvar 0))) (mulN (powE (.bvar 1) (.bvar 0)) (.bvar 1))))
  modChar : HasTy env "mod_char" [] (piN [(tNat, true), (tNat, true), (tNat, true),
      (eqE 1 tB (bin2 "Nat.blt" (.bvar 1) (.bvar 0)) tt, true)]
    (eqE 1 tNat (modN (addN (mulN (.bvar 3) (.bvar 1)) (.bvar 2)) (.bvar 1)) (.bvar 2)))
  divChar : HasTy env "div_char" [] (piN [(tNat, true), (tNat, true), (tNat, true),
      (eqE 1 tB (bin2 "Nat.blt" (.bvar 1) (.bvar 0)) tt, true)]
    (eqE 1 tNat (divN (addN (mulN (.bvar 3) (.bvar 1)) (.bvar 2)) (.bvar 1)) (.bvar 3)))
  brShl : HasTy env "br_shl" [] (piN [(tNat, true), (tNat, true)]
    (eqE 1 tU (shlU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (mulN (.bvar 1) (powE (litNat 2) (modN (.bvar 0) (litNat 64)))))))
  brShr : HasTy env "br_shr" [] (piN [(tNat, true), (tNat, true), (guard (.bvar 1), true)]
    (eqE 1 tU (shrU (ofN (.bvar 2)) (ofN (.bvar 1))) (ofN (divN (.bvar 2) (powE (litNat 2) (modN (.bvar 1) (litNat 64)))))))

variable (L : SetLaws O)
include L

theorem core_mem {f H hi K : String} (HA : AddEnv env) (HO : OpCore env f H hi K) {ρ : Nat → S} {T : S}
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

/-- `Nat.pow` on numerals -/
theorem pow_set (H : EncEnv env) (HA : AddEnv env) (HM : MulEnv env) (HS : ShiftEnv env) (ρ : Nat → S) (a : Nat) :
    ∀ k, O.app (O.app (M.cval "Nat.pow" []) (natEnc M a)) (natEnc M k) = natEnc M (a ^ k) := by
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dP : D O M.cval ρ (.forallE tNat (.forallE tNat tNat false) false) _ :=
    .pi .const (fun _ _ => .pi .const (fun _ _ => .const) (np rfl)) (np rfl)
  have pm : ∀ x y, O.mem x (M.cval "Nat" []) → O.mem y (M.cval "Nat" []) →
      O.mem (O.app (O.app (M.cval "Nat.pow" []) x) y) (M.cval "Nat" []) := fun x y hx hy =>
    L.app_mem_piR (L.app_mem_piR (mem_ty M L HS.powH dP) hx (np rfl)) hy (np rfl)
  have hIN := mem_ty M L HM.op.kNat (ρ := ρ) (.app .const .const)
  intro k
  induction k with
  | zero =>
    obtain ⟨ty, hc, hty⟩ := HS.powZ
    exact transferN L M hc (ls := []) hty ρ (.cons .const (hn a) .nil) .const (.app (.app .const .bvar) .const)
      (.app .const .const) hNu (pm _ _ (hn a) (hn 0)) (hn 1)
  | succ k ih =>
    obtain ⟨ty, hc, hty⟩ := HS.powS
    have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn a) (.cons .const (hn k) .nil)) .const
      (.app (.app .const .bvar) (.app .const .bvar)) (.app (.app (opS_D _ _) (.app (.app .const .bvar) .bvar)) .bvar) hNu
      (pm _ _ (hn a) (hn (k + 1))) (op_mem L HA HM.op (ρ := ρ) hNu hIN (pm _ _ (hn a) (hn k)) (hn a))
    simp only [push] at key
    show O.app (O.app (M.cval "Nat.pow" []) (natEnc M a)) (O.app (M.cval "Nat.succ" []) (natEnc M k)) = _
    rw [key, ih, mul_set L H HA HM ρ, Nat.pow_succ]

/-- the numeral `q * b + r` -/
theorem qbr (H : EncEnv env) (HA : AddEnv env) (HM : MulEnv env) (ρ : Nat → S) (q b r : Nat) :
    O.app (O.app (opS M "HAdd.hAdd" "instHAdd" (M.cval "Nat" []) "instAddNat")
      (O.app (O.app (opS M "HMul.hMul" "instHMul" (M.cval "Nat" []) "instMulNat") (natEnc M q)) (natEnc M b))) (natEnc M r) =
      natEnc M (q * b + r) := by
  rw [mul_set L H HA HM ρ, add_set L H HA ρ]

/-- `%` and `/` on numerals, through the guarded characterizations -/
theorem modDiv_set (H : EncEnv env) (HA : AddEnv env) (HM : MulEnv env) (HS : ShiftEnv env) (HC : CmpEnv env)
    (ρ : Nat → S) (a b : Nat) (hb : 0 < b) :
    O.app (O.app (opS M "HMod.hMod" "instHMod" (M.cval "Nat" []) "Nat.instMod") (natEnc M a)) (natEnc M b) = natEnc M (a % b) ∧
    O.app (O.app (opS M "HDiv.hDiv" "instHDiv" (M.cval "Nat" []) "Nat.instDiv") (natEnc M a)) (natEnc M b) = natEnc M (a / b) := by
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hBu := univ1 (M := M) (L := L) H HC.bool ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have hIM := mem_ty M L HS.modI (ρ := ρ) (.app .const .const)
  have hID := mem_ty M L HS.divI (ρ := ρ) (.app .const .const)
  have hr : a % b < b := Nat.mod_lt _ hb
  have ha : natEnc M a = O.app (O.app (opS M "HAdd.hAdd" "instHAdd" (M.cval "Nat" []) "instAddNat")
      (O.app (O.app (opS M "HMul.hMul" "instHMul" (M.cval "Nat" []) "instMulNat") (natEnc M (a / b))) (natEnc M b)))
      (natEnc M (a % b)) := by
    rw [qbr L H HA HM ρ, Nat.div_add_mod']
  have hblt := blt_set (M := M) L H HC ρ (a % b) b
  rw [show decide (a % b < b) = true by simpa using hr] at hblt
  have hbltm : O.mem (O.app (O.app (M.cval "Nat.blt" []) (natEnc M (a % b))) (natEnc M b)) (M.cval "Bool" []) := by
    rw [hblt]; exact bool_mem L HC ρ true
  have hg : O.mem O.pt (O.app (O.app (O.app (M.cval "Eq" [1]) (M.cval "Bool" []))
      (O.app (O.app (M.cval "Nat.blt" []) (natEnc M (a % b))) (natEnc M b))) (M.cval "Bool.true" [])) := by
    rw [M.eq_equality 1 ρ _ _ _ _ .const hBu hbltm (mem_ty M L HC.btrue (ρ := ρ) .const)]
    exact L.pt_mem_eqv (by rw [hblt]; rfl)
  have hAm : O.mem (natEnc M a) (M.cval "Nat" []) := hn a
  rw [ha] at hAm
  have tele := Tele.cons (M := M) (pw := true) (ts := [(tNat, true), (tNat, true),
      (eqE 1 tB (bin2 "Nat.blt" (.bvar 1) (.bvar 0)) tt, true)]) (ρ := ρ) .const (hn (a / b))
    (.cons (pw := true) .const (hn (a % b)) (.cons (pw := true) .const (hn b)
      (.cons (pw := true) (.app (.app (.app .const .const) (.app (.app .const .bvar) .bvar)) .const) hg .nil)))
  constructor
  · obtain ⟨ty, hc, hty⟩ := HS.modChar
    have key := transferN L M hc (ls := []) hty ρ tele .const
      (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) .bvar) .bvar)) .bvar)) .bvar) .bvar hNu
      (core_mem L HA HS.modC (ρ := ρ) hNu hIM hAm (hn b)) (hn (a % b))
    simp only [push] at key
    rw [ha]; exact key
  · obtain ⟨ty, hc, hty⟩ := HS.divChar
    have key := transferN L M hc (ls := []) hty ρ tele .const
      (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) .bvar) .bvar)) .bvar)) .bvar) .bvar hNu
      (core_mem L HA HS.divC (ρ := ρ) hNu hID hAm (hn b)) (hn (a / b))
    simp only [push] at key
    rw [ha]; exact key

/-- **`<<<` (op 6)** -/
theorem shl_field (E : Env6 env sig P) (HS : ShiftEnv env) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S)
    (x y : UInt64) :
    O.app (O.app (opS M "HShiftLeft.hShiftLeft" "instHShiftLeftOfShiftLeft" (M.cval "UInt64" []) "instShiftLeftUInt64")
      (encM M (.w x))) (encM M (.w y)) = encM M (.w (x <<< y)) := by
  have H := E.enc
  have HA := E.add
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "UInt64.ofNat" []) a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  have hIU := mem_ty M L HS.shlI (ρ := ρ) (.app .const .const)
  have hIN := mem_ty M L E.mul.op.kNat (ρ := ρ) (.app .const .const)
  have hIM := mem_ty M L HS.modI (ρ := ρ) (.app .const .const)
  have dP : D O M.cval ρ (.forallE tNat (.forallE tNat tNat false) false) _ :=
    .pi .const (fun _ _ => .pi .const (fun _ _ => .const) (np rfl)) (np rfl)
  have pm : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) →
      O.mem (O.app (O.app (M.cval "Nat.pow" []) a) b) (M.cval "Nat" []) := fun a b ha hb =>
    L.app_mem_piR (L.app_mem_piR (mem_ty M L HS.powH dP) ha (np rfl)) hb (np rfl)
  have hmod := core_mem L HA HS.modC (ρ := ρ) hNu hIM (hn y.toNat) (hn 64)
  have hpow := pm _ _ (hn 2) hmod
  have hmul := op_mem L HA E.mul.op (ρ := ρ) hNu hIN (hn x.toNat) hpow
  obtain ⟨ty, hc, hty⟩ := HS.brShl
  have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn x.toNat) (.cons .const (hn y.toNat) .nil)) .const
    (.app (.app (opS_D _ _) (.app .const .bvar)) (.app .const .bvar))
    (.app .const (.app (.app (opS_D _ _) .bvar) (.app (.app .const (litNat_D L E.toEnv hbl _ 2))
      (.app (.app (opS_D _ _) .bvar) (litNat_D L E.toEnv hbl _ 64))))) hUu
    (core_mem L HA HS.shlC (ρ := ρ) hUu hIU (ofMem _ (hn _)) (ofMem _ (hn _))) (ofMem _ hmul)
  simp only [push] at key
  show O.app (O.app _ (O.app (M.cval "UInt64.ofNat" []) (natEnc M x.toNat)))
    (O.app (M.cval "UInt64.ofNat" []) (natEnc M y.toNat)) = O.app (M.cval "UInt64.ofNat" []) (natEnc M (x <<< y).toNat)
  rw [key, (modDiv_set L H HA E.mul HS E.cmp ρ y.toNat 64 (by decide)).1, pow_set L H HA E.mul HS ρ 2,
    mul_set L H HA E.mul ρ, wrap_mod L H E.lit E.instN hbl HA ρ]
  congr 2
  simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- **`>>>` (op 7)** -/
theorem shr_field (E : Env6 env sig P) (HS : ShiftEnv env) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S)
    (x y : UInt64) :
    O.app (O.app (opS M "HShiftRight.hShiftRight" "instHShiftRightOfShiftRight" (M.cval "UInt64" []) "instShiftRightUInt64")
      (encM M (.w x))) (encM M (.w y)) = encM M (.w (x >>> y)) := by
  have H := E.enc
  have HA := E.add
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "UInt64.ofNat" []) a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  have hIU := mem_ty M L HS.shrI (ρ := ρ) (.app .const .const)
  have hID := mem_ty M L HS.divI (ρ := ρ) (.app .const .const)
  have hIM := mem_ty M L HS.modI (ρ := ρ) (.app .const .const)
  have dP : D O M.cval ρ (.forallE tNat (.forallE tNat tNat false) false) _ :=
    .pi .const (fun _ _ => .pi .const (fun _ _ => .const) (np rfl)) (np rfl)
  have pm : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) →
      O.mem (O.app (O.app (M.cval "Nat.pow" []) a) b) (M.cval "Nat" []) := fun a b ha hb =>
    L.app_mem_piR (L.app_mem_piR (mem_ty M L HS.powH dP) ha (np rfl)) hb (np rfl)
  have hmod := core_mem L HA HS.modC (ρ := ρ) hNu hIM (hn y.toNat) (hn 64)
  have hpow := pm _ _ (hn 2) hmod
  have hdiv := core_mem L HA HS.divC (ρ := ρ) hNu hID (hn x.toNat) hpow
  let ρ2 := push (natEnc M y.toNat) (push (natEnc M x.toNat) ρ)
  obtain ⟨G, hG, hp⟩ := guard_mem (ρ := ρ2) (i := 1) L H E.lit E.instN E.cmp hbl rfl x.toNat_lt_size
  obtain ⟨ty, hc, hty⟩ := HS.brShr
  have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn x.toNat) (.cons .const (hn y.toNat) (.cons hG hp .nil)))
    .const (.app (.app (opS_D _ _) (.app .const .bvar)) (.app .const .bvar))
    (.app .const (.app (.app (opS_D _ _) .bvar) (.app (.app .const (litNat_D L E.toEnv hbl _ 2))
      (.app (.app (opS_D _ _) .bvar) (litNat_D L E.toEnv hbl _ 64))))) hUu
    (core_mem L HA HS.shrC (ρ := ρ) hUu hIU (ofMem _ (hn _)) (ofMem _ (hn _))) (ofMem _ hdiv)
  simp only [push] at key
  show O.app (O.app _ (O.app (M.cval "UInt64.ofNat" []) (natEnc M x.toNat)))
    (O.app (M.cval "UInt64.ofNat" []) (natEnc M y.toNat)) = O.app (M.cval "UInt64.ofNat" []) (natEnc M (x >>> y).toNat)
  rw [key, (modDiv_set L H HA E.mul HS E.cmp ρ y.toNat 64 (by decide)).1, pow_set L H HA E.mul HS ρ 2,
    (modDiv_set L H HA E.mul HS E.cmp ρ x.toNat (2 ^ (y.toNat % 64)) (Nat.two_pow_pos _)).2]
  congr 2
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

end Bridge.Shift
