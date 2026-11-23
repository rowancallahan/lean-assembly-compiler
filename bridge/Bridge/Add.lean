/- Bridge.Add: the `.bin` fact for `+` (op 1), the arithmetic pattern of DENOTES_SPIKE §2, in the trimmed model.
* `HeadTy.bin` for op 1: typing through `HAdd.hAdd`'s declared type, INCLUDING `outParam` (needs the stored
  `outParam.{2} Type = Type`, `rfl`), and `instHAdd`/`instAddUInt64`.
* `Open.bin` for op 1: `⟦+⟧ (enc x) (enc y) = enc (x + y)` from four stored theorems (transfer):
  `add0 : ∀ n : Nat, n + Nat.zero = n`, `addS : ∀ n m : Nat, n + Nat.succ m = Nat.succ (n + m)`,
  `br_add : ∀ a b : Nat, UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b)`,
  `br_wrap : ∀ n : Nat, UInt64.ofNat (n + 18446744073709551616) = UInt64.ofNat n` (the literal via `br_litN`).
  Note for the exported prelude: `add0`/`addS` must be stated with `Nat.zero`/`Nat.succ` (not `0`/`m+1`).

STATUS: proved, no sorry. -/
import Bridge.Assembly

namespace Bridge.Add
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota2 Bridge.Asm

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def hAdd (T I : E) : E := .app (.app (.app (.app (.const "HAdd.hAdd" [0, 0, 0]) T) T) T) I
def instH (T : E) (i : String) : E := .app (.app (.const "instHAdd" [0]) T) (.const i [])
def addN (a b : E) : E := .app (.app (hAdd tNat (instH tNat "instAddNat")) a) b
def addU (a b : E) : E := .app (.app (hAdd tU (instH tU "instAddUInt64")) a) b
def ofN (a : E) : E := .app (.const "UInt64.ofNat" []) a
def litNat (k : Nat) : E := .app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.lit k)) (.app (.const "instOfNatNat" []) (.lit k))

/-- the constants and theorems read here -/
structure AddEnv (env : List Const) : Prop where
  outParam : HasTy env "outParam" [2] (.forallE (.sort 2) (.sort 2) false)
  outEq : HasTy env "outParam_eq" [] (eqE 3 (.sort 2) (.app (.const "outParam" [2]) (.sort 1)) (.sort 1))
  hadd : HasTy env "HAdd" [0, 0, 0] (.forallE (.sort 1) (.forallE (.sort 1)
    (.forallE (.app (.const "outParam" [2]) (.sort 1)) (.sort 1) false) false) false)
  hAddH : HasTy env "HAdd.hAdd" [0, 0, 0] (.forallE (.sort 1) (.forallE (.sort 1)
    (.forallE (.app (.const "outParam" [2]) (.sort 1))
      (.forallE (.app (.app (.app (.const "HAdd" [0, 0, 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
        (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) false) false) false) false) false) false)
  add : HasTy env "Add" [0] (.forallE (.sort 1) (.sort 1) false)
  instHAdd : HasTy env "instHAdd" [0] (.forallE (.sort 1) (.forallE (.app (.const "Add" [0]) (.bvar 0))
    (.app (.app (.app (.const "HAdd" [0, 0, 0]) (.bvar 1)) (.bvar 1)) (.bvar 1)) false) false)
  addNat : HasTy env "instAddNat" [] (.app (.const "Add" [0]) tNat)
  addU64 : HasTy env "instAddUInt64" [] (.app (.const "Add" [0]) tU)
  add0 : HasTy env "add0" [] (piN [(tNat, false)] (eqE 1 tNat (addN (.bvar 0) (.const "Nat.zero" [])) (.bvar 0)))
  addS : HasTy env "addS" [] (piN [(tNat, false), (tNat, false)] (eqE 1 tNat
    (addN (.bvar 1) (.app (.const "Nat.succ" []) (.bvar 0))) (.app (.const "Nat.succ" []) (addN (.bvar 1) (.bvar 0)))))
  brAdd : HasTy env "br_add" [] (piN [(tNat, false), (tNat, false)] (eqE 1 tU
    (addU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (addN (.bvar 1) (.bvar 0)))))
  brWrap : HasTy env "br_wrap" [] (piN [(tNat, false)] (eqE 1 tU
    (ofN (addN (.bvar 0) (litNat UInt64.size))) (ofN (.bvar 0))))

variable (L : SetLaws O)
include L

/-- `⟦outParam Type⟧ = ⟦Type⟧` -/
theorem outParam_type (HA : AddEnv env) (ρ : Nat → S) :
    O.app (M.cval "outParam" [2]) (O.univ 1) = O.univ 1 := by
  obtain ⟨ty, hc, hty⟩ := HA.outEq
  have dO : D O M.cval ρ (.forallE (.sort 2) (.sort 2) false) (O.piR (regime false) (O.univ 2) fun _ => O.univ 2) :=
    .pi .sort (fun _ _ => .sort) (np rfl)
  have ha := mem_app' L dO (mem_ty M L HA.outParam dO) .sort (L.univ_mem_univ 1) .sort
  exact transferN L M hc (ls := []) (ts := []) hty ρ .nil .sort (.app .const .sort) .sort
    (L.univ_mem_univ 2) ha (L.univ_mem_univ 1)

/-- typing of `@HAdd.hAdd T T T (instHAdd T I)` -/
theorem hAdd_mem (HA : AddEnv env) {ρ : Nat → S} {T I : S} (hT : O.mem T (O.univ 1))
    (hI : O.mem I (O.app (M.cval "Add" [0]) T)) :
    O.mem (O.app (O.app (O.app (O.app (M.cval "HAdd.hAdd" [0, 0, 0]) T) T) T)
      (O.app (O.app (M.cval "instHAdd" [0]) T) I)) (O.piR 1 T fun _ => O.piR 1 T fun _ => T) := by
  have hOP := outParam_type (M := M) L HA ρ
  have dTy : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1)
      (.forallE (.app (.const "outParam" [2]) (.sort 1))
        (.forallE (.app (.app (.app (.const "HAdd" [0, 0, 0]) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3) false) false) false) false) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.univ 1) fun b => O.piR 1 (O.app (M.cval "outParam" [2]) (O.univ 1)) fun c =>
        O.piR 1 (O.app (O.app (O.app (M.cval "HAdd" [0, 0, 0]) a) b) c) fun _ =>
          O.piR 1 a fun _ => O.piR 1 b fun _ => c) :=
    .pi .sort (fun _ _ => .pi .sort (fun _ _ => .pi (.app .const .sort) (fun _ _ => .pi (.app (.app (.app .const .bvar)
      .bvar) .bvar) (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar (fun _ _ => .bvar) (np rfl)) (np rfl)) (np rfl))
      (np rfl)) (np rfl)) (np rfl)
  have dI : D O M.cval ρ (.forallE (.sort 1) (.forallE (.app (.const "Add" [0]) (.bvar 0))
      (.app (.app (.app (.const "HAdd" [0, 0, 0]) (.bvar 1)) (.bvar 1)) (.bvar 1)) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.app (M.cval "Add" [0]) a) fun _ =>
        O.app (O.app (O.app (M.cval "HAdd" [0, 0, 0]) a) a) a) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .app (.app (.app .const .bvar) .bvar) .bvar) (np rfl)) (np rfl)
  have hInst := L.app_mem_piR (L.app_mem_piR (mem_ty M L HA.instHAdd dI) hT (np rfl)) hI (np rfl)
  have hT' : O.mem T (O.app (M.cval "outParam" [2]) (O.univ 1)) := by rw [hOP]; exact hT
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HA.hAddH dTy) hT (np rfl)) hT (np rfl))
    hT' (np rfl)) hInst (np rfl)

/-! ## the add facts at the set level -/

section Alg
variable (Z Sc ADD : S)

omit L in
/-- `Nat.add` from its two recursion theorems, on canonical numerals (typed hypotheses) -/
theorem add_nat (N : S) (nat : Nat → S) (hnz : nat 0 = Z) (hns : ∀ k, nat (k + 1) = O.app Sc (nat k))
    (hmem : ∀ k, O.mem (nat k) N)
    (hz : ∀ x, O.mem x N → O.app (O.app ADD x) Z = x)
    (hs : ∀ x y, O.mem x N → O.mem y N → O.app (O.app ADD x) (O.app Sc y) = O.app Sc (O.app (O.app ADD x) y)) :
    ∀ a b, O.app (O.app ADD (nat a)) (nat b) = nat (a + b) := by
  intro a b
  induction b with
  | zero => rw [hnz, hz _ (hmem a)]; rfl
  | succ b ih => rw [hns, hs _ _ (hmem a) (hmem b), ih, ← hns]; rfl
end Alg

/-- **`Open.bin` for `+`, discharged** -/
theorem add_field (H : EncEnv env) (HL : LitEnv env) (HN : InstN env)
    (hb : HasTy env "br_litN" [] (piN [(tNat, false)] (eqE 1 tNat
      (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0)))
      (.bvar 0)))) (HA : AddEnv env) {ρ : Nat → S} {Hv : S}
    (hH : D O M.cval ρ (trM (apps (.c "HAdd.hAdd" [0, 0, 0]) [U, U, U, apps (.c "instHAdd" [0]) [U, .c "instAddUInt64" []]])) Hv)
    (x y : UInt64) :
    O.app (O.app Hv (encM M (.w x))) (encM M (.w y)) = encM M (.w (x + y)) := by
  -- the head's denotation
  obtain ⟨H3, Iv, hH3, hIv, rfl⟩ := app_inv hH
  obtain ⟨H2, U3, hH2, hU3, rfl⟩ := app_inv hH3
  obtain ⟨H1, U2, hH1, hU2, rfl⟩ := app_inv hH2
  obtain ⟨H0, U1, hH0, hU1, rfl⟩ := app_inv hH1
  obtain ⟨J, Ia, hJ, hIa, rfl⟩ := app_inv hIv
  obtain ⟨J0, U4, hJ0, hU4, rfl⟩ := app_inv hJ
  cases hH0; cases hU1; cases hU2; cases hU3; cases hJ0; cases hU4; cases hIa
  -- sets
  let ρ0 := ρ
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hnat := natEnc_mem' (M := M) (L := L) H ρ
  have dAddN : D O M.cval ρ (.app (.const "Add" [0]) tNat) _ := .app .const .const
  have dAddU : D O M.cval ρ (.app (.const "Add" [0]) tU) _ := .app .const .const
  have hAN := hAdd_mem (M := M) L HA (ρ := ρ) hNu (mem_ty M L HA.addNat dAddN)
  have hAU := hAdd_mem (M := M) L HA (ρ := ρ) hUu (mem_ty M L HA.addU64 dAddU)
  let ADD := O.app (O.app (O.app (O.app (M.cval "HAdd.hAdd" [0, 0, 0]) (M.cval "Nat" [])) (M.cval "Nat" []))
    (M.cval "Nat" [])) (O.app (O.app (M.cval "instHAdd" [0]) (M.cval "Nat" [])) (M.cval "instAddNat" []))
  let ADD64 := O.app (O.app (O.app (O.app (M.cval "HAdd.hAdd" [0, 0, 0]) (M.cval "UInt64" [])) (M.cval "UInt64" []))
    (M.cval "UInt64" [])) (O.app (O.app (M.cval "instHAdd" [0]) (M.cval "UInt64" [])) (M.cval "instAddUInt64" []))
  let OF := M.cval "UInt64.ofNat" []
  have addMem : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) → O.mem (O.app (O.app ADD a) b) (M.cval "Nat" []) :=
    fun a b ha hb => L.app_mem_piR (L.app_mem_piR hAN ha (np rfl)) hb (np rfl)
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app OF a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  have dS : D O M.cval ρ (.forallE tNat tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have sMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "Nat.succ" []) a) (M.cval "Nat" []) :=
    fun a ha => mem_app' L dS (mem_ty M L H.succ dS) .const ha .const
  have hz0 := natEnc_mem' (M := M) (L := L) H ρ 0
  -- the four transfers
  have dAddNE : ∀ ρ', D O M.cval ρ' (hAdd tNat (instH tNat "instAddNat")) ADD := fun _ =>
    .app (.app (.app (.app .const .const) .const) .const) (.app (.app .const .const) .const)
  have dAddUE : ∀ ρ', D O M.cval ρ' (hAdd tU (instH tU "instAddUInt64")) ADD64 := fun _ =>
    .app (.app (.app (.app .const .const) .const) .const) (.app (.app .const .const) .const)
  have hz : ∀ a, O.mem a (M.cval "Nat" []) → O.app (O.app ADD a) (M.cval "Nat.zero" []) = a := by
    intro a ha
    obtain ⟨ty, hc, hty⟩ := HA.add0
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha .nil) .const (.app (.app (dAddNE _) .bvar) .const) .bvar
      hNu (addMem _ _ ha hz0) ha
  have hs : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) →
      O.app (O.app ADD a) (O.app (M.cval "Nat.succ" []) b) = O.app (M.cval "Nat.succ" []) (O.app (O.app ADD a) b) := by
    intro a b ha hb
    obtain ⟨ty, hc, hty⟩ := HA.addS
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha (.cons .const hb .nil)) .const
      (.app (.app (dAddNE _) .bvar) (.app .const .bvar)) (.app .const (.app (.app (dAddNE _) .bvar) .bvar))
      hNu (addMem _ _ ha (sMem _ hb)) (sMem _ (addMem _ _ ha hb))
  have hadd : ∀ a b, O.mem a (M.cval "Nat" []) → O.mem b (M.cval "Nat" []) →
      O.app (O.app ADD64 (O.app OF a)) (O.app OF b) = O.app OF (O.app (O.app ADD a) b) := by
    intro a b ha hb
    obtain ⟨ty, hc, hty⟩ := HA.brAdd
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha (.cons .const hb .nil)) .const
      (.app (.app (dAddUE _) (.app .const .bvar)) (.app .const .bvar)) (.app .const (.app (.app (dAddNE _) .bvar) .bvar))
      hUu (L.app_mem_piR (L.app_mem_piR hAU (ofMem _ ha) (np rfl)) (ofMem _ hb) (np rfl)) (ofMem _ (addMem _ _ ha hb))
  -- the literal 2^64
  have hlit : ∀ ρ', D O M.cval ρ' (litNat UInt64.size) (natEnc M UInt64.size) := by
    intro ρ'
    obtain ⟨R, hR⟩ : ∃ R, D O M.cval ρ' (litNat UInt64.size) R :=
      ⟨_, .app (.app (.app .const .const) (lit_denotes M ρ' _)) (.app .const (lit_denotes M ρ' _))⟩
    have := litN_field (M := M) (ρ := ρ') L H HL HN hb (k := UInt64.size) (R := R) hR
    rwa [this] at hR
  have hwrap : ∀ a, O.mem a (M.cval "Nat" []) →
      O.app OF (O.app (O.app ADD a) (natEnc M UInt64.size)) = O.app OF a := by
    intro a ha
    obtain ⟨ty, hc, hty⟩ := HA.brWrap
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha .nil) .const
      (.app .const (.app (.app (dAddNE _) .bvar) (hlit _))) (.app .const .bvar) hUu
      (ofMem _ (addMem _ _ ha (hnat _))) (ofMem _ ha)
  -- algebra (DenotesSpike.add_u64)
  have hAdd := add_nat (O := O) (M.cval "Nat.zero" []) (M.cval "Nat.succ" []) ADD (M.cval "Nat" []) (natEnc M) rfl
    (fun _ => rfl) hnat hz hs
  show O.app (O.app ADD64 (O.app OF (natEnc M x.toNat))) (O.app OF (natEnc M y.toNat)) = O.app OF (natEnc M (x + y).toNat)
  rw [hadd _ _ (hnat _) (hnat _), hAdd, UInt64.toNat_add, show (2:Nat) ^ 64 = UInt64.size from rfl]
  have hx := x.toNat_lt_size; have hy := y.toNat_lt_size
  generalize UInt64.size = N at hx hy hwrap ⊢
  by_cases h : x.toNat + y.toNat < N
  · rw [Nat.mod_eq_of_lt h]
  · have hk : x.toNat + y.toNat = (x.toNat + y.toNat - N) + N := by omega
    have hm : (x.toNat + y.toNat) % N = x.toNat + y.toNat - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm, hk, ← hAdd, hwrap _ (hnat _), Nat.add_sub_cancel]

/-- **`HeadTy.bin` for `+`, discharged** -/
theorem add_ty (H : EncEnv env) (HA : AddEnv env) {ρ : Nat → S} {Hv X Y : S}
    (hH : D O M.cval ρ (trM (apps (.c "HAdd.hAdd" [0, 0, 0]) [U, U, U, apps (.c "instHAdd" [0]) [U, .c "instAddUInt64" []]])) Hv)
    (hX : O.mem X (tyS M .uw)) (hY : O.mem Y (tyS M .uw)) : O.mem (O.app (O.app Hv X) Y) (tyS M .uw) := by
  obtain ⟨H3, Iv, hH3, hIv, rfl⟩ := app_inv hH
  obtain ⟨H2, U3, hH2, hU3, rfl⟩ := app_inv hH3
  obtain ⟨H1, U2, hH2', hU2, rfl⟩ := app_inv hH2
  obtain ⟨H0, U1, hH0, hU1, rfl⟩ := app_inv hH2'
  obtain ⟨J, Ia, hJ, hIa, rfl⟩ := app_inv hIv
  obtain ⟨J0, U4, hJ0, hU4, rfl⟩ := app_inv hJ
  cases hH0; cases hU1; cases hU2; cases hU3; cases hJ0; cases hU4; cases hIa
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have dAddU : D O M.cval ρ (.app (.const "Add" [0]) tU) _ := .app .const .const
  have hAU := hAdd_mem (M := M) L HA (ρ := ρ) hUu (mem_ty M L HA.addU64 dAddU)
  exact L.app_mem_piR (L.app_mem_piR hAU hX (np rfl)) hY (np rfl)

end Bridge.Add
