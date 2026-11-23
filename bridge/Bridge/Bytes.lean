/- Bridge.Bytes: prelude ops `put` and `rd`, DISCHARGED.  Stored theorems: S2's `bo_put : put o b = List.append o
[b.toUInt8]` (with `List.append`), `bo_u64to8 : ∀ n, (UInt64.ofNat n).toUInt8 = UInt8.ofNat n`, `bo_wrap8 : ∀ n,
UInt8.ofNat (n + 256) = UInt8.ofNat n`; for `rd`: `bo_rd : rd x i = (List.getD x i.toNat (0 : UInt8)).toUInt64`,
`br_lit8 : ∀ n, @OfNat.ofNat UInt8 n (UInt8.instOfNat n) = UInt8.ofNat n`, and the guarded
`u8to64 : ∀ n, Nat.blt n 256 = true → (UInt8.ofNat n).toUInt64 = UInt64.ofNat n`.

STATUS: proved, no sorry. -/
import Bridge.Index

namespace Bridge.Bytes
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Asm Bridge.Add Bridge.Final
  Bridge.Call Bridge.Len Bridge.Push Bridge.Cmp Bridge.Final4 Bridge.Index Bridge.Iota2

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def of8 (a : E) : E := .app (.const "UInt8.ofNat" []) a
def lit8 (k : Nat) : E := .app (.app (.app (.const "OfNat.ofNat" [0]) tU8) (.lit k)) (.app (.const "UInt8.instOfNat" []) (.lit k))

structure ByteEnv (env : List Const) : Prop where
  to8H : HasTy env "UInt64.toUInt8" [] (.forallE tU tU8 false)
  to64H : HasTy env "UInt8.toUInt64" [] (.forallE tU8 tU false)
  inst8 : HasTy env "UInt8.instOfNat" [] (.forallE tNat (.app (.app (.const "OfNat" [0]) tU8) (.bvar 0)) false)
  boPut : HasTy env "bo_put" [] (piN [(tList tU8, true), (tU, true)]
    (eqE 1 (tList tU8) (.app (.app (.const "put" []) (.bvar 1)) (.bvar 0))
      (appE tU8 (.bvar 1) (consE tU8 (.app (.const "UInt64.toUInt8" []) (.bvar 0)) (nilE tU8)))))
  u64to8 : HasTy env "bo_u64to8" [] (piN [(tNat, true)] (eqE 1 tU8 (.app (.const "UInt64.toUInt8" []) (ofN (.bvar 0)))
    (of8 (.bvar 0))))
  wrap8 : HasTy env "bo_wrap8" [] (piN [(tNat, true)] (eqE 1 tU8 (of8 (addN (.bvar 0) (litNat 256))) (of8 (.bvar 0))))
  boRd : HasTy env "bo_rd" [] (piN [(tList tU8, true), (tU, true)]
    (eqE 1 tU (.app (.app (.const "rd" []) (.bvar 1)) (.bvar 0))
      (.app (.const "UInt8.toUInt64" []) (getDE tU8 (.bvar 1) (toNatE (.bvar 0)) (lit8 0)))))
  brLit8 : HasTy env "br_lit8" [] (piN [(tNat, true)] (eqE 1 tU8
    (.app (.app (.app (.const "OfNat.ofNat" [0]) tU8) (.bvar 0)) (.app (.const "UInt8.instOfNat" []) (.bvar 0)))
    (of8 (.bvar 0))))
  u8to64 : HasTy env "u8to64" [] (piN [(tNat, true), (eqE 1 tB (bin2 "Nat.blt" (.bvar 0) (litNat 256)) tt, true)]
    (eqE 1 tU (.app (.const "UInt8.toUInt64" []) (of8 (.bvar 1))) (ofN (.bvar 1))))

variable (L : SetLaws O)
include L

/-- a Nat literal denotes its numeral -/
theorem litNat_D (E : Env env sig P) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S) (k : Nat) :
    D O M.cval ρ (litNat k) (natEnc M k) := by
  obtain ⟨R, hR⟩ : ∃ R, D O M.cval ρ (litNat k) R :=
    ⟨_, .app (.app (.app .const .const) (lit_denotes M ρ _)) (.app .const (lit_denotes M ρ _))⟩
  have := litN_field (M := M) (ρ := ρ) L E.enc E.lit E.instN hbl (k := k) (R := R) hR
  rwa [this] at hR

theorem of8_mem (H : EncEnv env) {ρ : Nat → S} {a : S} (ha : O.mem a (M.cval "Nat" [])) :
    O.mem (O.app (M.cval "UInt8.ofNat" []) a) (M.cval "UInt8" []) := by
  have dP : D O M.cval ρ (.forallE tNat (.const "UInt8" []) false) _ := .pi .const (fun _ _ => .const) (np rfl)
  exact mem_app' L dP (mem_ty M L H.ofNat8 dP) .const ha .const

/-- the 8-bit wrap on canonical numerals -/
theorem wrap8_mod (E : Env4 env sig P) (HB : ByteEnv env) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S) :
    ∀ k, O.app (M.cval "UInt8.ofNat" []) (natEnc M k) = O.app (M.cval "UInt8.ofNat" []) (natEnc M (k % 256)) := by
  have H := E.enc
  have HA := E.add
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hU8u := univ1 (M := M) (L := L) H H.u8 ρ
  have hnat := natEnc_mem' (M := M) (L := L) H ρ
  have dAddN : D O M.cval ρ (.app (.const "Add" [0]) tNat) _ := .app .const .const
  have hAN := hAdd_mem (M := M) L HA (ρ := ρ) hNu (mem_ty M L HA.addNat dAddN)
  let ADD := O.app (O.app (O.app (O.app (M.cval "HAdd.hAdd" [0, 0, 0]) (M.cval "Nat" [])) (M.cval "Nat" []))
    (M.cval "Nat" [])) (O.app (O.app (M.cval "instHAdd" [0]) (M.cval "Nat" [])) (M.cval "instAddNat" []))
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
  have hwrap : ∀ a, O.mem a (M.cval "Nat" []) →
      O.app (M.cval "UInt8.ofNat" []) (O.app (O.app ADD a) (natEnc M 256)) = O.app (M.cval "UInt8.ofNat" []) a := by
    intro a ha
    obtain ⟨ty, hc, hty⟩ := HB.wrap8
    exact transferN L M hc (ls := []) hty ρ (.cons .const ha .nil) .const
      (.app .const (.app (.app (dAddNE _) .bvar) (litNat_D L E.toEnv hbl _ 256))) (.app .const .bvar) hU8u
      (of8_mem L H (ρ := ρ) (addMem _ _ ha (hnat _))) (of8_mem L H (ρ := ρ) ha)
  have hAdd := add_nat (O := O) (M.cval "Nat.zero" []) (M.cval "Nat.succ" []) ADD (M.cval "Nat" []) (natEnc M) rfl
    (fun _ => rfl) hnat hz hs
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases h : k < 256
    · rw [Nat.mod_eq_of_lt h]
    · have hk : k = (k - 256) + 256 := by omega
      have := ih (k - 256) (by omega)
      rw [hk, ← hAdd, hwrap _ (hnat _), this, Nat.add_mod_right]

/-- **`put`** -/
theorem put_field (E : Env4 env sig P) (HB : ByteEnv env) (hbl : HasTy env "br_litN" [] brLitNTy) (ρ : Nat → S)
    (o : List UInt8) (v : UInt64) :
    O.app (O.app (M.cval "put" []) (encM M (.l o))) (encM M (.w v)) = encM M (.l (o ++ [v.toUInt8])) := by
  have H := E.enc
  have hU8u := univ1 (M := M) (L := L) H H.u8 ρ
  have hLu := list_univ (M := M) L H (ρ := ρ) hU8u
  let f : UInt8 → S := fun b => O.app (M.cval "UInt8.ofNat" []) (natEnc M b.toNat)
  have hf : ∀ b : UInt8, O.mem (f b) (M.cval "UInt8" []) := fun b => of8_mem L H (ρ := ρ) (natEnc_mem' (M := M) (L := L) H ρ _)
  have hl := listEnc_mem (M := M) (L := L) H ρ hU8u f hf
  have hv := (encM_mem (M := M) (L := L) H ρ (.w v)).1
  have d8 : D O M.cval ρ (.forallE tU tU8 false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have h8 : O.mem (O.app (M.cval "UInt64.toUInt8" []) (encM M (.w v))) (M.cval "UInt8" []) :=
    mem_app' L d8 (mem_ty M L HB.to8H d8) .const hv .const
  have hty2 := app_piS L .ls (mem_ty M L (E.primTy (p := 4) rfl (by decide) (by decide) (by decide)) (ρ := ρ)
    (piPs_D .ls _)) (.cons (hl o) (.cons hv .nil))
  obtain ⟨ty, hc, hty⟩ := HB.boPut
  have key := transferN L M hc (ls := []) hty ρ (.cons (.app .const .const) (hl o) (.cons .const hv .nil))
    (.app .const .const) (.app (.app .const .bvar) .bvar)
    (.app (.app (.app .const .const) .bvar) (.app (.app (.app .const .const) (.app .const .bvar)) (.app .const .const))) hLu
    hty2 (app_mem L E.push (ρ := ρ) hU8u (hl o) (cons_mem L H (ρ := ρ) hU8u h8 (hl [])))
  simp only [push] at key
  -- the byte: `toUInt8 (ofNat k) = UInt8.ofNat k`, then the 8-bit wrap
  have hb8 : O.app (M.cval "UInt64.toUInt8" []) (encM M (.w v)) = f v.toUInt8 := by
    obtain ⟨ty, hc, hty⟩ := HB.u64to8
    have hn := natEnc_mem' (M := M) (L := L) H ρ v.toNat
    have k8 : O.app (M.cval "UInt64.toUInt8" []) (O.app (M.cval "UInt64.ofNat" []) (natEnc M v.toNat)) =
        O.app (M.cval "UInt8.ofNat" []) (natEnc M v.toNat) :=
      transferN L M hc (ls := []) hty ρ (.cons .const hn .nil) .const (.app .const (.app .const .bvar)) (.app .const .bvar)
        hU8u h8 (of8_mem L H (ρ := ρ) hn)
    rw [show encM M (.w v) = O.app (M.cval "UInt64.ofNat" []) (natEnc M v.toNat) from rfl, k8, wrap8_mod L E HB hbl ρ]
    show _ = O.app _ (natEnc M (v.toUInt8).toNat)
    congr 2
  show O.app (O.app (M.cval "put" []) (listEnc M _ f o)) (encM M (.w v)) = listEnc M _ f (o ++ [v.toUInt8])
  rw [key, hb8, ← append_set L H E.push ρ hU8u f hf o [v.toUInt8]]; rfl

/-- **`rd`** -/
theorem rd_field (E : Env4 env sig P) (HI : IdxEnv env) (HB : ByteEnv env) (hbl : HasTy env "br_litN" [] brLitNTy)
    (ρ : Nat → S) (x : List UInt8) (i : UInt64) :
    O.app (O.app (M.cval "rd" []) (encM M (.l x))) (encM M (.w i)) = encM M (.w (x.getD i.toNat 0).toUInt64) := by
  have H := E.enc
  have hU8u := univ1 (M := M) (L := L) H H.u8 ρ
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hBu := univ1 (M := M) (L := L) H E.cmp.bool ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  let f : UInt8 → S := fun b => O.app (M.cval "UInt8.ofNat" []) (natEnc M b.toNat)
  have hf : ∀ b : UInt8, O.mem (f b) (M.cval "UInt8" []) := fun b => of8_mem L H (ρ := ρ) (hn _)
  have hl := listEnc_mem (M := M) (L := L) H ρ hU8u f hf
  have hi := (encM_mem (M := M) (L := L) H ρ (.w i)).1
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "UInt64.ofNat" []) a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  -- the default `(0 : UInt8)`
  have dI8 : D O M.cval ρ (.forallE tNat (.app (.app (.const "OfNat" [0]) tU8) (.bvar 0)) false) _ :=
    .pi .const (fun _ _ => .app (.app .const .const) .bvar) (np rfl)
  have hlit8 : ∀ ρ', D O M.cval ρ' (lit8 0) (f 0) := by
    intro ρ'
    have hI0 := mem_app' L dI8 (mem_ty M L HB.inst8 dI8) .const (hn 0) (.app (.app .const .const) .bvar)
    obtain ⟨ty, hc, hty⟩ := HB.brLit8
    have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn 0) .nil) .const
      (.app (.app (.app .const .const) .bvar) (.app .const .bvar)) (.app .const .bvar) hU8u
      (ofNat_mem (ρ := ρ) L E.lit hU8u (hn 0) hI0) (hf 0)
    simp only [push] at key
    have hD := (D.app (D.app (D.app .const .const) (lit_denotes M ρ' 0)) (D.app .const (lit_denotes M ρ' 0)) :
      D O M.cval ρ' (lit8 0) _)
    rw [key] at hD; exact hD
  have dTN : D O M.cval ρ (.forallE tU tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hK : O.mem (O.app (M.cval "UInt64.toNat" []) (encM M (.w i))) (M.cval "Nat" []) :=
    mem_app' L dTN (mem_ty M L HI.toNatH dTN) .const hi .const
  have d64 : D O M.cval ρ (.forallE tU8 tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have hty2 := app_piS L .uw (mem_ty M L (E.primTy (p := 2) rfl (by decide) (by decide) (by decide)) (ρ := ρ)
    (piPs_D .uw _)) (.cons (hl x) (.cons hi .nil))
  obtain ⟨ty, hc, hty⟩ := HB.boRd
  have key := transferN L M hc (ls := []) hty ρ (.cons (.app .const .const) (hl x) (.cons .const hi .nil)) .const
    (.app (.app .const .bvar) .bvar)
    (.app .const (.app (.app (.app (.app .const .const) .bvar) (.app .const .bvar)) (hlit8 _))) hUu hty2
    (mem_app' L d64 (mem_ty M L HB.to64H d64) .const (getD_mem L HI (ρ := ρ) hU8u (hl x) hK (hf 0)) .const)
  simp only [push] at key
  show O.app (O.app (M.cval "rd" []) (listEnc M _ f x)) (encM M (.w i)) = _
  rw [key, show encM M (.w i) = O.app (M.cval "UInt64.ofNat" []) (natEnc M i.toNat) from rfl, toNat_set L H E.lit E.instN E.cmp HI hbl ρ i.toNat_lt_size, getD_set L H HI ρ hU8u f hf (hf 0) x i.toNat]
  -- `(UInt8.ofNat k).toUInt64 = UInt64.ofNat k` for the byte `k < 256`
  have h64 : ∀ b : UInt8, O.app (M.cval "UInt8.toUInt64" []) (f b) = O.app (M.cval "UInt64.ofNat" []) (natEnc M b.toNat) := by
    intro b
    have hb := b.toNat_lt
    have hblt := blt_set (M := M) L H E.cmp ρ b.toNat 256
    rw [show decide (b.toNat < 256) = true by simpa using hb] at hblt
    have hbltm : O.mem (O.app (O.app (M.cval "Nat.blt" []) (natEnc M b.toNat)) (natEnc M 256)) (M.cval "Bool" []) := by
      rw [hblt]; exact bool_mem L E.cmp ρ true
    have hg : O.mem O.pt (O.app (O.app (O.app (M.cval "Eq" [1]) (M.cval "Bool" []))
        (O.app (O.app (M.cval "Nat.blt" []) (natEnc M b.toNat)) (natEnc M 256))) (M.cval "Bool.true" [])) := by
      rw [M.eq_equality 1 ρ _ _ _ _ .const hBu hbltm (mem_ty M L E.cmp.btrue (ρ := ρ) .const)]
      exact L.pt_mem_eqv (by rw [hblt]; rfl)
    obtain ⟨ty, hc, hty⟩ := HB.u8to64
    have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn b.toNat)
      (.cons (.app (.app (.app .const .const) (.app (.app .const .bvar) (litNat_D L E.toEnv hbl _ 256))) .const) hg .nil))
      .const (.app .const (.app .const .bvar)) (.app .const .bvar) hUu
      (mem_app' L d64 (mem_ty M L HB.to64H d64) .const (hf b) .const) (ofMem _ (hn _))
    simpa [push] using key
  rw [List.getD_eq_getElem?_getD]
  cases hx : x[i.toNat]? with
  | none => simp only [Option.getD_none]; rw [h64]; rfl
  | some b => simp only [Option.getD_some]; rw [h64]; rfl

end Bridge.Bytes
